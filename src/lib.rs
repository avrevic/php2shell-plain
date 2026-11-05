//! PHP2Shell, session upload-progress (CVE-2026-109618), smallest Rust model, verified with Verus.
//!
//! This crate does NOT chase the bug. It is the same feature as `php2shell-chase`, ported
//! line for line from PHP, with no property written about the bug. Each function gets the spec
//! a careful port would give it: what that one function does. No spec says anything that spans
//! two requests. Verus also checks what it checks for any Rust code: no overflow, no
//! out-of-bounds index, no panic.
//!
//! The PHP feature, and only it:
//! 1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, the
//!    session id is allocated on the request heap and published in the worker global `PS(id)`.
//! 2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the heap is destroyed.
//! 3. Fatal out-of-memory: `zend_bailout` (a longjmp) skips step 2's clear; the heap is destroyed
//!    anyway, and `PS(id)` keeps pointing into it.
//! 4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)`
//!    (pointer + length) and copies those bytes into the `PHPSESSID` cookie.

use vstd::prelude::*;

verus! {

/// The request heap (`emalloc` arena). `destroy` is the end of a request; the next request
/// reuses the same memory.
pub struct RequestHeap {
    pub bytes: Vec<u8>,
}

/// `zend_string *` stored in `PS(id)`.
#[derive(Clone, Copy)]
pub struct SessionId {
    pub off: usize,
    pub len: usize,
}

/// Process-lifetime globals of one PHP worker. `ps_id` is `PS(id)`.
pub struct Worker {
    pub ps_id: Option<SessionId>,
}

impl RequestHeap {
    pub fn new() -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new() }
    }

    /// End of a request: every allocation dies.
    pub fn destroy(self) -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new() }
    }

    /// `emalloc` in the next request: the attacker's request body reclaims the memory.
    pub fn alloc(self, b: u8) -> (heap: RequestHeap)
        ensures heap.bytes@ == self.bytes@.push(b),
    {
        let mut heap = self;
        heap.bytes.push(b);
        heap
    }
}

/// `MULTIPART_EVENT_FILE_START`: allocate the id on the request heap and publish it in `PS(id)`.
pub fn publish_session_id(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures
        out.1.bytes@ == heap.bytes@.push(sid),
        out.0.ps_id == Some(SessionId { off: heap.bytes.len() as usize, len: 1 }),
{
    let mut heap = heap;
    let mut worker = worker;
    let off = heap.bytes.len();
    heap.bytes.push(sid);
    worker.ps_id = Some(SessionId { off, len: 1 });
    (worker, heap)
}

/// `php_rshutdown_session_globals`.
pub fn rshutdown_session_globals(worker: Worker) -> (out: Worker)
    ensures out.ps_id is None,
{
    let mut worker = worker;
    worker.ps_id = None;
    worker
}

/// `MULTIPART_EVENT_END`: clear the globals, then the heap dies.
pub fn request_end_normal(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// THE BUG, unchanged: `zend_bailout` skips `php_rshutdown_session_globals`. Its own spec
/// (the request heap is gone) holds, so Verus verifies it.
pub fn request_end_fatal_oom(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    (worker, heap.destroy())
}

/// The same fatal edge with the fix. Verus verifies it too: with no spec across requests it
/// cannot tell the two apart.
pub fn request_end_fatal_oom_fixed(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// The next request, as PHP does it: trust `PS(id)`'s pointer and length.
/// Verus reports a possible out-of-bounds read here, in the next request, whether or not the
/// previous request ended through the bug, so the report does not point at the fatal edge.
pub fn upload_progress_cleanup<'a>(worker: &Worker, heap: &'a RequestHeap) -> (cookie: &'a [u8])
    ensures
        worker.ps_id is Some ==> cookie@.len() == worker.ps_id->Some_0.len,
        worker.ps_id is None ==> cookie@.len() == 0,
{
    match worker.ps_id {
        Some(id) => vstd::slice::slice_subrange(heap.bytes.as_slice(), id.off, id.off + id.len),
        None => &[],
    }
}

/// The next request, as a careful Rust port does it: check the bounds first. Verus verifies
/// it, and it still copies another request's bytes into the cookie (see the test).
pub fn upload_progress_cleanup_checked<'a>(worker: &Worker, heap: &'a RequestHeap) -> (cookie: &'a [u8])
    ensures cookie@.len() <= heap.bytes@.len(),
{
    match worker.ps_id {
        Some(id) => {
            if id.off <= heap.bytes.len() && id.len <= heap.bytes.len() - id.off {
                vstd::slice::slice_subrange(heap.bytes.as_slice(), id.off, id.off + id.len)
            } else {
                &[]
            }
        },
        None => &[],
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// The disclosure: request 1 dies of OOM, request 2 is the attacker's, and the cookie of
    /// request 2 is made from whatever now sits where request 1's session id was.
    #[test]
    fn fatal_oom_leaks_reclaimed_bytes_into_the_cookie() {
        let (worker, heap) = request_end_fatal_oom(Worker { ps_id: None }, RequestHeap::new(), b'S');
        let heap = heap.alloc(b'X'); // next request: someone else's secret now lives in that slot
        assert_eq!(upload_progress_cleanup_checked(&worker, &heap), b"X");
    }

    #[test]
    fn fixed_edge_leaks_nothing() {
        let (worker, heap) = request_end_fatal_oom_fixed(Worker { ps_id: None }, RequestHeap::new(), b'S');
        let heap = heap.alloc(b'X');
        assert_eq!(upload_progress_cleanup_checked(&worker, &heap), b"");
    }
}
