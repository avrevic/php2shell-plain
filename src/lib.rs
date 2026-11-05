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

/// The request heap: PHP's per-request `emalloc` arena (`Zend/zend_alloc.c`).
/// The next request reuses the same memory, which is what turns a stale pointer into a leak.
/// Unlike `php2shell-chase`, there is no generation: nothing records which request a byte
/// belongs to, just as in C.
pub struct RequestHeap {
    pub bytes: Vec<u8>,
}

/// `zend_string *` stored in `PS(id)`.
#[derive(Clone, Copy)]
/// The value of `PS(id)`: in PHP a `zend_string *`, here an offset and a length into the
/// request heap. Safe Rust cannot keep a reference past its heap, so an index stands in for
/// the pointer. The logic error survives that change.
pub struct SessionId {
    pub off: usize,
    pub len: usize,
}

/// One PHP worker process. It serves many requests in turn and its globals outlive all of them.
/// `ps_id` stands for `PS(id)`, the session module's current session id.
pub struct Worker {
    pub ps_id: Option<SessionId>,
}

impl RequestHeap {
    /// A fresh, empty request heap. Spec: it is empty. Verified.
    pub fn new() -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new() }
    }

    /// End of a request (`shutdown_memory_manager` in PHP): every allocation dies.
    /// Spec: the heap is empty afterwards. Verified. Note what this spec does not say: nothing
    /// about who may still hold an offset into the old heap.
    pub fn destroy(self) -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new() }
    }

    /// An `emalloc` in the next request. In the attack, the attacker's request body lands in the
    /// freed slot. Spec: one byte appended. Verified.
    pub fn alloc(self, b: u8) -> (heap: RequestHeap)
        ensures heap.bytes@ == self.bytes@.push(b),
    {
        let mut heap = self;
        heap.bytes.push(b);
        heap
    }
}

/// PHP: the session upload-progress handler (`ext/session/session.c`, RFC 1867 callback) on
/// `MULTIPART_EVENT_FILE_START`. It allocates the session id on the request heap and stores
/// it in `PS(id)`. Spec: the byte is appended and `ps_id` points at it. Verified.
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

/// PHP: `php_rshutdown_session_globals`, which clears `PS(id)`. This is the call the bug
/// skips. Spec: `ps_id` is `None`. Verified.
pub fn rshutdown_session_globals(worker: Worker) -> (out: Worker)
    ensures out.ps_id is None,
{
    let mut worker = worker;
    worker.ps_id = None;
    worker
}

/// PHP: `MULTIPART_EVENT_END`, the normal end: clear `PS(id)`, then free the heap.
/// Spec: the heap is freed. Verified.
pub fn request_end_normal(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// THE BUG (CVE-2026-109618), unchanged from `php2shell-chase`: out of memory,
/// `zend_bailout` skips `php_rshutdown_session_globals`, the heap is freed anyway, and
/// `PS(id)` dangles.
///
/// Verus: VERIFIED. Its spec, "the request heap is gone", is true. No spec here relates the
/// worker global to the heap, so there is nothing for this edge to violate. This is the
/// finding of this repo: a careful per-function spec proves the vulnerable code clean.
pub fn request_end_fatal_oom(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    (worker, heap.destroy())
}

/// The same edge with the fix (clear the globals before freeing). Verified too, with the same
/// spec. Verus cannot tell the bug and the fix apart here.
pub fn request_end_fatal_oom_fixed(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    ensures out.1.bytes.len() == 0,
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// PHP: the next request's upload-progress cleanup trusts `PS(id)`'s pointer and length and
/// copies the bytes into the `PHPSESSID` cookie. This is a literal port: no bounds check.
///
/// Verus: FAILED, the slice bounds precondition and a possible `off + len` overflow. This is
/// the only failure in the crate, and it is a symptom, not the cause. It fails whether or not
/// the previous request took the bug, and it points at the read in the next request, not at
/// the out-of-memory edge where the cleanup was skipped.
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

/// The same read as a careful Rust port writes it: check the bounds, else return nothing.
/// Verus: VERIFIED. Memory safety holds. The test
/// `fatal_oom_leaks_reclaimed_bytes_into_the_cookie` shows this version still copying another
/// request's bytes into the cookie: the read is in bounds, it is just the wrong request's
/// memory. Fixing the symptom silences the verifier and keeps the leak.
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

    /// The disclosure as a test: request 1 dies of OOM after publishing 'S', request 2 (the
    /// attacker's) allocates 'X' in the same slot, and request 2's cookie is "X". Passes.
    /// A test only shows this because someone thought to write this exact sequence.
    #[test]
    fn fatal_oom_leaks_reclaimed_bytes_into_the_cookie() {
        let (worker, heap) = request_end_fatal_oom(Worker { ps_id: None }, RequestHeap::new(), b'S');
        let heap = heap.alloc(b'X'); // next request: someone else's secret now lives in that slot
        assert_eq!(upload_progress_cleanup_checked(&worker, &heap), b"X");
    }

    /// The same sequence after the fixed edge: the cookie is empty. Passes.
    #[test]
    fn fixed_edge_leaks_nothing() {
        let (worker, heap) = request_end_fatal_oom_fixed(Worker { ps_id: None }, RequestHeap::new(), b'S');
        let heap = heap.alloc(b'X');
        assert_eq!(upload_progress_cleanup_checked(&worker, &heap), b"");
    }
}
