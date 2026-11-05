# php2shell-plain

The smallest Rust model of one PHP2Shell bug, verified with [Verus](https://github.com/verus-lang/verus). This version **does not chase the bug**. It is the same code as [php2shell-chase](https://github.com/avrevic/php2shell-chase). Each function has the spec a careful port would give it, which says what that one function does. No spec says anything that spans two requests.

## Result

| Function | PHP | Verus |
|---|---|---|
| `publish_session_id` | `MULTIPART_EVENT_FILE_START` | verified |
| `request_end_normal` | `MULTIPART_EVENT_END` | verified |
| `request_end_fatal_oom` | OOM, `zend_bailout` (**the bug**) | **verified** |
| `request_end_fatal_oom_fixed` | OOM with the fix | verified |
| `upload_progress_cleanup` | next request, reads `PS(id)` as C does | failed: index may be out of bounds, `off + len` may overflow |
| `upload_progress_cleanup_checked` | next request, bounds-checked first | verified, and it still leaks |

```
error: precondition not satisfied        (slice_subrange: 0 <= i <= j <= len)
error: possible arithmetic underflow/overflow
verification results:: 10 verified, 1 errors
```

- The buggy edge verifies. Its own spec, "the request heap is gone", is true.
- The one failure is in the next request, and it fails whether or not the previous request took the bug. It says "this read might be out of bounds", which is the symptom, not the cause, and it does not point at the fatal edge.
- A Rust port that checks bounds before the read verifies cleanly. `cargo test` shows that port still copying another request's bytes into the cookie (`fatal_oom_leaks_reclaimed_bytes_into_the_cookie`). Memory safety holds, and the disclosure is still there.

**Without a property that spans requests, verification does not find the flaw.**

## The PHP feature being modelled

[PHP2Shell](https://www.wiz.io/blog/php2shell-php-rce), CVE-2026-109618, "remote process-memory disclosure". This is the session upload-progress path and nothing else:

1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, PHP allocates the session id on the request heap and publishes it in the worker global `PS(id)`.
2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the request heap is destroyed.
3. Fatal out-of-memory: `zend_bailout` (a `longjmp`) skips that clear. The heap is destroyed anyway, and `PS(id)` keeps pointing into it.
4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)` (pointer + length) and copies those bytes into the `PHPSESSID` cookie.

`Worker.ps_id` is `PS(id)`. `RequestHeap` is the `emalloc` arena. The C pointer is an offset and a length into it.

## Run it

```sh
probe-verus setup            # installs Verus and its Rust toolchain
cargo verus verify           # Verus
probe-verus extract --with-spec-text .   # VeriLib probe output in .verilib/probes/
cargo test                   # the leak, as a test
```
