//! Canonical deterministic MAC verification, extracted to anchor Demo 4.
//!
//! The MAC is `tag(k, m) = PRF_k(m)` and `verify(k, m, t) = (PRF_k(m) == t)`. The PRF
//! (HMAC-SHA256 in libsignal) is modeled abstractly on the Lean side; THIS code is the
//! tag-comparison glue the receiver runs: a constant-length, all-bytes equality check
//! (where truncation / early-exit / length bugs would live — constant-time behaviour is a
//! side-channel concern, out of scope here). No unsafe / FFI / traits; in the Aeneas fragment.

/// MAC tag length in bytes (HMAC-SHA256 output / libsignal `MAC_SIZE`).
pub const TAG_LEN: usize = 32;

/// Verify a MAC tag: accept iff the recomputed PRF output equals the received tag, checked
/// over all 32 bytes. `prf_out` is `PRF_k(m)`, supplied by the (abstract) PRF.
pub fn verify(prf_out: [u8; 32], recv_tag: [u8; 32]) -> bool {
    let mut i = 0;
    let mut ok = true;
    while i < 32 {
        if prf_out[i] != recv_tag[i] {
            ok = false;
        }
        i += 1;
    }
    ok
}
