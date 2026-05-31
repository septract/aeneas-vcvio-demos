//! SPQR Ratcheted Authenticator glue — domain-separation string assembly, the
//! `root_key`/`mac_key` update split, and the constant-time MAC comparison, as
//! in SPQR's `src/authenticator.rs` and `src/util.rs`
//! (signalapp/SparsePostQuantumRatchet, HEAD `f2589fe`).
//!
//! Faithful, Aeneas-extractable analog of the authenticator's *non-cryptographic*
//! core. The MAC and KDF themselves (`libcrux_hmac::hmac`, `hkdf::Hkdf::<Sha256>`)
//! are external crates outside the Aeneas fragment, so here their outputs are
//! modelled as `[u8; …]` inputs and we lift only the byte plumbing. (In the
//! game-based proof these are either the raw hardness floor — assumed — or
//! reductions proved separately; their `#[hax_lib::opaque]` marking in SPQR is
//! unrelated — that supports Signal's panic-freedom proofs, not cryptographic
//! correctness.) That plumbing is where the interesting divergences from
//! the ML-KEM-Braid spec prose live (e.g. the spec says HKDF salt = `root_key`,
//! IKM = `update_key`, but the code feeds salt = `[0; 32]`, IKM = `root_key ‖ k`):
//! the extracted node targets the *code's* actual schedule, not the prose.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits,
//! no `Vec`; fixed-size arrays and `while` loops in place of `[…].concat()`.
//!
//! ## Correspondence & coverage
//!
//! Upstream: signalapp/SparsePostQuantumRatchet @`f2589fe` — `src/authenticator.rs`,
//! `src/util.rs`, `src/kdf.rs`. Per-site divergences are tagged `XREF:` below.
//!
//! NOT modeled (out of the Aeneas fragment or deferred):
//!   - the HMAC/HKDF themselves (`libcrux_hmac::hmac`, `hkdf::Hkdf::<Sha256>` — external
//!     crates outside the fragment); modeled here as byte inputs. (HMAC/HKDF are
//!     constructions *above* the hardness floor: see `crypto/sha256.rs`, where HMAC is
//!     extracted and reduced to SHA's compression PRF, rather than left opaque.)
//!   - the `Authenticator` struct + its `new`/`update`/`mac_*`/`verify_*` methods as
//!     stateful methods (we extract the pure byte-builders they call);
//!   - `core::hint::black_box` around `is_non_zero` (a non-functional optimizer barrier).

/// MAC output size (`Authenticator::MACSIZE`); HMAC-SHA256 truncated to 32 bytes.
pub const MACSIZE: usize = 32;

// Domain-separation labels (`authenticator.rs`). The array lengths below are
// checked by the compiler against the literals, so they double as a spec for the
// "Signal_PQCKA_V1_MLKEM768" protocol-info prefix and its three suffixes.
const UPDATE_LABEL: [u8; 45] = *b"Signal_PQCKA_V1_MLKEM768:Authenticator Update";
const CT_LABEL: [u8; 35] = *b"Signal_PQCKA_V1_MLKEM768:ciphertext";
const HDR_LABEL: [u8; 33] = *b"Signal_PQCKA_V1_MLKEM768:ekheader";

// ML-KEM-768 message sizes used by the authenticator (incremental_mlkem768.rs).
const HEADER_SIZE: usize = 64;
// The ciphertext the authenticator actually MACs is the concatenation `ct1 ‖ ct2`
// (CIPHERTEXT1_SIZE 960 + CIPHERTEXT2_SIZE 128); see `send_ct.rs`:
// `ct1.extend_from_slice(&ct2); auth.mac_ct(epoch, &ct1)`.
const CIPHERTEXT_SIZE: usize = 1088;

/// `ToBytes(epoch)` — big-endian encoding of a 64-bit epoch. Mirrors
/// `ep.to_be_bytes()` (the spec recommends big-endian for `EPOCH_TYPE = u64`).
///
/// XREF: spqr authenticator.rs:48,:69,:94 @f2589fe (`ep.to_be_bytes()`) [type-only — exact].
pub fn epoch_to_be_bytes(ep: u64) -> [u8; 8] {
    let mut out = [0u8; 8];
    let mut i = 0;
    while i < 8 {
        out[i] = (ep >> (56 - 8 * i)) as u8;
        i += 1;
    }
    out
}

/// HKDF `info` for the authenticator update:
/// `"Signal_PQCKA_V1_MLKEM768:Authenticator Update" ‖ ToBytes(epoch)`.
/// Mirrors the `info` built in `Authenticator::update`.
///
/// XREF: spqr authenticator.rs:46-50 @f2589fe (the `info = [LABEL, ep.to_be_bytes()].concat()`)
/// [type-only — exact; `concat()` → fixed `[u8;53]`].
pub fn auth_update_info(ep: u64) -> [u8; 53] {
    let eb = epoch_to_be_bytes(ep);
    let mut out = [0u8; 53];
    let mut i = 0;
    while i < 45 {
        out[i] = UPDATE_LABEL[i];
        i += 1;
    }
    let mut j = 0;
    while j < 8 {
        out[45 + j] = eb[j];
        j += 1;
    }
    out
}

/// HKDF input keying material for the authenticator update: `root_key ‖ k`.
/// Mirrors `let ikm = [self.root_key.as_slice(), k].concat();` — note this is the
/// `root_key` (not the spec's `update_key`) in the IKM position, the documented
/// salt/IKM swap relative to the ML-KEM-Braid prose.
///
/// XREF: spqr authenticator.rs:45 @f2589fe (`ikm = [self.root_key.as_slice(), k].concat()`;
/// HKDF `salt = [0u8;32]` at :51, not the spec's `root_key`) [type-only — exact to the *code*;
/// `concat()` → fixed `[u8;64]`. NB the *code* diverges from the ML-KEM-Braid spec prose here
/// (salt/IKM swap); the mirror faithfully follows the code, which is the proof target].
pub fn auth_update_ikm(root_key: [u8; 32], k: [u8; 32]) -> [u8; 64] {
    let mut out = [0u8; 64];
    let mut i = 0;
    while i < 32 {
        out[i] = root_key[i];
        out[32 + i] = k[i];
        i += 1;
    }
    out
}

/// Split the 64-byte `KDF_AUTH` output into the new `(root_key, mac_key)`.
/// Mirrors `self.root_key = kdf_out[..32]; self.mac_key = kdf_out[32..];`.
///
/// XREF: spqr authenticator.rs:52-53 @f2589fe [type-only — exact; `to_vec()` slices → fixed `[u8;32]`].
pub fn update_split(kdf_out: [u8; 64]) -> ([u8; 32], [u8; 32]) {
    let mut root_key = [0u8; 32];
    let mut mac_key = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        root_key[i] = kdf_out[i];
        mac_key[i] = kdf_out[32 + i];
        i += 1;
    }
    (root_key, mac_key)
}

/// MAC input for a header message:
/// `"Signal_PQCKA_V1_MLKEM768:ekheader" ‖ ToBytes(epoch) ‖ hdr`.
/// Mirrors the `ct_mac_data` built in `Authenticator::mac_hdr` (header is the
/// fixed 64-byte ML-KEM-768 `pk1`/header).
///
/// XREF: spqr authenticator.rs:92-97 @f2589fe (`Authenticator::mac_hdr`) [type-only — exact; `concat()`
/// → fixed `[u8;105]`; HMAC over this data is opaque].
pub fn mac_hdr_data(ep: u64, hdr: [u8; 64]) -> [u8; 105] {
    let eb = epoch_to_be_bytes(ep);
    let mut out = [0u8; 105];
    let mut i = 0;
    while i < 33 {
        out[i] = HDR_LABEL[i];
        i += 1;
    }
    let mut j = 0;
    while j < 8 {
        out[33 + j] = eb[j];
        j += 1;
    }
    let mut m = 0;
    while m < HEADER_SIZE {
        out[41 + m] = hdr[m];
        m += 1;
    }
    out
}

/// MAC input for a ciphertext:
/// `"Signal_PQCKA_V1_MLKEM768:ciphertext" ‖ ToBytes(epoch) ‖ ct`.
/// Mirrors the `ct_mac_data` built in `Authenticator::mac_ct`/`verify_ct`. The MACed
/// `ct` is the full ML-KEM-768 ciphertext `ct1 ‖ ct2` (960 + 128 = 1088 bytes): the
/// caller does `ct1.extend_from_slice(&ct2); auth.mac_ct(epoch, &ct1)`
/// (`v1/unchunked/send_ct.rs:191-193`; verified symmetrically in `send_ek.rs:160`).
///
/// XREF: spqr authenticator.rs:67-72 @f2589fe (`Authenticator::mac_ct`), data assembled at
/// send_ct.rs:191-193 (ct = ct1‖ct2 = 1088 B) [type-only — exact — corrected after audit: an earlier
/// draft MACed a standalone 128-byte ct2, which is never what upstream covers].
pub fn mac_ct_data(ep: u64, ct: [u8; 1088]) -> [u8; 1131] {
    let eb = epoch_to_be_bytes(ep);
    let mut out = [0u8; 1131];
    let mut i = 0;
    while i < 35 {
        out[i] = CT_LABEL[i];
        i += 1;
    }
    let mut j = 0;
    while j < 8 {
        out[35 + j] = eb[j];
        j += 1;
    }
    let mut m = 0;
    while m < CIPHERTEXT_SIZE {
        out[43 + m] = ct[m];
        m += 1;
    }
    out
}

// ── Constant-time comparison (util.rs, from libcrux-ml-kem constant_time_ops) ──

/// Return 1 if `value` is non-zero, 0 otherwise — branch-free. Mirrors
/// `util::inz`: `((value | (!value).wrapping_add(1)) >> 8) & 1`. (SPQR wraps this
/// in `core::hint::black_box` to defeat the optimizer; that barrier is a
/// non-functional intrinsic and is dropped here.)
///
/// XREF: spqr util.rs:7-13 @f2589fe (`util::inz`) [type-only — exact; `core::hint::black_box` dropped —
/// a non-functional optimizer barrier].
fn inz(value: u8) -> u8 {
    let value = value as u16;
    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;
    result as u8
}

/// Return 0 iff the two 32-byte MACs are equal, branch-free over the bytes.
/// Mirrors `util::compare` specialized to `MACSIZE`-length inputs: accumulate
/// `r |= lhs[i] ^ rhs[i]`, then `is_non_zero(r)`. Used by `verify_ct`/`verify_hdr`
/// (`compare(expected, &mac) != 0` ⇒ reject).
///
/// XREF: spqr util.rs:25-33 @f2589fe (`util::compare`) [type-only — exact; specialized to the
/// `MACSIZE`-length (32-byte) inputs the verifiers use, vs upstream's generic `&[u8]`].
pub fn compare(lhs: [u8; 32], rhs: [u8; 32]) -> u8 {
    let mut r: u8 = 0;
    let mut i = 0;
    while i < MACSIZE {
        r |= lhs[i] ^ rhs[i];
        i += 1;
    }
    inz(r)
}
