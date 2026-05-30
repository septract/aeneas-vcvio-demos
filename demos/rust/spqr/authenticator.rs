//! SPQR Ratcheted Authenticator glue — domain-separation string assembly, the
//! `root_key`/`mac_key` update split, and the constant-time MAC comparison, as
//! in SPQR's `src/authenticator.rs` and `src/util.rs`
//! (signalapp/SparsePostQuantumRatchet, HEAD `f2589fe`).
//!
//! Faithful, Aeneas-extractable analog of the authenticator's *non-cryptographic*
//! core. The MAC and KDF themselves (`libcrux_hmac::hmac`, `hkdf::Hkdf::<Sha256>`)
//! are external and are marked `#[hax_lib::opaque]` in SPQR's own kdf module — we
//! keep the same boundary, modelling their outputs as `[u8; …]` inputs and lifting
//! only the byte plumbing. That plumbing is where the interesting divergences from
//! the ML-KEM-Braid spec prose live (e.g. the spec says HKDF salt = `root_key`,
//! IKM = `update_key`, but the code feeds salt = `[0; 32]`, IKM = `root_key ‖ k`):
//! the extracted node targets the *code's* actual schedule, not the prose.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits,
//! no `Vec`; fixed-size arrays and `while` loops in place of `[…].concat()`.

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
const CIPHERTEXT2_SIZE: usize = 128;

/// `ToBytes(epoch)` — big-endian encoding of a 64-bit epoch. Mirrors
/// `ep.to_be_bytes()` (the spec recommends big-endian for `EPOCH_TYPE = u64`).
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

/// MAC input for a `ct2` ciphertext:
/// `"Signal_PQCKA_V1_MLKEM768:ciphertext" ‖ ToBytes(epoch) ‖ ct2`.
/// Mirrors the `ct_mac_data` built in `Authenticator::mac_ct` (ct2 is the fixed
/// 128-byte ML-KEM-768 second ciphertext component).
pub fn mac_ct2_data(ep: u64, ct2: [u8; 128]) -> [u8; 171] {
    let eb = epoch_to_be_bytes(ep);
    let mut out = [0u8; 171];
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
    while m < CIPHERTEXT2_SIZE {
        out[43 + m] = ct2[m];
        m += 1;
    }
    out
}

// ── Constant-time comparison (util.rs, from libcrux-ml-kem constant_time_ops) ──

/// Return 1 if `value` is non-zero, 0 otherwise — branch-free. Mirrors
/// `util::inz`: `((value | (!value).wrapping_add(1)) >> 8) & 1`. (SPQR wraps this
/// in `core::hint::black_box` to defeat the optimizer; that barrier is a
/// non-functional intrinsic and is dropped here.)
fn inz(value: u8) -> u8 {
    let value = value as u16;
    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;
    result as u8
}

/// Return 0 iff the two 32-byte MACs are equal, branch-free over the bytes.
/// Mirrors `util::compare` specialized to `MACSIZE`-length inputs: accumulate
/// `r |= lhs[i] ^ rhs[i]`, then `is_non_zero(r)`. Used by `verify_ct`/`verify_hdr`
/// (`compare(expected, &mac) != 0` ⇒ reject).
pub fn compare(lhs: [u8; 32], rhs: [u8; 32]) -> u8 {
    let mut r: u8 = 0;
    let mut i = 0;
    while i < MACSIZE {
        r |= lhs[i] ^ rhs[i];
        i += 1;
    }
    inz(r)
}
