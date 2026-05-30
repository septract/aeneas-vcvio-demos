//! PQXDH key-schedule glue — the byte-exact assembly of the PQXDH secret input
//! and the split of the KDF output, as in Signal's `rust/protocol/src/pqxdh.rs`
//! (signalapp/libsignal, HEAD `5441a83`).
//!
//! This is a faithful, Aeneas-extractable analog of the *deterministic key
//! schedule* of PQXDH: the part that orders the Diffie–Hellman outputs and the
//! ML-KEM shared secret, prepends the all-`0xFF` "discontinuity bytes", and
//! slices the 96-byte HKDF output into (`root_key`, `chain_key`, `pqr_key`). The
//! cryptographic primitives themselves — X25519 `calculate_agreement`, ML-KEM
//! `encapsulate`/`decapsulate`, and `hkdf::Hkdf::<Sha256>::expand` — are external
//! (dalek / libcrux / RustCrypto) and out of the extraction fragment; here their
//! outputs are the `[u8; 32]` inputs. That is exactly the right boundary: the
//! **key schedule and associated-data construction is the error-dense glue** —
//! the Bhargavan–Jacomme–Kiefer–Schmidt (USENIX'24) re-encapsulation attack on
//! PQXDH was a domain-separation bug in precisely this assembly, not in any
//! primitive. Putting the byte layout under extraction is what surfaces such bugs.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits;
//! fixed-size arrays and `while` loops (mirroring `Vec::extend_from_slice`).

// In PQXDH every X25519 agreement and the ML-KEM shared secret are 32 bytes.
const DH_LEN: usize = 32;

/// Copy a 32-byte segment `src` into `out` starting at byte offset `off`.
/// Models one `secrets.extend_from_slice(&dh)` against a pre-sized buffer.
fn put32(out: &mut [u8], off: usize, src: &[u8; 32]) {
    let mut i = 0;
    while i < DH_LEN {
        out[off + i] = src[i];
        i += 1;
    }
}

/// Assemble the PQXDH secret input **without** a one-time prekey (3 DH legs).
///
/// Mirrors `pqxdh_initiate` / `pqxdh_accept` when `their_one_time_pre_key` is
/// `None`: `[0xFF; 32] ‖ DH1 ‖ DH2 ‖ DH3 ‖ SS`. The leading `0xFF` block is the
/// X3DH/PQXDH "discontinuity bytes" (`secrets.extend_from_slice(&[0xFFu8; 32])`).
///   DH1 = DH(IK_A, SPK_B), DH2 = DH(EK_A, IK_B), DH3 = DH(EK_A, SPK_B),
///   SS  = ML-KEM shared secret encapsulated to the Kyber prekey.
pub fn pqxdh_secret_input(
    dh1: [u8; 32],
    dh2: [u8; 32],
    dh3: [u8; 32],
    ss: [u8; 32],
) -> [u8; 160] {
    let mut out = [0u8; 160];
    let mut i = 0;
    while i < DH_LEN {
        out[i] = 0xFFu8; // discontinuity bytes
        i += 1;
    }
    put32(&mut out, 32, &dh1);
    put32(&mut out, 64, &dh2);
    put32(&mut out, 96, &dh3);
    put32(&mut out, 128, &ss);
    out
}

/// Assemble the PQXDH secret input **with** a one-time prekey (4 DH legs).
///
/// Mirrors the `if let Some(their_one_time_prekey) = …` branch:
/// `[0xFF; 32] ‖ DH1 ‖ DH2 ‖ DH3 ‖ DH4 ‖ SS`, where DH4 = DH(EK_A, OPK_B) is
/// spliced in *before* the KEM shared secret.
pub fn pqxdh_secret_input_with_opk(
    dh1: [u8; 32],
    dh2: [u8; 32],
    dh3: [u8; 32],
    dh4: [u8; 32],
    ss: [u8; 32],
) -> [u8; 192] {
    let mut out = [0u8; 192];
    let mut i = 0;
    while i < DH_LEN {
        out[i] = 0xFFu8; // discontinuity bytes
        i += 1;
    }
    put32(&mut out, 32, &dh1);
    put32(&mut out, 64, &dh2);
    put32(&mut out, 96, &dh3);
    put32(&mut out, 128, &dh4);
    put32(&mut out, 160, &ss);
    out
}

/// Split the 96-byte HKDF output into the three ratchet-initialization arrays.
///
/// Mirrors `HandshakeKeys::derive_with_label`'s `derive_arrays(|bytes| …expand…)`,
/// which fills one `N1+N2+N3 = 32+32+32` buffer and reinterprets it as
/// `(root_key, chain_key, pqr_key)` (`libsignal_core::derive_arrays`). The HKDF
/// `expand` over the secret input — with `info` = the
/// `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024` label — is the external,
/// opaque step; this is the pure de-serialization of its output.
pub fn derive_split(okm: [u8; 96]) -> ([u8; 32], [u8; 32], [u8; 32]) {
    let mut root_key = [0u8; 32];
    let mut chain_key = [0u8; 32];
    let mut pqr_key = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        root_key[i] = okm[i];
        chain_key[i] = okm[32 + i];
        pqr_key[i] = okm[64 + i];
        i += 1;
    }
    (root_key, chain_key, pqr_key)
}

// ── EC public-key wire encoding (rust/core/src/curve.rs) ──────────────────────

/// The single-byte curve tag for Curve25519 / "DJB" keys (`KeyType::Djb.value()`).
const KEY_TYPE_DJB: u8 = 0x05;

/// Encode a Curve25519 public key to its 33-byte wire form.
///
/// Mirrors `PublicKey::serialize`: a one-byte `KeyType` tag followed by the
/// 32-byte u-coordinate (`result.push(self.key_type().value()); result.extend(v)`).
/// This `EncodeEC` is the function whose pairwise-disjoint ranges the PQXDH spec
/// (§2.1) and the AD construction depend on.
pub fn encode_ec(key: [u8; 32]) -> [u8; 33] {
    let mut out = [0u8; 33];
    out[0] = KEY_TYPE_DJB;
    let mut i = 0;
    while i < 32 {
        out[1 + i] = key[i];
        i += 1;
    }
    out
}

/// Decode a 33-byte wire public key back to its u-coordinate, or `None` on a
/// bad curve tag.
///
/// Mirrors `PublicKey::deserialize`: read the leading `key_type` byte
/// (`split_first`), reject anything but `KeyType::Djb` (`0x05`), and return the
/// following 32-byte chunk. `DecodeEC` is required to be the inverse of
/// `EncodeEC` (spec §2.1); `decode_ec ∘ encode_ec = Some` is the natural
/// round-trip adequacy lemma on the Lean side.
pub fn decode_ec(bytes: [u8; 33]) -> Option<[u8; 32]> {
    if bytes[0] != KEY_TYPE_DJB {
        return None;
    }
    let mut key = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        key[i] = bytes[1 + i];
        i += 1;
    }
    Some(key)
}

/// Build the PQXDH "associated data" `AD = EncodeEC(IK_A) ‖ EncodeEC(IK_B)`
/// (spec §3.3), the identity-binding context for the initial AEAD ciphertext.
/// Two 33-byte encoded identity keys, concatenated.
pub fn associated_data(ika: [u8; 32], ikb: [u8; 32]) -> [u8; 66] {
    let a = encode_ec(ika);
    let b = encode_ec(ikb);
    let mut out = [0u8; 66];
    let mut i = 0;
    while i < 33 {
        out[i] = a[i];
        out[33 + i] = b[i];
        i += 1;
    }
    out
}
