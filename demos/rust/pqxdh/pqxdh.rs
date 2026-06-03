#![feature(register_tool)]
#![register_tool(charon)]

//! PQXDH key agreement — an Aeneas-extractable mirror of Signal's
//! `rust/protocol/src/pqxdh.rs` (signalapp/libsignal, HEAD `5441a83`).
//!
//! This models the **full PQXDH key agreement** on both sides: `pqxdh_initiate`
//! (compute the X25519 agreements + the ML-KEM encapsulation, assemble the secret
//! input, run the KDF, return the derived keys and the ciphertext to send) and
//! `pqxdh_accept` (validate the base key, compute the matching agreements + the
//! ML-KEM decapsulation, assemble the same secret input, run the KDF). The
//! *orchestration* — which key produces which agreement leg, in which order, and how
//! the legs and the KEM shared secret feed the KDF — is genuine extracted Rust, so a
//! security proof can quantify over the real wiring rather than re-modelling it.
//!
//! The cryptographic primitives themselves — X25519 `calculate_agreement`, ML-KEM
//! `encapsulate`/`decapsulate`, `hkdf::Hkdf::<Sha256>::expand`, and the EC
//! `is_canonical` check — are external crates (dalek / libcrux / RustCrypto) and the
//! assumed cryptographic **hardness floor**. They are modelled as `#[charon::opaque]`
//! functions, which Aeneas emits as Lean `axiom`s of the given signature: the
//! primitives' *behaviour* is a named trust assumption, but their *call sites* (the
//! wiring) are extracted and checked. This is the error-dense layer the
//! Bhargavan–Jacomme–Kiefer–Schmidt (USENIX'24) re-encapsulation attack lived in.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits;
//! fixed-size arrays, structs, `Option`, and `while` loops (mirroring
//! `Vec::extend_from_slice`). RNG is handled by derandomisation — the KEM
//! encapsulation takes explicit `coins` (the real `encapsulate` draws them from a
//! CSPRNG).
//!
//! ## Correspondence & coverage
//!
//! Upstream: signalapp/libsignal @`5441a83` — `rust/protocol/src/pqxdh.rs`,
//! `rust/protocol/src/kem.rs`, `rust/core/src/curve.rs`, `rust/core/src/lib.rs`.
//! Per-site divergences are tagged `XREF:` below (grep `XREF` across `demos/rust`).
//!
//! NOT modeled from this feature (out of the Aeneas fragment or deferred):
//!   - the **primitive bodies**: X25519 `calculate_agreement`, ML-KEM `encapsulate`/
//!     `decapsulate`, `hkdf::Hkdf::<Sha256>::expand`, `PublicKey::is_canonical` — the
//!     opaque hardness floor (modelled as `axiom`s; their *call sites* ARE extracted);
//!   - the `Handshake` trait, `*Store` threading, prekey-bundle fetch, and the
//!     signed-prekey *signature* verification (it lives in the bundle-processing layer
//!     above `pqxdh.rs`, not in `initiate`/`accept` — an explicit authenticity
//!     assumption here);
//!   - session/ratchet initialization from the derived keys;
//!   - the message-layer MAC over `AD ‖ ciphertext` (`protocol.rs` `compute_mac`) —
//!     only the `AD` identity prefix is built here (see `associated_data`).

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
///
/// XREF: libsignal pqxdh.rs:198-230 (initiate), :335-373 (accept) @5441a83 — upstream
/// accumulates `secrets: Vec<u8>` with `extend_from_slice` (0xFF prefix at :200/:337);
/// mirror writes a fixed `[u8;160]` [type-only: no growable Vec]. Byte layout identical.
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
///
/// XREF: libsignal pqxdh.rs:220-224 (initiate), :360-366 (accept) @5441a83 — the
/// `if let Some(their_one_time_prekey)` branch; mirror writes a fixed `[u8;192]`
/// [type-only: no growable Vec]. Byte layout identical.
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
/// `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024` label (`pqxdh.rs:74`) — is the
/// external, opaque step; this is the pure de-serialization of its output.
///
/// XREF: libsignal core/src/lib.rs:39-65 @5441a83 — `derive_arrays` reinterprets one
/// contiguous buffer as a `#[repr(C)] ([u8;N1],[u8;N2],[u8;N3])` via `zerocopy`; mirror
/// copies the three 32-byte slices [type-only: no zerocopy/transmute]. Order identical.
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
///
/// XREF: libsignal core/src/curve.rs:122-129 @5441a83 (`PublicKey::serialize`,
/// tag `0x05` = `KeyType::Djb` at :28) — upstream returns `Box<[u8]>` via `Vec::push`/
/// `extend_from_slice`; mirror writes a fixed `[u8;33]` [type-only: no Vec/Box]. Bytes identical.
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
///
/// XREF: libsignal core/src/curve.rs:84-91 @5441a83 (`PublicKey::deserialize`)
/// [domain-restricted: mirror's input is exactly `[u8;33]`, vs upstream `&[u8]` of length
/// ≥33 with trailing bytes tolerated (a warning; upstream's own TODO is to make trailing a
/// hard error) — so the mirror omits the ≥34-byte inputs upstream accepts. `Result`→`Option`
/// is type-only]. Accept/reject decision (tag == 0x05) identical on the shared 33-byte domain.
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
/// (spec §3.3), the identity-binding context for the initial AEAD ciphertext —
/// two 33-byte encoded identity keys, concatenated.
///
/// Note: this is the AD *identity prefix* only. libsignal does not materialize this
/// buffer; its message-layer MAC (`protocol.rs` `compute_mac`) feeds the serialized
/// `IK_A`, serialized `IK_B`, and the message bytes into HMAC sequentially. So the
/// full authenticated input downstream is `AD ‖ ciphertext`, of which this is the
/// `AD` part.
///
/// XREF: libsignal protocol.rs:237-239 @5441a83 (`compute_mac`) [type-only for the AD bytes:
/// upstream never materializes this buffer — it feeds `IK_A.serialize()`, `IK_B.serialize()`,
/// then the message into HMAC in sequence; mirror builds the `AD` identity-prefix `[u8;66]`,
/// byte-identical to that prefix. The message component (full MAC input `AD ‖ ciphertext`)
/// is a separate node, not modeled here].
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

// ── The opaque cryptographic primitives (the hardness floor) ──────────────────
//
// X25519 agreement, ML-KEM-1024 (Kyber1024) encaps/decaps, HKDF-Expand, and the
// EC canonicity check are external crates (dalek / libcrux / RustCrypto). They are
// the assumed hardness floor: we do NOT extract their bodies. Marking them
// `#[charon::opaque]` makes Charon/Aeneas emit them as Lean `axiom`s of the given
// signature — so the *orchestration* (which key feeds which agreement, in which
// order, into the KDF) is genuine extracted Rust, while the primitives' behaviour
// is an explicit, named trust assumption. Their Rust signatures are infallible;
// Aeneas conservatively wraps every opaque call in `Result`, so the orchestration's
// value-adequacy is stated relative to the primitives succeeding (see the Lean node).

/// X25519 Diffie–Hellman: `our_private.calculate_agreement(their_public)` → 32-byte
/// shared secret. (libsignal `curve.rs` `PrivateKey::calculate_agreement`.)
#[charon::opaque]
fn x25519_agree(_our_private: [u8; 32], _their_public: [u8; 32]) -> [u8; 32] {
    [0u8; 32]
}

/// ML-KEM-1024 (Kyber1024) encapsulation to a public key, derandomised: `coins` is
/// the explicit randomness (the real `encapsulate` draws it from the CSPRNG).
/// Returns the 32-byte shared secret and the serialized ciphertext (1568-byte
/// Kyber1024 ciphertext + the 1-byte `0x08` key-type tag). (libsignal `kem.rs`
/// `PublicKey::encapsulate`.)
#[charon::opaque]
fn mlkem_encapsulate(_their_public: [u8; 1568], _coins: [u8; 32]) -> ([u8; 32], [u8; 1569]) {
    ([0u8; 32], [0u8; 1569])
}

/// ML-KEM-1024 (Kyber1024) decapsulation: recover the 32-byte shared secret from a
/// serialized ciphertext using the 3168-byte secret key. (libsignal `kem.rs`
/// `SecretKey::decapsulate`.) Note: as an opaque total function on `[u8; 1569]`, this
/// models decapsulation only on well-formed ciphertexts; upstream's `decapsulate` first
/// runs `Ciphertext::deserialize` (rejecting a wrong `0x08` tag or wrong length), so the
/// recipient's reject surface here is narrower than upstream's — a consequence of the
/// hardness-floor abstraction, not a wiring divergence.
#[charon::opaque]
fn mlkem_decapsulate(_our_secret: [u8; 3168], _ciphertext: [u8; 1569]) -> [u8; 32] {
    [0u8; 32]
}

/// HKDF-SHA256 expand with no salt (`Hkdf::<Sha256>::new(None, ikm)` — an HKDF `None`
/// salt is a `HashLen`-zero salt block, i.e. 32 zero bytes, not a zero-length salt),
/// filling the 96-byte `(root_key ‖ chain_key ‖ pqr_key)` output keyed on `ikm` (the
/// secret input) with `info` (the domain-separation label). (libsignal `pqxdh.rs`
/// `HandshakeKeys::derive_with_label`.)
#[charon::opaque]
fn hkdf_sha256_derive(_ikm: &[u8], _info: &[u8]) -> [u8; 96] {
    [0u8; 96]
}

/// Whether a received Curve25519 public key is canonical — the receiver's base-key
/// validation. (libsignal `curve.rs` `PublicKey::is_canonical` / `pqxdh.rs:328`.)
#[charon::opaque]
fn ec_is_canonical(_public_key: [u8; 32]) -> bool {
    true
}

/// The PQXDH HKDF domain-separation label (`HandshakeKeys::derive`, `pqxdh.rs:74`).
const PQXDH_LABEL: [u8; 46] = *b"WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024";

// ── Key material (the prekey-bundle / parameter types) ────────────────────────

/// A Curve25519 key pair (only the private half is used in agreement). Mirror of
/// libsignal `KeyPair` / `IdentityKeyPair` (the public half is carried for fidelity).
pub struct KeyPair {
    pub private_key: [u8; 32],
    pub public_key: [u8; 32],
}

/// The keys derived from a PQXDH handshake, ready for ratchet initialization
/// (libsignal `HandshakeKeys`).
pub struct HandshakeKeys {
    pub root_key: [u8; 32],
    pub chain_key: [u8; 32],
    pub pqr_key: [u8; 32],
}

/// The initiator's output: the derived keys plus the KEM ciphertext to send to the
/// recipient (libsignal `InitiatorAgreement`).
pub struct InitiatorAgreement {
    pub keys: HandshakeKeys,
    pub kyber_ciphertext: [u8; 1569],
}

/// Initiator parameters: our identity and ephemeral key pairs, and the recipient's
/// prekey-bundle public keys. Mirror of libsignal `InitiatorParameters`
/// (`their_ratchet_key` / `self_session` are downstream of the key schedule and
/// omitted; they do not affect the derived secret).
pub struct InitiatorParameters {
    pub our_identity_key_pair: KeyPair,
    pub our_ephemeral_key_pair: KeyPair,
    pub their_identity_key: [u8; 32],
    pub their_signed_pre_key: [u8; 32],
    pub their_one_time_pre_key: Option<[u8; 32]>,
    pub their_kyber_pre_key: [u8; 1568],
}

/// Recipient parameters: our identity / signed-prekey / optional one-time-prekey
/// key pairs and Kyber secret key, plus the initiator's identity, ephemeral (base)
/// key, and KEM ciphertext. Mirror of libsignal `RecipientParameters`.
pub struct RecipientParameters {
    pub our_identity_key_pair: KeyPair,
    pub our_signed_pre_key_pair: KeyPair,
    pub our_one_time_pre_key_pair: Option<KeyPair>,
    pub our_kyber_secret_key: [u8; 3168],
    pub their_identity_key: [u8; 32],
    pub their_ephemeral_key: [u8; 32],
    pub their_kyber_ciphertext: [u8; 1569],
}

// ── The PQXDH key agreement (initiator / recipient) ───────────────────────────

/// **Initiator side of PQXDH** (libsignal `pqxdh_initiate`): compute the three (or,
/// with a one-time prekey, four) X25519 agreements and the ML-KEM encapsulation,
/// assemble the secret input `0xFF³² ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ SS`, run HKDF, and
/// split the output into `(root, chain, pqr)`; return those keys and the KEM
/// ciphertext to send.
///   DH1 = DH(IK_A, SPK_B), DH2 = DH(EK_A, IK_B), DH3 = DH(EK_A, SPK_B),
///   DH4 = DH(EK_A, OPK_B) (only with a one-time prekey), SS = encapsulate(KyberPK_B).
///
/// XREF: libsignal pqxdh.rs:194-236 @5441a83 (`pqxdh_initiate`) [structure-faithful:
/// the agreement/KEM/HKDF *call sites and key wiring* are extracted; the primitives
/// themselves (`calculate_agreement`/`encapsulate`/`expand`) are the opaque floor.
/// `Vec`→fixed buffers (the assembly nodes), `Result`/`Rng`→derandomised `coins`. The
/// encapsulation is hoisted above the one-time-prekey branch (vs. appended after DH4
/// upstream): value-equivalent, since `ss` is still placed last in the secret input].
pub fn pqxdh_initiate(params: &InitiatorParameters, coins: [u8; 32]) -> InitiatorAgreement {
    let dh1 = x25519_agree(params.our_identity_key_pair.private_key, params.their_signed_pre_key);
    let dh2 = x25519_agree(params.our_ephemeral_key_pair.private_key, params.their_identity_key);
    let dh3 = x25519_agree(params.our_ephemeral_key_pair.private_key, params.their_signed_pre_key);
    let (ss, ct) = mlkem_encapsulate(params.their_kyber_pre_key, coins);
    let okm = match &params.their_one_time_pre_key {
        Some(opk) => {
            let dh4 = x25519_agree(params.our_ephemeral_key_pair.private_key, *opk);
            let secret_input = pqxdh_secret_input_with_opk(dh1, dh2, dh3, dh4, ss);
            hkdf_sha256_derive(&secret_input, &PQXDH_LABEL)
        }
        None => {
            let secret_input = pqxdh_secret_input(dh1, dh2, dh3, ss);
            hkdf_sha256_derive(&secret_input, &PQXDH_LABEL)
        }
    };
    let (root_key, chain_key, pqr_key) = derive_split(okm);
    InitiatorAgreement {
        keys: HandshakeKeys {
            root_key,
            chain_key,
            pqr_key,
        },
        kyber_ciphertext: ct,
    }
}

/// **Recipient side of PQXDH** (libsignal `pqxdh_accept`): validate the initiator's
/// base key, then compute the matching agreements and the ML-KEM decapsulation,
/// assemble the same secret input, run HKDF, and split into `(root, chain, pqr)`.
/// Returns `None` when the base key is non-canonical (mirroring the early `Err`).
/// The agreements are wired to recover the *same* secret as the initiator:
///   DH1 = DH(SPK_B, IK_A), DH2 = DH(IK_B, EK_A), DH3 = DH(SPK_B, EK_A),
///   DH4 = DH(OPK_B, EK_A) (only with a one-time prekey), SS = decapsulate(CT).
///
/// XREF: libsignal pqxdh.rs:326-376 @5441a83 (`pqxdh_accept`) [structure-faithful:
/// the `is_canonical` guard (:328-333), the agreement/KEM/HKDF call sites and key
/// wiring are extracted; the primitives are the opaque floor; `Result`→`Option`].
pub fn pqxdh_accept(params: &RecipientParameters) -> Option<HandshakeKeys> {
    if !ec_is_canonical(params.their_ephemeral_key) {
        return None;
    }
    let dh1 = x25519_agree(params.our_signed_pre_key_pair.private_key, params.their_identity_key);
    let dh2 = x25519_agree(params.our_identity_key_pair.private_key, params.their_ephemeral_key);
    let dh3 = x25519_agree(params.our_signed_pre_key_pair.private_key, params.their_ephemeral_key);
    let ss = mlkem_decapsulate(params.our_kyber_secret_key, params.their_kyber_ciphertext);
    let okm = match &params.our_one_time_pre_key_pair {
        Some(opk_pair) => {
            let dh4 = x25519_agree(opk_pair.private_key, params.their_ephemeral_key);
            let secret_input = pqxdh_secret_input_with_opk(dh1, dh2, dh3, dh4, ss);
            hkdf_sha256_derive(&secret_input, &PQXDH_LABEL)
        }
        None => {
            let secret_input = pqxdh_secret_input(dh1, dh2, dh3, ss);
            hkdf_sha256_derive(&secret_input, &PQXDH_LABEL)
        }
    };
    let (root_key, chain_key, pqr_key) = derive_split(okm);
    Some(HandshakeKeys {
        root_key,
        chain_key,
        pqr_key,
    })
}
