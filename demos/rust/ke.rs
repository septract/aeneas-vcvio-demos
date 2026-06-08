//! SYNTHETIC one-pass KEM-based key transport — a Demo-6 extraction target.
//!
//! This file makes NO security claim by itself: the functions are simple, total byte transforms
//! over fixed 32-byte arrays, written to be a clean Charon+Aeneas extraction target (modeled on
//! `demos/rust/mac.rs`: fixed `[u8; N]`, `while`-loops, no Vec / generics / traits / unsafe / FFI).
//!
//! The PROTOCOL is textbook one-pass key transport (Boneh-Shoup, *A Graduate Course in Applied
//! Cryptography* v0.6, §11.5, scheme `E_EG`): the responder encapsulates a shared secret to the
//! initiator's public key, and the session key is derived as `H(shared_secret)` — a KDF/hash of the
//! SINGLE shared secret. (Demo-6 v1's bug was deriving the session key as `k_i XOR k_r` of two
//! cross-encapsulated secrets, which the XOR structurally annihilated to a constant; this version
//! derives from one shared secret via an INJECTIVE transform and is entropy-preserving.)
//!
//! On the Lean side: `keygen`/`encaps`/`decaps` are the extracted KEM ops (functional correctness
//! is proved; IND-CPA is carried as an explicit ASSUMPTION on the KEM, exactly as the eventual real
//! proof assumes ML-KEM IND-CCA). `derive_session_key` models the KDF `H`; the demo's reduction
//! discharges the session-key key-indistinguishability to the KEM's assumed IND-CPA advantage
//! (single session ≈ Boneh-Shoup Thm 11.4 core; multi-session via the standard Q-query hybrid,
//! Boneh-Shoup §5.4). The Rust here is the faithful wiring; the security assumption lives in Lean.

/// Public-key / secret-key / ciphertext / shared-secret / session-key length, all 32 bytes.
pub const KE_LEN: usize = 32;

/// Deterministic keygen from a 32-byte seed: `pk[i] = seed[i]`, `sk[i] = seed[i] ^ 0xFF`.
/// (Randomness stays on the Lean side; this is the deterministic core.)
pub fn keygen(seed: [u8; 32]) -> ([u8; 32], [u8; 32]) {
    let mut pk = [0u8; 32];
    let mut sk = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        pk[i] = seed[i];
        sk[i] = seed[i] ^ 0xFF;
        i += 1;
    }
    (pk, sk)
}

/// Encapsulate against `pk` using `coins`: `ct[i] = pk[i] ^ coins[i]`, `shared[i] = pk[i] & coins[i]`.
/// Returns `(ct, shared_secret)`. (The KEM's IND-CPA is ASSUMED on the Lean side, not implied by
/// these transforms — this is the functional wiring only.)
pub fn encaps(pk: [u8; 32], coins: [u8; 32]) -> ([u8; 32], [u8; 32]) {
    let mut ct = [0u8; 32];
    let mut shared = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        ct[i] = pk[i] ^ coins[i];
        shared[i] = pk[i] & coins[i];
        i += 1;
    }
    (ct, shared)
}

/// Decapsulate `ct` with `sk`: recompute `pk[i] = sk[i] ^ 0xFF`, `coins[i] = ct[i] ^ pk[i]`,
/// `shared[i] = pk[i] & coins[i]`. Total (no Option); returns the shared secret directly.
/// Correctness: `decaps(sk, encaps(pk, coins).0) = encaps(pk, coins).1` when `(pk, sk)` is a keypair.
pub fn decaps(sk: [u8; 32], ct: [u8; 32]) -> [u8; 32] {
    let mut shared = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let pk_i = sk[i] ^ 0xFF;
        let coins_i = ct[i] ^ pk_i;
        shared[i] = pk_i & coins_i;
        i += 1;
    }
    shared
}

/// Derive the session key from the SINGLE shared secret: the KDF `H` of the textbook scheme.
/// Here an INJECTIVE byte transform (`out[i] = shared[i] ^ 0x5C`, a domain-separated copy) — distinct
/// shared secrets give distinct session keys (entropy-preserving), unlike the v1 XOR-of-two-keys
/// combiner. On the Lean side `H` is modeled as a PRF/RO and the session key's pseudorandomness
/// reduces to the shared secret's unpredictability (the KEM assumption). This transform is NOT itself
/// a secure KDF; it is the wiring where the assumption plugs in.
pub fn derive_session_key(shared: [u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = shared[i] ^ 0x5C;
        i += 1;
    }
    out
}

/// Constant-length all-bytes equality (clone of `mac.verify`) — Test/freshness comparison glue.
pub fn key_eq(a: [u8; 32], b: [u8; 32]) -> bool {
    let mut i = 0;
    let mut ok = true;
    while i < 32 {
        if a[i] != b[i] {
            ok = false;
        }
        i += 1;
    }
    ok
}
