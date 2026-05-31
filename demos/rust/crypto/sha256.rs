//! SHA-256 compression and one-block hash — the hash primitive under libsignal's
//! HMAC-SHA256 / HKDF (`rust/protocol/src/crypto.rs` uses `sha2::Sha256`, which is
//! this algorithm; the crate delegates to a SIMD/asm core out of the extraction
//! fragment, so we extract a faithful FIPS 180-4 reference of the same function).
//!
//! This is genuine ARX cryptographic arithmetic — the SHA-256 analog of the
//! ratchet demo's ChaCha20 node. Its compression function is the standard,
//! named hardness assumption (PRF / random oracle); the Lean side proves the
//! extraction is *total* (value adequacy), then HMAC/HKDF are built structurally
//! on top of it.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits;
//! fixed-size arrays, `while` loops, and the `wrapping_add` / `rotate_right`
//! intrinsics, shifts, and `^`/`&`/`|`.
//!
//! ## Correspondence & coverage
//!
//! Upstream: SHA-256 = FIPS 180-4 (the `sha2::Sha256` libsignal uses); HMAC = RFC 2104
//! (`crypto.rs` `hmac_sha256`); AEAD = libsignal `rust/protocol/src/crypto.rs`
//! `aes256_ctr_hmacsha256_encrypt`/`_decrypt` @`5441a83`. Per-site `XREF:` below.
//!
//! Divergence classes used in `XREF` tags (grep `XREF` across `demos/rust`):
//!   [type-only]        — functionally identical to upstream, modulo type/representation;
//!   [domain-restricted]— computes upstream's function only on a sub-domain (the only one
//!                        here is the fixed capacity bound — see below);
//!   [bug]              — behavioral difference on the shared domain (none open).
//!
//! `sha256` / `hmac_sha256_var` / `hkdf_extract` / `hkdf_expand_96` / `etm_encrypt_var` /
//! `etm_decrypt_var` are the **functionally-identical** (`[type-only]`) versions — the full
//! multi-block hash, two-pass HMAC, RFC 5869 extract+expand, and encrypt-then-MAC over an
//! arbitrary message — bounded only by a fixed capacity (HASH_CAP=2048, message ≤ 1536), the
//! single type-level concession; over that domain they compute exactly the upstream function.
//!
//! This file also hosts the **SPQR symmetric ratchet step** (`hkdf_expand_64` + `spqr_chain_next`,
//! mirroring SPQR `chain.rs::next_key_internal` @`f2589fe`): the per-direction key chain is an
//! HKDF over a counter-and-label `info` split into the next chain key and the emitted output key.
//! It is genuinely SPQR-layer, but lives here to reuse this crate's SHA/HMAC/HKDF stack rather
//! than duplicate it (each `demos/rust/*.rs` extracts as a standalone crate). See its `XREF` below.
//!
//! NOT modeled (genuinely out of scope here):
//!   - the SHA compression itself is the floor primitive (assumed PRF/RO); everything here is
//!     *above* the floor and extracted, not assumed;
//!   - arbitrary-length HMAC *keys* (>64 bytes, needing `K0 = H(key)`): keys are 32 bytes
//!     throughout the protocols, so HMAC fixes a 32-byte key;
//!   - the AES-CTR keystream is the opaque PRP floor (an input here), not extracted.

/// SHA-256 round constants (FIPS 180-4 §4.2.2): first 32 bits of the fractional
/// parts of the cube roots of the first 64 primes.
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The SHA-256 initial hash value (FIPS 180-4 §5.3.3): fractional parts of the
/// square roots of the first 8 primes.
pub const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Load one big-endian u32 word from four bytes (SHA-256 is big-endian).
fn load_be(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

/// The SHA-256 compression function: absorb one 512-bit block into the 8-word
/// state. Builds the 64-word message schedule, runs 64 rounds, adds the result
/// back to the input state (Davies–Meyer feed-forward). This is the keyed
/// primitive the PRF/RO assumption is made about.
///
/// XREF: FIPS 180-4 §6.2 (the `sha2::Sha256` compression libsignal uses) [type-only —
/// faithful reference of the standard algorithm; sha2's SIMD/asm core is out of fragment].
pub fn sha256_compress(state: [u32; 8], block: [u8; 64]) -> [u32; 8] {
    // Message schedule W[0..64].
    let mut w = [0u32; 64];
    let mut t = 0;
    while t < 16 {
        w[t] = load_be(block[4 * t], block[4 * t + 1], block[4 * t + 2], block[4 * t + 3]);
        t += 1;
    }
    let mut t = 16;
    while t < 64 {
        let w15 = w[t - 15];
        let w2 = w[t - 2];
        let s0 = w15.rotate_right(7) ^ w15.rotate_right(18) ^ (w15 >> 3);
        let s1 = w2.rotate_right(17) ^ w2.rotate_right(19) ^ (w2 >> 10);
        w[t] = w[t - 16]
            .wrapping_add(s0)
            .wrapping_add(w[t - 7])
            .wrapping_add(s1);
        t += 1;
    }

    // Working variables.
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    let mut t = 0;
    while t < 64 {
        let big_s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = h
            .wrapping_add(big_s1)
            .wrapping_add(ch)
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let big_s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = big_s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
        t += 1;
    }

    // Feed-forward: add the working variables back into the state, word by word.
    let work_final = [a, b, c, d, e, f, g, h];
    let mut out = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        out[i] = state[i].wrapping_add(work_final[i]);
        i += 1;
    }
    out
}

/// Serialize the 8-word state to a 32-byte big-endian digest.
fn state_to_bytes(state: [u32; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 8 {
        let w = state[i];
        out[4 * i] = (w >> 24) as u8;
        out[4 * i + 1] = (w >> 16) as u8;
        out[4 * i + 2] = (w >> 8) as u8;
        out[4 * i + 3] = w as u8;
        i += 1;
    }
    out
}

// ── Shared helpers for the variable-length HMAC / AEAD below ───────────────────

/// `K0 ⊕ pad`, where `K0 = key ‖ zeros` (key is 32 ≤ 64 bytes). Bytes 32..64 are
/// `0 ⊕ pad = pad`, already set by the initializer. Used by `hmac_sha256_var`.
fn key_pad_block(key: [u8; 32], pad: u8) -> [u8; 64] {
    let mut out = [pad; 64];
    let mut i = 0;
    while i < 32 {
        out[i] = key[i] ^ pad;
        i += 1;
    }
    out
}

/// MAC tag length: HMAC-SHA256 truncated to 10 bytes (libsignal `crypto.rs`); used by the AEAD.
const TAG_LEN: usize = 10;

// ── Variable-length (bounded) SHA-256 — the multi-block Merkle–Damgård hash ───
//
// `sha256(data, len)` hashes the first `len` bytes of a fixed-capacity buffer,
// applying FIPS 180-4 §5.1.1 padding and iterating `sha256_compress` over the
// resulting blocks. This is the full SHA-256 function (not the single-block
// `sha256_oneblock`), so HMAC/HKDF/AEAD built on it are functionally identical to
// upstream over the bounded domain `len + 9 <= HASH_CAP`. The capacity bounds the
// message length (a type-level concession); HASH_CAP = 2048 covers the largest
// protocol input (HMAC over the 1088-byte ct1‖ct2, i.e. a 1152-byte inner hash).

const HASH_CAP: usize = 2048;

/// Copy a 64-byte block out of `buf` at byte offset `off` (no nested loop in the
/// compression iteration). Requires `off + 64 <= HASH_CAP`.
fn extract_block(buf: [u8; 2048], off: usize) -> [u8; 64] {
    let mut block = [0u8; 64];
    let mut j = 0;
    while j < 64 {
        block[j] = buf[off + j];
        j += 1;
    }
    block
}

/// SHA-256 of the first `len` bytes of `data` (requires `len + 9 <= HASH_CAP`):
/// FIPS 180-4 padding (`0x80`, zeros, 64-bit big-endian bit length) then iterate
/// the compression over `ceil((len + 9) / 64)` blocks.
/// XREF: FIPS 180-4 §5.1.1/§6.2 (the `sha2::Sha256` libsignal uses) [type-only — the full
/// SHA-256 over the bounded domain `len + 9 ≤ HASH_CAP`; capacity is the only concession].
pub fn sha256(data: [u8; 2048], len: usize) -> [u8; 32] {
    let nblocks = (len + 9 + 63) / 64;
    let total = nblocks * 64;

    // Build the padded message in a zero-initialized scratch buffer.
    let mut buf = [0u8; 2048];
    let mut i = 0;
    while i < len {
        buf[i] = data[i];
        i += 1;
    }
    buf[len] = 0x80;
    // Bit length = len*8, in the 64-bit big-endian length field. Multiply in `usize`
    // first (no overflow for the bounded `len`) then widen to `u64`, so the only
    // overflow obligation is `len*8 ≤ usize::MAX`.
    let bitlen = (len * 8) as u64;
    let mut k = 0;
    while k < 8 {
        buf[total - 8 + k] = (bitlen >> (56 - 8 * k)) as u8;
        k += 1;
    }

    // Absorb each 64-byte block.
    let mut state = H0;
    let mut b = 0;
    while b < nblocks {
        let block = extract_block(buf, 64 * b);
        state = sha256_compress(state, block);
        b += 1;
    }
    state_to_bytes(state)
}

// ── Variable-length HMAC-SHA256 (RFC 2104) over the multi-block hash ──────────
//
// `hmac_sha256_var(key, msg, msglen)` = H((K0⊕opad) ‖ H((K0⊕ipad) ‖ msg)) over the
// variable-length `sha256`, for a 32-byte key and an arbitrary (bounded) message.
// This is the full HMAC the protocol uses (e.g. over the 1088-byte ct1‖ct2), not
// the 32-byte-only `hmac_sha256`. Reuses `key_pad_block` for K0⊕pad.

const HMAC_MSG_CAP: usize = 1536;

/// HMAC-SHA256 of `msg[0..msglen]` under a 32-byte key (requires `msglen ≤ 1536`,
/// so the inner hash `64 + msglen ≤ 1600` stays within `HASH_CAP`).
/// XREF: libsignal crypto.rs:48-54 @5441a83 (`hmac_sha256`) / RFC 2104 [type-only — the full
/// two-pass HMAC over the variable hash, any (bounded) message under a 32-byte key].
pub fn hmac_sha256_var(key: [u8; 32], msg: [u8; 1536], msglen: usize) -> [u8; 32] {
    // Inner hash: SHA-256( (K0⊕ipad) ‖ msg ), length 64 + msglen.
    let kb_i = key_pad_block(key, 0x36);
    let mut inner = [0u8; 2048];
    let mut i = 0;
    while i < 64 {
        inner[i] = kb_i[i];
        i += 1;
    }
    let mut i = 0;
    while i < msglen {
        inner[64 + i] = msg[i];
        i += 1;
    }
    let id = sha256(inner, 64 + msglen);
    // Outer hash: SHA-256( (K0⊕opad) ‖ inner_digest ), length 96.
    let kb_o = key_pad_block(key, 0x5c);
    let mut outer = [0u8; 2048];
    let mut i = 0;
    while i < 64 {
        outer[i] = kb_o[i];
        i += 1;
    }
    let mut i = 0;
    while i < 32 {
        outer[64 + i] = id[i];
        i += 1;
    }
    sha256(outer, 96)
}

// ── HKDF-SHA256 (RFC 5869) over the variable-length HMAC ──────────────────────
//
// HKDF-Extract(salt, ikm) = HMAC(salt, ikm). HKDF-Expand(prk, info, L): T(0)="",
// T(i) = HMAC(prk, T(i-1) ‖ info ‖ i), OKM = T(1) ‖ T(2) ‖ … (first L bytes). We
// expand to 96 bytes (3 blocks) — covers PQXDH's `derive` (root‖chain‖pqr) and,
// via a prefix, SPQR's 64-byte KDF_AUTH and 32-byte KDF_OK — with the T-chaining
// spelled out (variable output length is the same shape under a counter loop).

const HKDF_INFO_CAP: usize = 256;

/// HKDF-Extract: `PRK = HMAC(salt, ikm)`.
/// XREF: RFC 5869 §2.2 (HKDF-Extract; `hkdf::Hkdf::<Sha256>::extract`) [type-only —
/// `PRK = HMAC(salt, ikm)` over the variable HMAC].
pub fn hkdf_extract(salt: [u8; 32], ikm: [u8; 1536], ikmlen: usize) -> [u8; 32] {
    hmac_sha256_var(salt, ikm, ikmlen)
}

/// Build the first expand message `info ‖ ctr` (requires `infolen ≤ 256`).
fn hkdf_t1_msg(info: [u8; 256], infolen: usize, ctr: u8) -> [u8; 1536] {
    let mut m = [0u8; 1536];
    let mut i = 0;
    while i < infolen {
        m[i] = info[i];
        i += 1;
    }
    m[infolen] = ctr;
    m
}

/// Build a subsequent expand message `prev ‖ info ‖ ctr` (requires `infolen ≤ 256`).
fn hkdf_tn_msg(prev: [u8; 32], info: [u8; 256], infolen: usize, ctr: u8) -> [u8; 1536] {
    let mut m = [0u8; 1536];
    let mut i = 0;
    while i < 32 {
        m[i] = prev[i];
        i += 1;
    }
    let mut i = 0;
    while i < infolen {
        m[32 + i] = info[i];
        i += 1;
    }
    m[32 + infolen] = ctr;
    m
}

/// HKDF-Expand to 96 bytes: `T1 ‖ T2 ‖ T3` with `T_i = HMAC(prk, T_{i-1}‖info‖i)`
/// (`T0` empty). Requires `infolen ≤ 256`.
/// XREF: RFC 5869 §2.3 (HKDF-Expand; `hkdf::Hkdf::<Sha256>::expand`) [type-only — the
/// `T_i = HMAC(prk, T_{i-1}‖info‖i)` chaining; fixed at 3 output blocks (96 bytes), which is
/// the max the protocols use (PQXDH derive; SPQR via prefix). Variable output is a counter loop].
pub fn hkdf_expand_96(prk: [u8; 32], info: [u8; 256], infolen: usize) -> [u8; 96] {
    let t1 = hmac_sha256_var(prk, hkdf_t1_msg(info, infolen, 1), infolen + 1);
    let t2 = hmac_sha256_var(prk, hkdf_tn_msg(t1, info, infolen, 2), 32 + infolen + 1);
    let t3 = hmac_sha256_var(prk, hkdf_tn_msg(t2, info, infolen, 3), 32 + infolen + 1);
    let mut okm = [0u8; 96];
    let mut i = 0;
    while i < 32 {
        okm[i] = t1[i];
        okm[32 + i] = t2[i];
        okm[64 + i] = t3[i];
        i += 1;
    }
    okm
}

/// HKDF-Expand to 64 bytes: `T1 ‖ T2` with `T_i = HMAC(prk, T_{i-1}‖info‖i)` (`T0` empty).
/// Requires `infolen ≤ 256`. Used by the SPQR chain ratchet step below (`KDF_AUTH` is 64 bytes).
/// XREF: RFC 5869 §2.3 (HKDF-Expand; `hkdf::Hkdf::<Sha256>::expand` for a 64-byte slice)
/// [type-only — same `T_i` chaining as `hkdf_expand_96`, fixed at 2 output blocks].
pub fn hkdf_expand_64(prk: [u8; 32], info: [u8; 256], infolen: usize) -> [u8; 64] {
    let t1 = hmac_sha256_var(prk, hkdf_t1_msg(info, infolen, 1), infolen + 1);
    let t2 = hmac_sha256_var(prk, hkdf_tn_msg(t1, info, infolen, 2), 32 + infolen + 1);
    let mut okm = [0u8; 64];
    let mut i = 0;
    while i < 32 {
        okm[i] = t1[i];
        okm[32 + i] = t2[i];
        i += 1;
    }
    okm
}

// ── SPQR symmetric ratchet step (chain.rs `ChainEpochDirection::next_key_internal`) ──
//
// The SPQR per-direction key chain: from the current chain key and a counter, derive a
// 64-byte block via HKDF over a counter-and-label `info`, then split it into the *next*
// chain key (first 32 bytes) and the emitted *output key* (last 32 bytes). This is the
// symmetric KDF ratchet feeding the SCKA `output_key`s — built on the same SHA/HMAC/HKDF
// stack above (libsignal/SPQR routes it through the `hkdf` crate's `Hkdf::<Sha256>`),
// hence it lives in this crate to reuse that machinery rather than duplicate it.

/// The domain-separation label for the chain-next derivation (31 bytes).
const CHAIN_NEXT_LABEL: [u8; 31] = *b"Signal PQ Ratchet V1 Chain Next";

/// SPQR chain step: `genr8r = HKDF(salt = 0^32, ikm = next, info = (ctr+1)_be ‖ label, 64)`,
/// returning `(ctr+1, genr8r[..32] as the new chain key, genr8r[32..] as the output key)`.
/// Requires `ctr < u32::MAX` (so `ctr+1` does not overflow) — inherited from upstream.
/// XREF: spqr chain.rs:226-245 @f2589fe (`ChainEpochDirection::next_key_internal`) [type-only:
/// `next: &mut [u8]` / `ctr: &mut u32` in-out params → returned `(u32, [u8;32], [u8;32])`;
/// `kdf::hkdf_to_slice` (the `hkdf` crate) → our `hkdf_extract` ∘ `hkdf_expand_64`; the
/// `[ctr.to_be_bytes(), label].concat()` info built explicitly].
pub fn spqr_chain_next(next: [u8; 32], ctr: u32) -> (u32, [u8; 32], [u8; 32]) {
    let ctr1 = ctr + 1;
    // info = ctr1.to_be_bytes() ‖ CHAIN_NEXT_LABEL  (4 + 31 = 35 bytes)
    let ctrb = ctr1.to_be_bytes();
    let mut info = [0u8; 256];
    info[0] = ctrb[0];
    info[1] = ctrb[1];
    info[2] = ctrb[2];
    info[3] = ctrb[3];
    let mut i = 0;
    while i < 31 {
        info[4 + i] = CHAIN_NEXT_LABEL[i];
        i += 1;
    }
    // ikm = next (the current chain key)
    let mut ikm = [0u8; 1536];
    let mut i = 0;
    while i < 32 {
        ikm[i] = next[i];
        i += 1;
    }
    let prk = hkdf_extract([0u8; 32], ikm, 32);
    let genr8r = hkdf_expand_64(prk, info, 35);
    let mut new_next = [0u8; 32];
    let mut out_key = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        new_next[i] = genr8r[i];
        out_key[i] = genr8r[32 + i];
        i += 1;
    }
    (ctr1, new_next, out_key)
}

// ── Variable-length AEAD: stream cipher + encrypt-then-MAC ────────────────────
//
// The variable-length form of `etm_encrypt`/`etm_decrypt` (libsignal `crypto.rs`
// `aes256_ctr_hmacsha256_*`): stream-XOR a `len`-byte message with the AES-CTR
// keystream (opaque PRP floor, an input), then append the first 10 bytes of
// HMAC-SHA256 over the ciphertext; decryption recomputes, compares in constant
// time, and only then XORs back. Now over an arbitrary (bounded) message length.

/// Encrypt-then-MAC over a `len`-byte message: returns `(ciphertext, tag[..10])`.
/// Requires `len ≤ 1536`.
/// XREF: libsignal crypto.rs:56-66 @5441a83 (`aes256_ctr_hmacsha256_encrypt`) [type-only —
/// stream-XOR + HMAC-over-ciphertext + append 10-byte tag, any (bounded) message length;
/// AES-CTR keystream is the opaque PRP floor].
pub fn etm_encrypt_var(
    keystream: [u8; 1536],
    msg: [u8; 1536],
    len: usize,
    mac_key: [u8; 32],
) -> ([u8; 1536], [u8; 10]) {
    let mut c = [0u8; 1536];
    let mut i = 0;
    while i < len {
        c[i] = msg[i] ^ keystream[i];
        i += 1;
    }
    let mac = hmac_sha256_var(mac_key, c, len);
    let mut tag = [0u8; 10];
    let mut j = 0;
    while j < TAG_LEN {
        tag[j] = mac[j];
        j += 1;
    }
    (c, tag)
}

/// Verify-then-decrypt a `len`-byte ciphertext `c` with tag `tag`: recompute the
/// MAC over `c`, compare the first 10 bytes in constant time, and on success
/// return `c ⊕ keystream`. Requires `len ≤ 1536`.
/// XREF: libsignal crypto.rs:68-81 @5441a83 (`aes256_ctr_hmacsha256_decrypt`) [type-only —
/// recompute MAC / constant-time compare / MAC-before-decrypt, any (bounded) length;
/// `Result`→`Option`].
pub fn etm_decrypt_var(
    c: [u8; 1536],
    len: usize,
    tag: [u8; 10],
    keystream: [u8; 1536],
    mac_key: [u8; 32],
) -> Option<[u8; 1536]> {
    let mac = hmac_sha256_var(mac_key, c, len);
    let mut r: u8 = 0;
    let mut k = 0;
    while k < TAG_LEN {
        r |= mac[k] ^ tag[k];
        k += 1;
    }
    if r != 0 {
        return None;
    }
    let mut m = [0u8; 1536];
    let mut i = 0;
    while i < len {
        m[i] = c[i] ^ keystream[i];
        i += 1;
    }
    Some(m)
}
