//! A real ARX block function — ChaCha20 — keyed by the 32-byte ratchet chain key
//! (fixed zero counter+nonce), producing a 64-byte output block. This is the concrete,
//! cryptographically-substantive `G : ck -> block` that the ratchet (demo 3) iterates: the
//! extracted node now does genuine add/xor/rotate arithmetic, not a memcpy. Its
//! pseudorandomness is the (standard, named) hardness assumption; the Lean side proves only
//! that the extraction is *total* (value adequacy), then plugs it into the generic ratchet
//! security theorem.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits; fixed-size
//! arrays; only the `wrapping_add` / `rotate_left` intrinsics, shifts, casts, and `^`.

/// One ChaCha quarter-round on four words (pure, total: wrapping add / xor / rotate).
pub fn quarter(a: u32, b: u32, c: u32, d: u32) -> (u32, u32, u32, u32) {
    let mut a = a;
    let mut b = b;
    let mut c = c;
    let mut d = d;
    a = a.wrapping_add(b);
    d ^= a;
    d = d.rotate_left(16);
    c = c.wrapping_add(d);
    b ^= c;
    b = b.rotate_left(12);
    a = a.wrapping_add(b);
    d ^= a;
    d = d.rotate_left(8);
    c = c.wrapping_add(d);
    b ^= c;
    b = b.rotate_left(7);
    (a, b, c, d)
}

/// One double round: four column quarter-rounds then four diagonal quarter-rounds.
pub fn double_round(s: [u32; 16]) -> [u32; 16] {
    let mut s = s;
    let (a, b, c, d) = quarter(s[0], s[4], s[8], s[12]);
    s[0] = a;
    s[4] = b;
    s[8] = c;
    s[12] = d;
    let (a, b, c, d) = quarter(s[1], s[5], s[9], s[13]);
    s[1] = a;
    s[5] = b;
    s[9] = c;
    s[13] = d;
    let (a, b, c, d) = quarter(s[2], s[6], s[10], s[14]);
    s[2] = a;
    s[6] = b;
    s[10] = c;
    s[14] = d;
    let (a, b, c, d) = quarter(s[3], s[7], s[11], s[15]);
    s[3] = a;
    s[7] = b;
    s[11] = c;
    s[15] = d;
    let (a, b, c, d) = quarter(s[0], s[5], s[10], s[15]);
    s[0] = a;
    s[5] = b;
    s[10] = c;
    s[15] = d;
    let (a, b, c, d) = quarter(s[1], s[6], s[11], s[12]);
    s[1] = a;
    s[6] = b;
    s[11] = c;
    s[12] = d;
    let (a, b, c, d) = quarter(s[2], s[7], s[8], s[13]);
    s[2] = a;
    s[7] = b;
    s[8] = c;
    s[13] = d;
    let (a, b, c, d) = quarter(s[3], s[4], s[9], s[14]);
    s[3] = a;
    s[4] = b;
    s[9] = c;
    s[14] = d;
    s
}

/// Load one little-endian u32 word from four bytes.
fn load_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

/// The ChaCha20 block function keyed by a 32-byte key (zero counter and nonce).
pub fn chacha20_block(key: [u8; 32]) -> [u8; 64] {
    // Build the 16-word initial state: 4 constants, 8 key words, counter (1 word), nonce (3).
    let mut state = [0u32; 16];
    state[0] = 0x61707865;
    state[1] = 0x3320646e;
    state[2] = 0x79622d32;
    state[3] = 0x6b206574;
    let mut i = 0;
    while i < 8 {
        state[4 + i] = load_le(key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]);
        i += 1;
    }
    // state[12..16] = counter and nonce = 0 (already zero).

    // Working copy, 20 rounds = 10 double rounds.
    let mut work = state;
    let mut r: usize = 0;
    while r < 10 {
        work = double_round(work);
        r += 1;
    }

    // Add the original state and serialize little-endian to 64 bytes.
    let mut out = [0u8; 64];
    let mut j = 0;
    while j < 16 {
        let w = work[j].wrapping_add(state[j]);
        out[4 * j] = (w & 0xff) as u8;
        out[4 * j + 1] = ((w >> 8) & 0xff) as u8;
        out[4 * j + 2] = ((w >> 16) & 0xff) as u8;
        out[4 * j + 3] = ((w >> 24) & 0xff) as u8;
        j += 1;
    }
    out
}
