//! Reed–Solomon field arithmetic over GF(2¹⁶) — the erasure-code substrate of
//! Signal's Sparse Post-Quantum Ratchet (SPQR / ML-KEM Braid).
//!
//! This is a faithful, Aeneas-extractable analog of SPQR's `src/encoding/gf.rs`
//! (signalapp/SparsePostQuantumRatchet, HEAD `f2589fe`). SPQR's `gf.rs` carries
//! two implementations of the field multiply: a SIMD-accelerated one
//! (`pclmulqdq` / `vmull_p64`, gated `#[cfg(not(hax))]`) and a portable
//! `unaccelerated` one used by Signal's *own* hax/F\* verification build
//! (`#[cfg(hax)]`). Extraction here runs plain `charon rustc` (no `--cfg hax`),
//! so the SIMD path cannot be lifted (`core::arch` intrinsics, `unsafe`); we
//! reproduce the portable path verbatim — i.e. exactly the code Signal proves
//! correct against `Spec.GF16` in F\*. The genuine carryless-multiply +
//! polynomial-reduction arithmetic is the SPQR analog of the ratchet demo's
//! ChaCha20 node: real field math, not byte-shuffling.
//!
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits,
//! no SIMD; fixed-width integers, shifts, `wrapping_add`, and `^`.

// https://web.eecs.utk.edu/~jplank/plank/papers/CS-07-593/primitive-polynomial-table.txt
// The primitive polynomial x¹⁶ + x¹² + x³ + x + 1 defining GF(2¹⁶).
pub const POLY: u32 = 0x1100b;

/// Carryless (polynomial) multiplication of two GF(2¹⁶) elements, returning the
/// unreduced degree-<32 product. Mirrors `unaccelerated::poly_mul`: long
/// multiplication, XOR-ing in `a << shift` for every set bit of `b`.
pub fn poly_mul(a: u16, b: u16) -> u32 {
    let mut acc: u32 = 0;
    let me = a as u32;
    let mut shift: u32 = 0;
    while shift < 16 {
        if 0 != b & (1 << shift) {
            acc ^= me << shift;
        }
        shift += 1;
    }
    acc
}

/// Compute the u16 reduction contribution associated with a single byte `a`.
/// Mirrors `reduce::reduce_from_byte`.
fn reduce_from_byte(a: u8) -> u32 {
    let mut a = a;
    let mut out: u32 = 0;
    let mut i: u32 = 8;
    while i > 0 {
        i -= 1;
        if (1 << i) & a != 0 {
            out ^= POLY << i;
            a ^= ((POLY << i) >> 16) as u8;
        }
    }
    out
}

/// Precompute the per-byte reduction table. Mirrors `reduce::reduce_bytes`,
/// whose result SPQR stores in the `REDUCE_BYTES: [u16; 256]` const.
fn reduce_bytes() -> [u16; 256] {
    let mut out = [0u16; 256];
    let mut i: usize = 0;
    while i < 256 {
        out[i] = reduce_from_byte(i as u8) as u16;
        i += 1;
    }
    out
}

/// Reduce a degree-<32 carryless product modulo `POLY` to a GF(2¹⁶) element.
/// Mirrors `reduce::poly_reduce`: two table-driven byte folds (top byte, then
/// the next), which Signal proves equal to the bit-by-bit `Spec.GF16.poly_reduce`.
pub fn poly_reduce(v: u32) -> u16 {
    let table = reduce_bytes();
    let mut v = v;
    let i1 = (v >> 24) as usize;
    v ^= (table[i1] as u32) << 8;
    let shifted_v = (v >> 16) as usize;
    let i2 = shifted_v & 0xFF;
    v ^= table[i2] as u32;
    v as u16
}

/// Field addition in GF(2¹⁶): characteristic-2, so addition is XOR.
/// Mirrors `GF16`'s `AddAssign`/`SubAssign` (`self.value ^= other.value`).
pub fn gf_add(a: u16, b: u16) -> u16 {
    a ^ b
}

/// Field multiplication in GF(2¹⁶): carryless multiply then reduce.
/// Mirrors `unaccelerated::mul` — the portable multiply Signal's hax build uses.
pub fn gf_mul(a: u16, b: u16) -> u16 {
    poly_reduce(poly_mul(a, b))
}

/// Field inverse-and-multiply `self / other`, i.e. `self * other^(2¹⁶-2)` via the
/// square-and-multiply ladder. Mirrors `GF16::const_div` (Fermat inverse in
/// GF(2¹⁶) = GF(65536): `inv(a) = a^(p^n - 2) = a^65534`).
pub fn gf_div(numer: u16, denom: u16) -> u16 {
    let mut square = denom;
    let mut out = numer;
    let mut i: usize = 1;
    while i < 16 {
        square = gf_mul(square, square);
        out = gf_mul(out, square);
        i += 1;
    }
    out
}
