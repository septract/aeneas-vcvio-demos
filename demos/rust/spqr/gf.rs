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
//!
//! ## Correspondence & coverage
//!
//! Upstream: signalapp/SparsePostQuantumRatchet @`f2589fe` — `src/encoding/gf.rs`
//! and `src/encoding/polynomial.rs`. Per-site divergences are tagged `XREF:` below.
//!
//! Modeled here: the field arithmetic (`poly_mul`/`poly_reduce`/`gf_*`), the encoder
//! polynomial core (`poly_eval`/`poly_add`/`poly_scale`), and the **Lagrange-interpolation
//! decoder kernel** (`mult_xdiff_trailing`, `prepare`, `complete`, `lagrange_interpolate`,
//! `compute_at`, `decode_value_at`) over fixed `[u16;37]` coefficient arrays — see the
//! decoder section's header for that node's divergence story.
//!
//! NOT modeled from the codec (out of the Aeneas fragment or deferred):
//!   - the SIMD multiply/reduce path (`accelerated::mul` via `pclmulqdq`/`vmull_p64`,
//!     `unsafe` + `core::arch`) — we take the portable `#[cfg(hax)]` path Signal verifies;
//!   - the `GF16` newtype + its `ops::{Add,Mul,Div,…}` trait impls (we use free `u16` fns);
//!   - the stateful `PolyEncoder`/`PolyDecoder` orchestration (16-way `SortedSet<Pt>`
//!     striping, `necessary_points`, `binary_search`, lazy caching) and the protobuf
//!     `into_pb`/`from_pb`, plus the const-generic precomputed `PolyConst<N>` / `Pt::Ord`
//!     tables (`from_complete_points`, `lagrange_sum`) — `Vec`/iterators/const-generics/IO,
//!     out of the fragment;
//!   - `parallel_mult`'s 2-wide unrolling (we do the scalar pointwise multiply).

// https://web.eecs.utk.edu/~jplank/plank/papers/CS-07-593/primitive-polynomial-table.txt
// The primitive polynomial x¹⁶ + x¹² + x³ + x + 1 defining GF(2¹⁶).
pub const POLY: u32 = 0x1100b;

/// Carryless (polynomial) multiplication of two GF(2¹⁶) elements, returning the
/// unreduced degree-<32 product. Mirrors `unaccelerated::poly_mul`: long
/// multiplication, XOR-ing in `a << shift` for every set bit of `b`.
///
/// XREF: spqr gf.rs:381-427 @f2589fe (`unaccelerated::poly_mul`) [type-only — exact].
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
///
/// XREF: spqr gf.rs:489-498 @f2589fe (`reduce::poly_reduce`; table from
/// `reduce_from_byte` :502-515, `reduce_bytes` :519-535) [type-only — exact; upstream `REDUCE_BYTES`
/// is a `const` table, mirror recomputes it — same values].
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
///
/// XREF: spqr gf.rs:28-31 @f2589fe (`GF16::add_assign`) [type-only — exact; mirror is a free `u16`
/// fn rather than the `ops::AddAssign` trait impl on the `GF16` newtype].
pub fn gf_add(a: u16, b: u16) -> u16 {
    a ^ b
}

/// Field multiplication in GF(2¹⁶): carryless multiply then reduce.
/// Mirrors `unaccelerated::mul` — the portable multiply Signal's hax build uses.
///
/// XREF: spqr gf.rs:444-446 @f2589fe (`unaccelerated::mul`) [type-only — exact]. The SIMD
/// `accelerated::mul` dispatch (`MulAssign`, runtime CPU check) is not modeled (unsafe/SIMD,
/// out of fragment) — it computes the same field product.
pub fn gf_mul(a: u16, b: u16) -> u16 {
    poly_reduce(poly_mul(a, b))
}

/// Field inverse-and-multiply `self / other`, i.e. `self * other^(2¹⁶-2)` via the
/// square-and-multiply ladder. Mirrors `GF16::const_div` (Fermat inverse in
/// GF(2¹⁶) = GF(65536): `inv(a) = a^(p^n - 2) = a^65534`).
///
/// XREF: spqr gf.rs:571-588 @f2589fe (`GF16::const_div`) [type-only — exact; mirror uses the scalar
/// `gf_mul` where upstream's `div_impl` uses the 2-wide `mul2_u16`].
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

// ── Polynomial arithmetic over GF(2¹⁶) (encoding/polynomial.rs core) ──────────
//
// SPQR's Reed–Solomon codec works with polynomials over GF(2¹⁶) (`Poly`, with
// `Vec<GF16>` coefficients). The encoder produces each 32-byte chunk by evaluating
// the message polynomial at successive points; the decoder reconstructs by Lagrange
// interpolation. We extract the in-fragment *field-arithmetic core* over fixed-degree
// polynomials (≤ 35, the `MAX_STORED_POLYNOMIAL_DEGREE_V1`, so ≤ 36 coefficients,
// here `[u16; 36]`): evaluation, pointwise add (`Poly::add_assign`), and scalar
// multiply (`Poly::mult_assign` / `gf::parallel_mult`). The full `Vec`-based Lagrange
// interpolation (the decoder) is outside the fixed-array fragment.

const POLY_COEFFS: usize = 36;

/// Evaluate `sum_{i < deg} coeffs[i] * x^i` at `x` by Horner's rule over GF(2¹⁶).
/// SPQR's `Poly::compute_at` builds an x-power table and dots it with the
/// coefficients; Horner computes the same field value with the same `gf_add`/`gf_mul`.
///
/// XREF: spqr polynomial.rs:255-272 @f2589fe (`Poly::compute_at`) [type-only: Horner vs
/// upstream's x-power-table-and-`zip` (over `Vec`s; out of fragment); mirror is a fixed
/// `[u16;36]` indexed loop]. Same field value on the same polynomial.
pub fn poly_eval(coeffs: [u16; 36], deg: usize, x: u16) -> u16 {
    let mut out: u16 = 0;
    let mut i = deg;
    while i > 0 {
        i -= 1;
        out = gf_add(gf_mul(out, x), coeffs[i]);
    }
    out
}

/// Pointwise field addition of two polynomials (`Poly::add_assign`).
///
/// XREF: spqr polynomial.rs:239-247 @f2589fe (`Poly::add_assign`) [type-only: upstream
/// iterates `other.coefficients` and `push`es on length-mismatch; mirror is a fixed
/// `[u16;36]` pointwise XOR — faithful in the equal-length (≤36-coeff) V1 regime].
pub fn poly_add(a: [u16; 36], b: [u16; 36]) -> [u16; 36] {
    let mut out = [0u16; 36];
    let mut i = 0;
    while i < POLY_COEFFS {
        out[i] = gf_add(a[i], b[i]);
        i += 1;
    }
    out
}

/// Scalar field multiply of a polynomial by `m` (`Poly::mult_assign`).
///
/// XREF: spqr polynomial.rs:250-251 @f2589fe (`Poly::mult_assign` → `gf::parallel_mult`
/// gf.rs:201-214) [type-only: upstream multiplies 2 coeffs at a time over a `&mut Vec`;
/// mirror is a scalar pointwise `gf_mul` over a fixed `[u16;36]`]. Same values.
pub fn poly_scale(a: [u16; 36], m: u16) -> [u16; 36] {
    let mut out = [0u16; 36];
    let mut i = 0;
    while i < POLY_COEFFS {
        out[i] = gf_mul(a[i], m);
        i += 1;
    }
    out
}

// ── Lagrange-interpolation decoder (encoding/polynomial.rs) ───────────────────
//
// The Reed–Solomon *decoder*: given a set of (x, y) points known to lie on a
// message polynomial, reconstruct the polynomial by Lagrange interpolation and
// evaluate it at any index to recover the original data. This is the inverse of
// the encoder's `poly_eval` and the heart of SPQR's erasure decoding.
//
// Upstream represents a polynomial as `Poly { coefficients: Vec<GF16> }` whose
// length varies during interpolation but is bounded — for Protocol V1 by
// `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1 = 37` coefficients (an interpolation
// produces ≤ 36 coefficients; the intermediate `working`/`template` carry one
// more). The one necessary divergence is therefore `Vec<GF16> → [u16; 37]` with an
// explicit length, exactly the bounded-capacity pattern used elsewhere; points
// `&[Pt]` become two parallel `[u16; 36]` arrays (x's and y's) plus a count `n`.
// In GF(2¹⁶) (characteristic 2) subtraction equals addition equals XOR, so
// upstream's `-=` / `pi.x - pj.x` / `const_sub` are all `gf_add` here.
//
// The `n ≤ MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` (= 36) precondition is inherited
// verbatim from upstream's `#[hax_lib::requires(pts.len() <= …)]`. The stateful
// `PolyDecoder` orchestration around this kernel (the 16-way `SortedSet<Pt>`
// striping, `necessary_points`, `binary_search`, lazy per-poly caching, and the
// protobuf `into_pb`/`from_pb`) is container/IO plumbing, out of the fragment.

// Capacities (inlined in the signatures below): points/coefficients are bounded by
// `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` = 36, so a coefficient array is `[u16; 37]`.

/// `coeffs[start-1 ..]` (a trailing sub-polynomial) `*= (x - difference)`, with the
/// carry propagating into `coeffs[start-1]`. Mirrors `Poly::mult_xdiff_assign_trailing`.
///
/// XREF: spqr polynomial.rs:174-181 @f2589fe (`mult_xdiff_assign_trailing`) [type-only:
/// `&mut Vec<GF16>` → functional update on `[u16;37]`+len; `-=` is XOR (char 2)].
fn mult_xdiff_trailing(coeffs: [u16; 37], len: usize, start: usize, difference: u16) -> [u16; 37] {
    let mut out = coeffs;
    let mut i = start;
    while i < len {
        let delta = gf_mul(out[i], difference);
        out[i - 1] = gf_add(out[i - 1], delta);
        i += 1;
    }
    out
}

/// Build `PRODUCT(x - xs[i])` from its highest coefficient down. Returns the
/// `n + 1` coefficients (little-endian). Mirrors `Poly::lagrange_interpolate_prepare`.
///
/// XREF: spqr polynomial.rs:144-163 @f2589fe (`lagrange_interpolate_prepare`) [type-only:
/// `Vec` resize → fixed `[u16;37]` written at `[0..n+1]`; `debug_assert` dropped].
fn prepare(xs: [u16; 36], n: usize) -> [u16; 37] {
    let mut p = [0u16; 37];
    let offset = n;
    p[offset] = 1; // GF16::ONE in the highest slot
    let mut i = 0;
    while i < offset {
        p = mult_xdiff_trailing(p, n + 1, offset - i, xs[i]);
        i += 1;
    }
    p
}

/// From `PRODUCT(x - xj)` (the `n+1`-coefficient prepared poly), produce `x ·` the
/// Lagrange basis poly for point `i`: divide out `(x - xi)` by long division and
/// scale by `yi / PRODUCT_{j≠i}(xi - xj)`. Mirrors `Poly::lagrange_interpolate_complete`.
///
/// XREF: spqr polynomial.rs:197-224 @f2589fe (`lagrange_interpolate_complete`) [type-only:
/// `Vec` → `[u16;37]`; `pi.x - pj.x` and `+=` are XOR; `continue` → negated guard;
/// `debug_assert` dropped]. Requires `i < n`.
fn complete(coeffs: [u16; 37], xs: [u16; 36], ys: [u16; 36], n: usize, i: usize) -> [u16; 37] {
    let mut out = coeffs;
    let pix = xs[i];
    let piy = ys[i];
    // Scaling factor: PRODUCT_{j≠i} (xi - xj).
    let mut denominator: u16 = 1;
    let mut j = 0;
    while j < n {
        if pix != xs[j] {
            denominator = gf_mul(denominator, gf_add(pix, xs[j]));
        }
        j += 1;
    }
    let scale = gf_div(piy, denominator);
    // Long-divide by (x - xi) and scale, from the top coefficient down.
    let len = n + 1;
    let mut j2 = 1;
    while j2 < len {
        let idx = len - j2;
        let negative_delta = gf_mul(out[idx], pix);
        out[idx] = gf_mul(out[idx], scale);
        out[idx - 1] = gf_add(out[idx - 1], negative_delta);
        j2 += 1;
    }
    out
}

/// Interpolate the polynomial through `(xs[k], ys[k])` for `k < n` (distinct x's),
/// returning its `n` little-endian coefficients. Mirrors `Poly::lagrange_interpolate`
/// — including the unrolled first iteration and the "divide by x" coefficient-skip
/// (`out[j] += working[j+1]`) that the upstream representation forces.
///
/// XREF: spqr polynomial.rs:106-137 @f2589fe (`lagrange_interpolate`) [type-only:
/// `Vec` ops (`extend_from_slice`, `copy_from_slice`) → fixed `[u16;37]` index loops].
/// Requires `n <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`.
pub fn lagrange_interpolate(xs: [u16; 36], ys: [u16; 36], n: usize) -> [u16; 37] {
    let mut out = [0u16; 37];
    if n == 0 {
        return out;
    }
    let template = prepare(xs, n);
    // Unroll the first iteration; `working` is `x · <basis poly>`, so we take [1..].
    let mut working = complete(template, xs, ys, n, 0);
    let mut k = 0;
    while k < n {
        out[k] = working[k + 1];
        k += 1;
    }
    let mut i = 1;
    while i < n {
        working = complete(template, xs, ys, n, i);
        // "divide by x" by skipping the lowest coefficient as we accumulate.
        let mut j = 0;
        while j < n {
            out[j] = gf_add(out[j], working[j + 1]);
            j += 1;
        }
        i += 1;
    }
    out
}

/// Evaluate the `len`-coefficient polynomial at `x` via the x-power table
/// (`powers[i] = powers[i/2] · powers[i/2 + i%2]`), then the coefficient dot
/// product. Mirrors `Poly::compute_at`.
///
/// XREF: spqr polynomial.rs:255-272 @f2589fe (`Poly::compute_at`, `#[opaque] // zip`)
/// [type-only: `Vec` power table → `[u16;37]`; the final `coefficients.zip(xs)` →
/// indexed loop]. Same field value. Requires `len <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1`.
pub fn compute_at(coeffs: [u16; 37], len: usize, x: u16) -> u16 {
    let mut powers = [0u16; 37];
    powers[0] = 1; // x^0
    powers[1] = x; // x^1 (the unconditional second push; unused when len < 2)
    let mut i = 2;
    while i < len {
        let a = powers[i / 2];
        let b = powers[(i / 2) + (i % 2)];
        powers[i] = gf_mul(a, b);
        i += 1;
    }
    let mut out: u16 = 0;
    let mut k = 0;
    while k < len {
        out = gf_add(out, gf_mul(coeffs[k], powers[k]));
        k += 1;
    }
    out
}

/// Recover the value at index `x` of a message polynomial known through the `n`
/// points `(xs[k], ys[k])`: interpolate, then evaluate. This is the per-value core
/// of `PolyDecoder::decoded_message` (interpolate the sub-polynomial, then
/// `compute_at` the missing index); the 16-way striping / SortedSet / caching
/// orchestration around it is out of the fragment.
///
/// XREF: spqr polynomial.rs:919-930 @f2589fe (`decoded_message`, the
/// `lagrange_interpolate(…).compute_at(pt.x)` recovery step) [type-only].
/// Requires `n <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`.
pub fn decode_value_at(xs: [u16; 36], ys: [u16; 36], n: usize, x: u16) -> u16 {
    let poly = lagrange_interpolate(xs, ys, n);
    compute_at(poly, n, x)
}
