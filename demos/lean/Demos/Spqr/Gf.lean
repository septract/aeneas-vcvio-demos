/-
  SPQR node — value adequacy of the extracted GF(2¹⁶) field arithmetic.

  `gf.rs` is the Aeneas extraction of Signal's Reed–Solomon field arithmetic over
  GF(2¹⁶) (the erasure-code substrate of the Sparse Post-Quantum Ratchet), in the
  portable form Signal's own hax/F\* build verifies. The genuine content is the
  carryless multiply `poly_mul` and the table-driven reduction `poly_reduce`; their
  composition `gf_mul` is the field multiply. This is the SPQR analog of the
  ratchet demo's ChaCha node: real arithmetic, so the value-adequacy obligation is
  **totality** — the extracted code never panics, overflows, or diverges, hence it
  denotes an honest pure function on `u16`.

  We prove totality of every arithmetic entry point (`gf_add`, `poly_mul`,
  `poly_reduce`, `gf_mul`, `gf_div`) and pin `gf_add` to XOR. Algebraic field laws
  (associativity, distributivity, reduction-correctness against `Spec.GF16`) are a
  separate, heavier obligation, out of scope for this node — we certify the
  extraction is a total function, the ε = 0 lifting premise.
-/
import Demos.Extracted.Gf

open Aeneas Std Result

namespace Spqr.Gf

/-- Masking by `0xFF` keeps a `usize` below 256 — taught to `scalar_tac` so the
`poly_reduce` table-index bounds (`(v >>> 16) & 0xFF < 256`) discharge automatically. -/
@[scalar_tac (x &&& 255#usize).val]
theorem and255_le (x : Std.Usize) : (x &&& 255#usize).val ≤ 255 := by
  simp only [UScalar.val_and]; exact Nat.and_le_right

/-- Field addition: total, and exactly bitwise XOR. Mirrors `GF16::AddAssign`
(`self.value ^= other.value`) — characteristic-2 addition. -/
theorem gf_add_total (a b : Std.U16) : gf.gf_add a b ⦃ r => r = a ^^^ b ⦄ := by
  unfold gf.gf_add
  step*

/-- Cheap totality of field addition, registered for `step*` (the value-carrying
characterization `gf_add_total` is too expensive to thread through array updates). -/
@[step]
theorem gf_add_ok (a b : Std.U16) : gf.gf_add a b ⦃ fun _ => True ⦄ := by
  unfold gf.gf_add
  step*

/-- The carryless-multiply loop never fails: shifts by `shift < 16` (in range for
`u16`/`u32`) and an XOR accumulate; `shift` rises to 16. Loop state is `(acc, shift)`. -/
theorem poly_mul_loop_ok (b : Std.U16) (me : Std.U32) :
    ∀ (acc shift : Std.U32), shift.val ≤ 16 →
      gf.poly_mul_loop b acc me shift ⦃ fun _ => True ⦄ := by
  intro acc shift hs
  unfold gf.poly_mul_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U32 × Std.U32 => 16 - s.2.val)
    (inv := fun s : Std.U32 × Std.U32 => s.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨acc1, shift1⟩ hinv
    simp only [gf.poly_mul_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨i1, hi1⟩
      split
      · step as ⟨i2, hi2⟩
        step as ⟨shift2, hshift2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
      · step as ⟨shift2, hshift2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hs

/-- `poly_mul` is total: the carryless product of two field elements always exists. -/
@[step]
theorem poly_mul_total (a b : Std.U16) : gf.poly_mul a b ⦃ fun _ => True ⦄ := by
  unfold gf.poly_mul
  step as ⟨me, hme⟩
  apply poly_mul_loop_ok
  scalar_tac

/-- `reduce_from_byte`'s loop never fails: shifts by `i-1 < 8` and XOR/cast; `i` falls to 0.
Loop state is `(a, out, i)`. -/
theorem reduce_from_byte_loop_ok :
    ∀ (a : Std.U8) (out i : Std.U32), i.val ≤ 8 →
      gf.reduce_from_byte_loop a out i ⦃ fun _ => True ⦄ := by
  intro a out i hi
  unfold gf.reduce_from_byte_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.U32 × Std.U32 => s.2.2.val)
    (inv := fun s : Std.U8 × Std.U32 × Std.U32 => s.2.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨a1, out1, i1⟩ hinv
    simp only [gf.reduce_from_byte_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      split
      · step as ⟨i5, hi5⟩
        step as ⟨i6, hi6⟩
        step as ⟨i7, hi7⟩
        step as ⟨a2, ha2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
      · refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hi

@[step]
theorem reduce_from_byte_total (a : Std.U8) : gf.reduce_from_byte a ⦃ fun _ => True ⦄ := by
  unfold gf.reduce_from_byte
  apply reduce_from_byte_loop_ok
  scalar_tac

/-- Building the 256-entry reduction table never fails (each entry is a total
`reduce_from_byte`; `i` rises to 256, the array length). Loop state is `(out, i)`. -/
theorem reduce_bytes_loop_ok :
    ∀ (out : Array Std.U16 256#usize) (i : Std.Usize), i.val ≤ 256 →
      gf.reduce_bytes_loop out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.reduce_bytes_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 256#usize) × Std.Usize => 256 - s.2.val)
    (inv := fun s : (Array Std.U16 256#usize) × Std.Usize => s.2.val ≤ 256)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.reduce_bytes_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨o2, ho2⟩
      step as ⟨i5, hi5⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hi

@[step]
theorem reduce_bytes_total : gf.reduce_bytes ⦃ fun _ => True ⦄ := by
  unfold gf.reduce_bytes
  apply reduce_bytes_loop_ok
  scalar_tac

/-- **Value adequacy of the reduction.** `poly_reduce` is total: the two table folds
index `[u16; 256]` at `(v >>> 24)` and `(v >>> 16) & 0xFF`, both `< 256`, so neither
read is out of bounds and the function denotes a total `u32 → u16`. -/
@[step]
theorem poly_reduce_total (v : Std.U32) : gf.poly_reduce v ⦃ fun _ => True ⦄ := by
  unfold gf.poly_reduce
  -- `step*` advances the straight-line body, leaving the two table-index bounds.
  step*
  · -- first index: `(v >>> 24) < 256`.
    scalar_tac
  · -- second index: `((v >>> 16) & 0xFF) < 256`, from masking with `0xFF`.
    have key : (shifted_v &&& 255#usize).val ≤ 255 := and255_le shifted_v
    scalar_tac

/-- **Value adequacy of the field multiply.** `gf_mul = poly_reduce ∘ poly_mul` is
total — the headline ε = 0 lifting obligation for the SPQR field arithmetic. -/
@[step]
theorem gf_mul_total (a b : Std.U16) : gf.gf_mul a b ⦃ fun _ => True ⦄ := by
  unfold gf.gf_mul
  step*

/-- The Fermat-inverse division ladder is total: 15 iterations of the (total) field
multiply. Mirrors `GF16::const_div` (`a / b = a · b^(2¹⁶-2)`). Loop state `(sq, out, i)`. -/
@[step]
theorem gf_div_total (numer denom : Std.U16) : gf.gf_div numer denom ⦃ fun _ => True ⦄ := by
  unfold gf.gf_div
  unfold gf.gf_div_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.U16 × Std.Usize => 16 - s.2.2.val)
    (inv := fun s : Std.U16 × Std.U16 × Std.Usize => s.2.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨sq, out, i⟩ hinv
    simp only [gf.gf_div_loop.body]
    split
    · rename_i hlt
      step as ⟨sq1, hsq1⟩
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · scalar_tac

/-! ### Polynomial arithmetic over GF(2¹⁶) (the codec's field core) -/

/-- Horner evaluation never fails: `deg ≤ 36` keeps every coefficient read
`coeffs[i-1]` (`i ≤ deg`) in bounds, and each step is a (total) field mul + add. -/
@[step]
theorem poly_eval_loop_ok (coeffs : Array Std.U16 36#usize) (x : Std.U16) :
    ∀ (out : Std.U16) (i : Std.Usize), i.val ≤ 36 →
      gf.poly_eval_loop coeffs x out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.poly_eval_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => s.2.val)
    (inv := fun s : Std.U16 × Std.Usize => s.2.val ≤ 36)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.poly_eval_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of polynomial evaluation.** `poly_eval` is total for degree
`≤ 36` (`MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1`) — the encoder's chunk-generation core. -/
theorem poly_eval_total (coeffs : Array Std.U16 36#usize) (deg : Std.Usize) (x : Std.U16) :
    deg.val ≤ 36 → gf.poly_eval coeffs deg x ⦃ fun _ => True ⦄ := by
  intro hdeg
  unfold gf.poly_eval
  apply poly_eval_loop_ok; exact hdeg

/-- Pointwise polynomial addition never fails. -/
theorem poly_add_loop_ok (a b : Array Std.U16 36#usize) :
    ∀ (out : Array Std.U16 36#usize) (i : Std.Usize), i.val ≤ 36 →
      gf.poly_add_loop a b out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.poly_add_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 36#usize) × Std.Usize => 36 - s.2.val)
    (inv := fun s : (Array Std.U16 36#usize) × Std.Usize => s.2.val ≤ 36)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.poly_add_loop.body, gf.POLY_COEFFS]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of polynomial addition** (`Poly::add_assign`). -/
theorem poly_add_total (a b : Array Std.U16 36#usize) :
    gf.poly_add a b ⦃ fun _ => True ⦄ := by
  unfold gf.poly_add
  apply poly_add_loop_ok; scalar_tac

/-- Scalar polynomial multiply never fails. -/
theorem poly_scale_loop_ok (a : Array Std.U16 36#usize) (m : Std.U16) :
    ∀ (out : Array Std.U16 36#usize) (i : Std.Usize), i.val ≤ 36 →
      gf.poly_scale_loop a m out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.poly_scale_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 36#usize) × Std.Usize => 36 - s.2.val)
    (inv := fun s : (Array Std.U16 36#usize) × Std.Usize => s.2.val ≤ 36)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.poly_scale_loop.body, gf.POLY_COEFFS]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of scalar polynomial multiply** (`Poly::mult_assign`). -/
theorem poly_scale_total (a : Array Std.U16 36#usize) (m : Std.U16) :
    gf.poly_scale a m ⦃ fun _ => True ⦄ := by
  unfold gf.poly_scale
  apply poly_scale_loop_ok; scalar_tac

/-! ### Lagrange-interpolation decoder (the codec's Reed–Solomon reconstruction core)

The decoder rebuilds a message polynomial from its sampled points and evaluates it at
the missing indices. Every coefficient array is `[u16; 37]` (the V1 bound
`MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1`); the value-adequacy obligation is totality
under the single inherited precondition `n ≤ 36`. -/

/-- `mult_xdiff_trailing`'s loop never fails: it reads `out[i]` (`i < len ≤ 37`) and
writes `out[i-1]` (so `i ≥ 1` throughout), with `i` rising to `len`. -/
theorem mult_xdiff_trailing_loop_ok (len : Std.Usize) (difference : Std.U16)
    (hlen : len.val ≤ 37) :
    ∀ (out : Array Std.U16 37#usize) (i : Std.Usize), 1 ≤ i.val →
      gf.mult_xdiff_trailing_loop len difference out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.mult_xdiff_trailing_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize => 1 ≤ s.2.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.mult_xdiff_trailing_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨delta, hdelta⟩
      step as ⟨i2, hi2⟩
      step as ⟨v3, hv3⟩
      step as ⟨v4, hv4⟩
      step as ⟨a, ha⟩
      step as ⟨i5, hi5⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hi

/-- `mult_xdiff_trailing` is total for `len ≤ 37` and `start ≥ 1`. -/
@[step]
theorem mult_xdiff_trailing_total (coeffs : Array Std.U16 37#usize) (len start : Std.Usize)
    (difference : Std.U16) (hlen : len.val ≤ 37) (hstart : 1 ≤ start.val) :
    gf.mult_xdiff_trailing coeffs len start difference ⦃ fun _ => True ⦄ := by
  unfold gf.mult_xdiff_trailing
  exact mult_xdiff_trailing_loop_ok len difference hlen coeffs start hstart

/-- `prepare`'s loop never fails: each step calls the (total) `mult_xdiff_trailing` with
`len = n+1 ≤ 37` and `start = n-i ≥ 1` (since `i < n`), reading `xs[i]` (`i < n ≤ 36`). -/
@[step]
theorem prepare_loop_ok (xs : Array Std.U16 36#usize) (n : Std.Usize) (hn : n.val ≤ 36) :
    ∀ (p : Array Std.U16 37#usize) (i : Std.Usize),
      gf.prepare_loop xs n p i ⦃ fun _ => True ⦄ := by
  intro p i
  unfold gf.prepare_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun _ : (Array Std.U16 37#usize) × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨p1, i1⟩ _
    simp only [gf.prepare_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- **Value adequacy of `prepare`** (`PRODUCT(x - xj)`): total for `n ≤ 36`. -/
@[step]
theorem prepare_total (xs : Array Std.U16 36#usize) (n : Std.Usize) (hn : n.val ≤ 36) :
    gf.prepare xs n ⦃ fun _ => True ⦄ := by
  unfold gf.prepare
  step*

/-- The denominator loop in `complete` never fails: reads `xs[j]` (`j < n ≤ 36`), field
mul/add only. -/
@[step]
theorem complete_loop0_ok (xs : Array Std.U16 36#usize) (n : Std.Usize) (pix : Std.U16)
    (hn : n.val ≤ 36) :
    ∀ (denominator : Std.U16) (j : Std.Usize),
      gf.complete_loop0 xs n pix denominator j ⦃ fun _ => True ⦄ := by
  intro denominator j
  unfold gf.complete_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => n.val - s.2.val)
    (inv := fun _ : Std.U16 × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨d1, j1⟩ _
    simp only [gf.complete_loop0.body]
    split
    · rename_i hlt
      step as ⟨xj, hxj⟩
      split
      · step as ⟨s1, hs1⟩
        step as ⟨d2, hd2⟩
        step as ⟨j2, hj2⟩
        scalar_tac
      · step as ⟨j2, hj2⟩
        scalar_tac
    · trivial
  · trivial

/-- The long-division loop in `complete` never fails: `idx = len - j2 ∈ [1, len-1] ⊆ [1, 36]`
(since `1 ≤ j2 < len ≤ 37`), so `out[idx]` and `out[idx-1]` are in bounds. -/
@[step]
theorem complete_loop1_ok (pix scale : Std.U16) (len : Std.Usize) (hlen : len.val ≤ 37) :
    ∀ (out : Array Std.U16 37#usize) (j2 : Std.Usize), 1 ≤ j2.val →
      gf.complete_loop1 out pix scale len j2 ⦃ fun _ => True ⦄ := by
  intro out j2 hj2
  unfold gf.complete_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize => 1 ≤ s.2.val)
    (post := fun _ => True)
  · rintro ⟨o1, j21⟩ hinv
    simp only [gf.complete_loop1.body]
    split
    · rename_i hlt
      step as ⟨idx, hidx⟩
      step as ⟨vi, hvi⟩
      step as ⟨nd, hnd⟩
      step as ⟨i1, hi1⟩
      step as ⟨out1, hout1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨a, ha⟩
      step as ⟨j22, hj22⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hj2

/-- **Value adequacy of `complete`**: total for `n ≤ 36` and `i < n`. -/
@[step]
theorem complete_total (coeffs : Array Std.U16 37#usize) (xs ys : Array Std.U16 36#usize)
    (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val) :
    gf.complete coeffs xs ys n i ⦃ fun _ => True ⦄ := by
  unfold gf.complete
  step*

/-- The first (unrolled-tail copy) loop of `lagrange_interpolate` never fails:
`out[k] = working[k+1]`, `k < n ≤ 36` so `k+1 ≤ 36 < 37`. -/
@[step]
theorem lagrange_interpolate_loop0_ok (n : Std.Usize) (working : Array Std.U16 37#usize)
    (hn : n.val ≤ 36) :
    ∀ (out : Array Std.U16 37#usize) (k : Std.Usize),
      gf.lagrange_interpolate_loop0 n out working k ⦃ fun _ => True ⦄ := by
  intro out k
  unfold gf.lagrange_interpolate_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun _ : (Array Std.U16 37#usize) × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨o1, k1⟩ _
    simp only [gf.lagrange_interpolate_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- The inner accumulate loop never fails: `out[j] += working[j+1]`, `j < n ≤ 36`. -/
@[step]
theorem lagrange_interpolate_loop1_loop0_ok (n : Std.Usize) (working : Array Std.U16 37#usize)
    (hn : n.val ≤ 36) :
    ∀ (out : Array Std.U16 37#usize) (j : Std.Usize),
      gf.lagrange_interpolate_loop1_loop0 n out working j ⦃ fun _ => True ⦄ := by
  intro out j
  unfold gf.lagrange_interpolate_loop1_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun _ : (Array Std.U16 37#usize) × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ _
    simp only [gf.lagrange_interpolate_loop1_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- The outer interpolation loop never fails: each step is a (total) `complete` (with
`i < n`) and the inner accumulate loop. -/
@[step]
theorem lagrange_interpolate_loop1_ok (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (template : Array Std.U16 37#usize) (hn : n.val ≤ 36) :
    ∀ (out working : Array Std.U16 37#usize) (i : Std.Usize),
      gf.lagrange_interpolate_loop1 xs ys n out template working i ⦃ fun _ => True ⦄ := by
  intro out working i
  unfold gf.lagrange_interpolate_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × (Array Std.U16 37#usize) × Std.Usize =>
      n.val - s.2.2.val)
    (inv := fun _ : (Array Std.U16 37#usize) × (Array Std.U16 37#usize) × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨o1, w1, i1⟩ _
    simp only [gf.lagrange_interpolate_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- **Value adequacy of `lagrange_interpolate`**: total for `n ≤ 36`. -/
@[step]
theorem lagrange_interpolate_total (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (hn : n.val ≤ 36) :
    gf.lagrange_interpolate xs ys n ⦃ fun _ => True ⦄ := by
  unfold gf.lagrange_interpolate
  split
  · trivial
  · rename_i hn0
    have hpos : 0 < n.val := by scalar_tac
    step*

/-- The x-power-table loop never fails: `powers[i] = powers[i/2]·powers[i/2 + i%2]`,
all indices `< len ≤ 37`. -/
@[step]
theorem compute_at_loop0_ok (len : Std.Usize) (hlen : len.val ≤ 37) :
    ∀ (powers : Array Std.U16 37#usize) (i : Std.Usize),
      gf.compute_at_loop0 len powers i ⦃ fun _ => True ⦄ := by
  intro powers i
  unfold gf.compute_at_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun _ : (Array Std.U16 37#usize) × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨p1, i1⟩ _
    simp only [gf.compute_at_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- The coefficient dot-product loop never fails: reads `coeffs[k]`, `powers[k]`,
`k < len ≤ 37`. -/
@[step]
theorem compute_at_loop1_ok (coeffs : Array Std.U16 37#usize) (len : Std.Usize)
    (powers : Array Std.U16 37#usize) (hlen : len.val ≤ 37) :
    ∀ (out : Std.U16) (k : Std.Usize),
      gf.compute_at_loop1 coeffs len powers out k ⦃ fun _ => True ⦄ := by
  intro out k
  unfold gf.compute_at_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => len.val - s.2.val)
    (inv := fun _ : Std.U16 × Std.Usize => True)
    (post := fun _ => True)
  · rintro ⟨o1, k1⟩ _
    simp only [gf.compute_at_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · trivial

/-- **Value adequacy of `compute_at`**: total for `len ≤ 37`. -/
@[step]
theorem compute_at_total (coeffs : Array Std.U16 37#usize) (len : Std.Usize) (x : Std.U16)
    (hlen : len.val ≤ 37) :
    gf.compute_at coeffs len x ⦃ fun _ => True ⦄ := by
  unfold gf.compute_at
  step*

/-- **Value adequacy of the decoder.** `decode_value_at` is total for `n ≤ 36`: interpolate
the message polynomial through its `n` known points, then evaluate at the missing index. This
certifies *totality* of the Reed–Solomon reconstruction kernel only — the algebraic
`decode ∘ encode = id` round-trip identity that the SCKA correctness argument ultimately needs
is a separate, heavier obligation (not proved here, future work). -/
theorem decode_value_at_total (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    (hn : n.val ≤ 36) :
    gf.decode_value_at xs ys n x ⦃ fun _ => True ⦄ := by
  unfold gf.decode_value_at
  step*

/-! ### Algebraic content: pure field operations and the Horner-fold value spec

The totality results above certify the extracted code denotes total `u16` functions. The next
layer of the Reed–Solomon correctness story is *algebraic*: characterizing **what value** the
extracted loops compute, as explicit recurrences over the field operations. The genuinely deep
endpoint (`decode ∘ encode = id`) additionally needs the GF(2¹⁶) field laws (associativity,
distributivity, inverses — exactly what Signal proves against `Spec.GF16` in F\*, and which the
header of this file flags as a separate, heavier obligation). Here we bank the algebraic *value
specs* that do **not** require those field laws: the extracted field multiply is a deterministic
pure function (`gfMulV`), and `poly_eval` is **exactly** the Horner fold over it. -/

/-- The extracted field multiply, read as a pure `u16 → u16 → u16` (the value of the
`Result`, or `0#u16` on the never-taken failure branch). -/
def gfMulV (a b : Std.U16) : Std.U16 :=
  match gf.gf_mul a b with
  | .ok c => c
  | _ => 0#u16

/-- The extracted field add is XOR (proved as `gf_add_total`); its pure value is `a ^^^ b`. -/
def gfAddV (a b : Std.U16) : Std.U16 := a ^^^ b

/-- **Value spec of the field multiply.** `gf_mul a b` succeeds with value `gfMulV a b` — so the
extracted carryless-multiply-then-reduce denotes the pure binary operation `gfMulV`. -/
theorem gf_mul_eq (a b : Std.U16) : gf.gf_mul a b = .ok (gfMulV a b) := by
  have := gf_mul_total a b
  unfold gfMulV
  cases h : gf.gf_mul a b with
  | ok c => rfl
  | div => simp [h] at this
  | fail e => simp [h] at this

/-- **Value spec of the field add.** `gf_add a b` succeeds with value `gfAddV a b = a ^^^ b`. -/
theorem gf_add_eq (a b : Std.U16) : gf.gf_add a b = .ok (gfAddV a b) := by
  unfold gf.gf_add gfAddV; rfl

/-- The Horner accumulator the encoder's evaluation loop computes. Mirrors `poly_eval_loop`
*exactly*: started at accumulator `acc` and index `i`, each step folds in one more coefficient
from the top, `acc ↦ gfAddV (gfMulV acc x) coeffs[i-1]`, decrementing `i`. -/
def hornerV (coeffs : Array Std.U16 36#usize) (x : Std.U16) : Std.U16 → Nat → Std.U16
  | acc, 0 => acc
  | acc, (i + 1) => hornerV coeffs x (gfAddV (gfMulV acc x) coeffs.val[i]!) i

/-- **Horner value spec of the evaluation loop.** `poly_eval_loop` computes exactly the pure
Horner fold `hornerV`: started from accumulator `out` and index `i` (`i ≤ 36`), it returns
`hornerV coeffs x out i.val`. -/
theorem poly_eval_loop_eq (coeffs : Array Std.U16 36#usize) (x : Std.U16) :
    ∀ (out : Std.U16) (i : Std.Usize), i.val ≤ 36 →
      gf.poly_eval_loop coeffs x out i ⦃ r => r = hornerV coeffs x out i.val ⦄ := by
  intro out i hi
  unfold gf.poly_eval_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => s.2.val)
    (inv := fun s : Std.U16 × Std.Usize =>
      s.2.val ≤ 36 ∧ hornerV coeffs x s.1 s.2.val = hornerV coeffs x out i.val)
    (post := fun r : Std.U16 => r = hornerV coeffs x out i.val)
  · rintro ⟨o1, i1⟩ ⟨hi1, hinv⟩
    simp only [gf.poly_eval_loop.body]
    split
    · rename_i hlt
      -- The loop step folds in one coefficient: rewrite its `gf_mul`/`gf_add` to the pure
      -- `gfMulV`/`gfAddV`, then recognise the result as one `hornerV` unfolding (`i1 = i2 + 1`).
      rw [gf_mul_eq]
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      rw [gf_add_eq]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      simp only [hinv.symm]
      have he : i1.val = i2.val + 1 := by scalar_tac
      conv_rhs => rw [he, hornerV]
      rw [hi3]
    · rename_i hge
      -- `i1 = 0`, so the loop returns its accumulator `o1`, which `hinv` ties back to the start.
      have h0 : i1.val = 0 := by scalar_tac
      simp only [h0, hornerV] at hinv
      exact hinv
  · exact ⟨hi, rfl⟩

/-- **Horner value spec of `poly_eval` (the encoder's evaluation core).** For degree `deg ≤ 36`,
`poly_eval coeffs deg x` succeeds with value `hornerV coeffs x 0 deg` — i.e. it computes exactly
the Horner fold of `coeffs[0..deg)` at `x`, the algebraic content behind the totality result
`poly_eval_total`. This is the value-level characterization the `decode ∘ encode = id` round-trip
ultimately builds on (the remaining step — that this fold equals `Σ coeffs[i]·x^i` and inverts
Lagrange interpolation — additionally needs the GF(2¹⁶) field laws, separate future work). -/
theorem poly_eval_eq (coeffs : Array Std.U16 36#usize) (deg : Std.Usize) (x : Std.U16)
    (hdeg : deg.val ≤ 36) :
    gf.poly_eval coeffs deg x ⦃ r => r = hornerV coeffs x 0#u16 deg.val ⦄ := by
  unfold gf.poly_eval
  exact poly_eval_loop_eq coeffs x 0#u16 deg hdeg

/-! ### Pointwise value specs: polynomial add and scalar multiply -/

/-- `poly_add_loop` fills `out[k] = a[k] ^^^ b[k]` for `k < 36`, preserving entries already set. -/
theorem poly_add_loop_eq (a b : Array Std.U16 36#usize) :
    ∀ (out : Array Std.U16 36#usize) (i : Std.Usize), i.val ≤ 36 →
      (∀ k, k < i.val → out.val[k]! = a.val[k]! ^^^ b.val[k]!) →
      gf.poly_add_loop a b out i
        ⦃ r => ∀ k, k < 36 → r.val[k]! = a.val[k]! ^^^ b.val[k]! ⦄ := by
  intro out i hi hpre
  unfold gf.poly_add_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 36#usize) × Std.Usize => 36 - s.2.val)
    (inv := fun s : (Array Std.U16 36#usize) × Std.Usize =>
      s.2.val ≤ 36 ∧ (∀ k, k < s.2.val → s.1.val[k]! = a.val[k]! ^^^ b.val[k]!))
    (post := fun r : Array Std.U16 36#usize =>
      ∀ k, k < 36 → r.val[k]! = a.val[k]! ^^^ b.val[k]!)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [gf.poly_add_loop.body, gf.POLY_COEFFS]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      rw [gf_add_eq]
      step as ⟨o2, ho2⟩
      step as ⟨i4, hi4⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk
      subst ho2
      by_cases hke : k = i1.val
      · subst hke; simp_lists [hv1, hv2]; unfold gfAddV; rfl
      · have : k < i1.val := by scalar_tac
        simp_lists; exact hpre1 k this
    · rename_i hge
      intro k hk; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-- **Pointwise value spec of `poly_add`** (`Poly::add_assign`): coefficient `k` of the result is
`a[k] ^^^ b[k]` — characteristic-2 polynomial addition. -/
theorem poly_add_eq (a b : Array Std.U16 36#usize) :
    gf.poly_add a b ⦃ r => ∀ k, k < 36 → r.val[k]! = a.val[k]! ^^^ b.val[k]! ⦄ := by
  unfold gf.poly_add
  apply poly_add_loop_eq a b _ 0#usize (by scalar_tac)
  intro k hk; scalar_tac

/-- `poly_scale_loop` fills `out[k] = gfMulV a[k] m` for `k < 36`. -/
theorem poly_scale_loop_eq (a : Array Std.U16 36#usize) (m : Std.U16) :
    ∀ (out : Array Std.U16 36#usize) (i : Std.Usize), i.val ≤ 36 →
      (∀ k, k < i.val → out.val[k]! = gfMulV a.val[k]! m) →
      gf.poly_scale_loop a m out i
        ⦃ r => ∀ k, k < 36 → r.val[k]! = gfMulV a.val[k]! m ⦄ := by
  intro out i hi hpre
  unfold gf.poly_scale_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 36#usize) × Std.Usize => 36 - s.2.val)
    (inv := fun s : (Array Std.U16 36#usize) × Std.Usize =>
      s.2.val ≤ 36 ∧ (∀ k, k < s.2.val → s.1.val[k]! = gfMulV a.val[k]! m))
    (post := fun r : Array Std.U16 36#usize =>
      ∀ k, k < 36 → r.val[k]! = gfMulV a.val[k]! m)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [gf.poly_scale_loop.body, gf.POLY_COEFFS]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      rw [gf_mul_eq]
      step as ⟨o2, ho2⟩
      step as ⟨i4, hi4⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk
      subst ho2
      by_cases hke : k = i1.val
      · subst hke; simp_lists [hv1]
      · have : k < i1.val := by scalar_tac
        simp_lists; exact hpre1 k this
    · rename_i hge
      intro k hk; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-- **Pointwise value spec of `poly_scale`** (`Poly::mult_assign`): coefficient `k` of the result
is the field product `gfMulV a[k] m`. -/
theorem poly_scale_eq (a : Array Std.U16 36#usize) (m : Std.U16) :
    gf.poly_scale a m ⦃ r => ∀ k, k < 36 → r.val[k]! = gfMulV a.val[k]! m ⦄ := by
  unfold gf.poly_scale
  apply poly_scale_loop_eq a m _ 0#usize (by scalar_tac)
  intro k hk; scalar_tac

/-! ### Value spec of `mult_xdiff_trailing` (multiply a trailing sub-polynomial by `(x - c)`)

`mult_xdiff_trailing coeffs len start difference` carries one step of polynomial multiplication by
`(x - difference)`: over the window `start-1 ≤ j < len-1` it sets coefficient `j` to
`coeffs[j] ⊕ difference · coeffs[j+1]` (the carry of the higher coefficient into the lower one,
characteristic-2), leaving all coefficients outside the window unchanged. Because every write
targets index `j-1 < j` while every read targets `j ≥ start`, the reads always see the *original*
`coeffs` values — the spec is therefore a clean closed form over `coeffs`, not the running array. -/

/-- The window-update closed form computed by `mult_xdiff_trailing`. -/
def xdiffStep (coeffs : Array Std.U16 37#usize) (len start : Std.Usize) (difference : Std.U16)
    (j : Nat) : Std.U16 :=
  if start.val - 1 ≤ j ∧ j < len.val - 1 then
    coeffs.val[j]! ^^^ gfMulV coeffs.val[j + 1]! difference
  else coeffs.val[j]!

theorem mult_xdiff_trailing_loop_eq (coeffs : Array Std.U16 37#usize) (len start : Std.Usize)
    (difference : Std.U16) (hlen : len.val ≤ 37) (hstart : 1 ≤ start.val) :
    ∀ (out : Array Std.U16 37#usize) (i : Std.Usize), start.val ≤ i.val → i.val ≤ len.val →
      -- updated region [start-1, i-1); everything else still equals `coeffs`
      (∀ j, j < 37 →
        out.val[j]! = if start.val - 1 ≤ j ∧ j < i.val - 1 then
          coeffs.val[j]! ^^^ gfMulV coeffs.val[j + 1]! difference else coeffs.val[j]!) →
      gf.mult_xdiff_trailing_loop len difference out i
        ⦃ r => ∀ j, j < 37 → r.val[j]! = xdiffStep coeffs len start difference j ⦄ := by
  intro out i hsi hil hinv
  unfold gf.mult_xdiff_trailing_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      start.val ≤ s.2.val ∧ s.2.val ≤ len.val ∧
      (∀ j, j < 37 →
        s.1.val[j]! = if start.val - 1 ≤ j ∧ j < s.2.val - 1 then
          coeffs.val[j]! ^^^ gfMulV coeffs.val[j + 1]! difference else coeffs.val[j]!))
    (post := fun r : Array Std.U16 37#usize =>
      ∀ j, j < 37 → r.val[j]! = xdiffStep coeffs len start difference j)
  · rintro ⟨o1, i1⟩ ⟨hsi1, hil1, hinv1⟩
    simp only [gf.mult_xdiff_trailing_loop.body]
    split
    · rename_i hlt
      -- read o1[i1] = coeffs[i1] (i1 ≥ i1-1, original region)
      step as ⟨v1, hv1⟩
      rw [gf_mul_eq]
      step as ⟨delta, hdelta⟩
      step as ⟨i3, hi3⟩
      rw [gf_add_eq]
      step as ⟨o2, ho2⟩
      step as ⟨i5, hi5⟩
      have hv1c : v1 = coeffs.val[i1.val]! := by
        rw [hv1, hinv1 i1.val (by scalar_tac)]
        rw [if_neg (by scalar_tac)]
      have hi3c : i3 = coeffs.val[i1.val - 1]! := by
        rw [hi3, hdelta, hinv1 (i1.val - 1) (by scalar_tac)]
        rw [if_neg (by scalar_tac)]
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      subst ho2
      by_cases hje : j = delta.val
      · subst hje
        simp_lists
        rw [gfAddV, hi3c, hv1c, hdelta]
        have hin : start.val - 1 ≤ i1.val - 1 ∧ i1.val - 1 < i5.val - 1 := by
          constructor <;> scalar_tac
        rw [if_pos hin]
        have he : i1.val - 1 + 1 = i1.val := by scalar_tac
        rw [he]
      · simp_lists
        rw [hinv1 j hj]
        by_cases hc : start.val - 1 ≤ j ∧ j < i1.val - 1
        · rw [if_pos hc, if_pos ⟨hc.1, by scalar_tac⟩]
        · rw [if_neg hc]
          rw [if_neg (by
            rintro ⟨h1, h2⟩
            apply hc; exact ⟨h1, by scalar_tac⟩)]
    · rename_i hge
      intro j hj
      rw [hinv1 j hj]
      unfold xdiffStep
      have : i1 = len := by scalar_tac
      subst this
      rfl
  · exact ⟨hsi, hil, hinv⟩

/-- **Value spec of `mult_xdiff_trailing`.** Over the window `start-1 ≤ j < len-1`, coefficient `j`
becomes `coeffs[j] ⊕ difference · coeffs[j+1]`; outside the window it is unchanged. This is one
step of multiplication by `(x - difference)` over GF(2¹⁶). -/
theorem mult_xdiff_trailing_eq (coeffs : Array Std.U16 37#usize) (len start : Std.Usize)
    (difference : Std.U16) (hlen : len.val ≤ 37) (hstart : 1 ≤ start.val)
    (hsl : start.val ≤ len.val) :
    gf.mult_xdiff_trailing coeffs len start difference
      ⦃ r => ∀ j, j < 37 → r.val[j]! = xdiffStep coeffs len start difference j ⦄ := by
  unfold gf.mult_xdiff_trailing
  apply mult_xdiff_trailing_loop_eq coeffs len start difference hlen hstart coeffs start
    (by scalar_tac) hsl
  intro j hj
  rw [if_neg (by rintro ⟨_, h⟩; scalar_tac)]

end Spqr.Gf
