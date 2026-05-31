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

end Spqr.Gf
