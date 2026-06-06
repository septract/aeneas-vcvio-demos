/-
  SPQR Reed–Solomon codec — Layer B-mul (PARTIAL): the carryless-multiply half of the
  GF(2¹⁶) multiplicative bridge.

  ## What this file establishes (genuine, in-boundary)

  `gfMulV = poly_reduce ∘ poly_mul` is the value spec of the extracted field multiply
  (`gf_mul_eq`, banked in `Gf.lean`). The multiplicative half of the ring-iso
  `U16 ≅ (ZMod 2)[X]/(POLY)` decomposes along the code (`gf_mul = poly_reduce ∘ poly_mul`):

    STAGE 1 (THIS FILE): `poly_mul` is the carryless coefficient convolution. Under the
      degree-<32 bit↔coefficient embedding `toPoly32 : U32 → (ZMod 2)[X]`, the extracted
      `poly_mul a b` denotes EXACTLY the polynomial product:
        `toPoly32 (poly_mulV a b) = toPoly a * toPoly b`   (in `(ZMod 2)[X]`).
      This is proved STRUCTURALLY from the bitwise definition of the carryless multiply
      loop (XOR-accumulate `a << shift` for each set bit of `b`) matched against
      `Polynomial.coeff_mul` — no field laws, no `decide` over the value space, no axiom.

    STAGE 2 (CLOSED in `Gf16ReduceTable.lean`): `poly_reduce` is reduction mod `POLY_poly` — the
      table-fold residue-correctness. This is the deeper obligation; it is proved there as
      `Spqr.Gf16ReduceTable.stage2_proved : Stage2` (residue correctness `poly_reduce_residue`),
      unconditionally and without `decide` over the value space, `native_decide`, or any axiom.

  Composing Stage 1 with Stage 2 gives the headline `toPoly (gfMulV a b) = (toPoly a *
  toPoly b) mod POLY_poly`. This file banks Stage 1; Stage 2 is banked in `Gf16ReduceTable.lean`.
-/
import Demos.Spqr.Gf
import Demos.Spqr.Gf16Field
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff

open Aeneas Std Result
open Spqr.Gf
open Polynomial

namespace Spqr.Gf16Mul

open Spqr.Gf16Field (bitZ toPoly)

/-! ### Stage 1: the carryless multiply is the polynomial product -/

/-- The value of the extracted carryless multiply, as a pure `u16 → u16 → u32`. -/
def polyMulV (a b : Std.U16) : Std.U32 :=
  match gf.poly_mul a b with
  | .ok c => c
  | _ => 0#u32

/-- Bit `i` (LSB-indexed) of a `U32`, as an element of `ZMod 2`. -/
def bitZ32 (a : Std.U32) (i : Nat) : ZMod 2 := if a.val.testBit i then 1 else 0

/-- The degree-<32 bit↔coefficient embedding `U32 → (ZMod 2)[X]`. -/
noncomputable def toPoly32 (a : Std.U32) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 32, C (bitZ32 a i) * X ^ i

/-! ### The carryless-multiply accumulator (Nat level)

The extracted `poly_mul_loop` accumulates, for each set bit `shift < 16` of `b`, the value
`me <<< shift` into `acc` by XOR. At the Nat level this is the partial XOR-fold below; the
loop value spec (`poly_mul_loop_val`) ties the extracted `U32` accumulator to it. -/

/-- The XOR-fold the carryless multiply computes: `⊕_{shift < s, b.testBit shift} (me <<< shift)`. -/
def clmulPartial (me bv : Nat) : Nat → Nat
  | 0 => 0
  | (s + 1) => (clmulPartial me bv s) ^^^ (if bv.testBit s then me <<< s else 0)

/-- Each summand `me <<< shift` with `me < 2^16`, `shift < 16` is `< 2^32`. -/
theorem clmulPartial_lt (me bv : Nat) (hme : me < 2 ^ 16) (s : Nat) (hs : s ≤ 16) :
    clmulPartial me bv s < 2 ^ 32 := by
  induction s with
  | zero => simp [clmulPartial]
  | succ k ih =>
    have hk : k ≤ 16 := by omega
    have hk16 : k < 16 := by omega
    rw [clmulPartial]
    refine Nat.xor_lt_two_pow (ih hk) ?_
    split
    · rw [Nat.shiftLeft_eq]
      have hk2 : (2:Nat) ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc me * 2 ^ k < 2 ^ 16 * 2 ^ k :=
              Nat.mul_lt_mul_of_lt_of_le hme (Nat.le_refl _) (by positivity)
        _ ≤ 2 ^ 16 * 2 ^ 15 := by gcongr
        _ < 2 ^ 32 := by norm_num
    · positivity

/-- `b &&& 2^s ≠ 0 ↔ b.testBit s`. -/
theorem and_pow_two_ne_zero (b s : Nat) : (b &&& 2 ^ s ≠ 0) ↔ b.testBit s := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, Bool.and_eq_false_iff]
    by_cases hi : i = s
    · subst hi; left; simpa using hb
    · right; simp [Ne.symm hi]
  · intro h hz
    have hh := congrArg (Nat.testBit · s) hz
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, h, decide_true,
      Bool.true_and] at hh
    exact absurd hh (by decide)

/-- **Loop value spec for the carryless multiply.** Started at accumulator value
`acc.val = clmulPartial me.val b.val shift.val` and shift `shift`, the loop ends with the
full fold `clmulPartial me.val b.val 16`. -/
theorem poly_mul_loop_val (b : Std.U16) (me : Std.U32) (hme : me.val < 2 ^ 16) :
    ∀ (acc shift : Std.U32), shift.val ≤ 16 →
      acc.val = clmulPartial me.val b.val shift.val →
      gf.poly_mul_loop b acc me shift
        ⦃ r => r.val = clmulPartial me.val b.val 16 ⦄ := by
  intro acc shift hs hacc
  unfold gf.poly_mul_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U32 × Std.U32 => 16 - s.2.val)
    (inv := fun s : Std.U32 × Std.U32 =>
      s.2.val ≤ 16 ∧ s.1.val = clmulPartial me.val b.val s.2.val)
    (post := fun r : Std.U32 => r.val = clmulPartial me.val b.val 16)
  · rintro ⟨acc1, shift1⟩ ⟨hsi, hinv⟩
    simp only [gf.poly_mul_loop.body]
    split
    · rename_i hlt
      have hlt16 : shift1.val < 16 := by scalar_tac
      step as ⟨v1, hv1⟩      -- v1 = 1#u16 <<< shift1
      step as ⟨i1, hi1⟩      -- i1 = b &&& v1
      -- value of v1: (1 <<< shift1) % 2^16 = 2^shift1
      have hv1v : v1.val = 2 ^ shift1.val := by
        rw [hv1, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
        have hsz : U16.size = 2 ^ 16 := by simp [Std.U16.size_def, Std.U16.numBits]
        rw [hsz]; exact Nat.pow_lt_pow_right (by norm_num) hlt16
      have hi1v : i1.val = b.val &&& 2 ^ shift1.val := by
        rw [hi1, UScalar.val_and, hv1v]
      -- the shifted summand value (no overflow at u32 since me < 2^16, shift < 16)
      have hsumlt : me.val <<< shift1.val < 2 ^ 32 := by
        rw [Nat.shiftLeft_eq]
        have hle : (2:Nat) ^ shift1.val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc me.val * 2 ^ shift1.val < 2 ^ 16 * 2 ^ shift1.val :=
                Nat.mul_lt_mul_of_lt_of_le hme (Nat.le_refl _) (by positivity)
          _ ≤ 2 ^ 16 * 2 ^ 15 := by gcongr
          _ < 2 ^ 32 := by norm_num
      split
      · rename_i hne
        -- the bit is set
        have hbit : b.val.testBit shift1.val := by
          rw [← and_pow_two_ne_zero, ← hi1v]
          have hne' : i1.val ≠ 0 := by
            have : i1 ≠ 0#u16 := by simpa using hne
            scalar_tac
          exact hne'
        step as ⟨i2, hi2⟩    -- i2 = me <<< shift1
        step as ⟨shift2, hshift2⟩  -- shift2 = shift1 + 1
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hsv : shift2.val = shift1.val + 1 := by scalar_tac
        rw [hsv, clmulPartial, if_pos hbit, UScalar.val_xor, hinv]
        congr 1
        rw [hi2]
        have hsz32 : U32.size = 2 ^ 32 := by simp [Std.U32.size_def, Std.U32.numBits]
        rw [hsz32, Nat.mod_eq_of_lt hsumlt]
      · rename_i heq
        -- bit not set
        have hbit : ¬ b.val.testBit shift1.val := by
          rw [← and_pow_two_ne_zero, ← hi1v]
          have hz : i1.val = 0 := by
            have : i1 = 0#u16 := by simp only [bne_iff_ne, ne_eq, not_not] at heq; exact heq.symm
            scalar_tac
          simpa using hz
        step as ⟨shift2, hshift2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hsv : shift2.val = shift1.val + 1 := by scalar_tac
        rw [hsv, clmulPartial, if_neg hbit]
        simp only [Nat.xor_zero]
        rw [hinv]
    · rename_i hge
      have : shift1.val = 16 := by scalar_tac
      rw [← this]; exact hinv
  · exact ⟨hs, hacc⟩

/-- **Hoare-triple value spec of `poly_mul`.** The extracted carryless multiply produces a
value whose underlying natural number is exactly the XOR-fold `clmulPartial a.val b.val 16`
(`⊕_{shift<16, b.testBit shift} (a << shift)`). -/
theorem poly_mul_spec (a b : Std.U16) :
    gf.poly_mul a b ⦃ r => r.val = clmulPartial a.val b.val 16 ⦄ := by
  unfold gf.poly_mul
  step as ⟨me, hme⟩
  -- me.val = a.val (cast U16 → U32 preserves the value)
  have hmev : me.val = a.val := by rw [hme]; scalar_tac
  have hmelt : me.val < 2 ^ 16 := by rw [hmev]; scalar_tac
  have hloop := poly_mul_loop_val b me hmelt 0#u32 0#u32 (by simp)
    (by simp [clmulPartial])
  rw [hmev] at hloop
  exact hloop

/-- The value of the extracted carryless multiply equals the XOR-fold. -/
theorem polyMulV_val (a b : Std.U16) :
    (polyMulV a b).val = clmulPartial a.val b.val 16 := by
  have htriple := poly_mul_spec a b
  unfold polyMulV
  cases h : gf.poly_mul a b with
  | ok c => rw [h] at htriple; simpa using htriple
  | div => rw [h] at htriple; simp at htriple
  | fail e => rw [h] at htriple; simp at htriple

/-! ### From the XOR-fold to the polynomial coefficient

We now show the bit `n` of the fold equals the char-2 convolution coefficient, then assemble
`toPoly32 (polyMulV a b) = toPoly a * toPoly b`. -/

/-- `bitZ32` of an XOR is the `ZMod 2` sum of the bits (the additive bridge for `U32`). -/
theorem bitZ32_xor (x y : Nat) (n : Nat) :
    (if (x ^^^ y).testBit n then (1 : ZMod 2) else 0) =
      (if x.testBit n then 1 else 0) + (if y.testBit n then 1 else 0) := by
  rw [Nat.testBit_xor]
  cases x.testBit n <;> cases y.testBit n <;> decide

/-- Bit `n` of the XOR-fold `clmulPartial m bv s`, as a `ZMod 2` element, is the sum over the
processed shifts `shift < s` of `bit shift of bv · bit n of (m << shift)`. -/
theorem bitZ32_clmulPartial (m bv : Nat) (s n : Nat) :
    (if (clmulPartial m bv s).testBit n then (1 : ZMod 2) else 0) =
      ∑ shift ∈ Finset.range s,
        (if bv.testBit shift then (1 : ZMod 2) else 0) *
        (if (m <<< shift).testBit n then (1 : ZMod 2) else 0) := by
  induction s with
  | zero => simp [clmulPartial]
  | succ k ih =>
    rw [clmulPartial, Finset.sum_range_succ, ← ih]
    rw [bitZ32_xor]
    congr 1
    by_cases hb : bv.testBit k
    · simp [hb]
    · simp [hb]

/-! ### Coefficient lemmas for the embeddings -/

/-- For a `U16`, bit `i ≥ 16` is `false` (the value is `< 2^16`). -/
theorem U16_testBit_high (a : Std.U16) (i : Nat) (hi : 16 ≤ i) : a.val.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  calc a.val < 2 ^ 16 := by scalar_tac
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

/-- For a `U32`, bit `i ≥ 32` is `false`. -/
theorem U32_testBit_high (a : Std.U32) (i : Nat) (hi : 32 ≤ i) : a.val.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  calc a.val < 2 ^ 32 := by scalar_tac
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

/-- The coefficient of `toPoly a` at index `n` is `bitZ a n` (for all `n`; for `n ≥ 16`
both are `0`). -/
theorem coeff_toPoly (a : Std.U16) (n : Nat) : (toPoly a).coeff n = bitZ a n := by
  unfold Spqr.Gf16Field.toPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hn : n < 16
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn; simp [Ne.symm hbn]
    · intro hcon; simp at hcon; omega
  · -- n ≥ 16: every term is 0, and bitZ a n = 0
    rw [Finset.sum_eq_zero]
    · unfold Spqr.Gf16Field.bitZ
      rw [U16_testBit_high a n (by omega)]
      simp
    · intro b hb
      have hbn : n ≠ b := by simp at hb; omega
      simp [hbn]

/-- The coefficient of `toPoly32 v` at index `n` is `bitZ32 v n` (for all `n`; for `n ≥ 32`
both are `0`). -/
theorem coeff_toPoly32 (v : Std.U32) (n : Nat) : (toPoly32 v).coeff n = bitZ32 v n := by
  unfold toPoly32
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hn : n < 32
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn; simp [Ne.symm hbn]
    · intro hcon; simp at hcon; omega
  · rw [Finset.sum_eq_zero]
    · unfold bitZ32
      rw [U32_testBit_high v n (by omega)]
      simp
    · intro b hb
      have hbn : n ≠ b := by simp at hb; omega
      simp [hbn]

/-! ### Stage 1 headline: the carryless multiply is the polynomial product -/

/-- Bit `n` of `a << shift`, as a `ZMod 2` element, factors as `[shift ≤ n] · bitZ a (n - shift)`. -/
theorem bitZ_shiftLeft (a : Std.U16) (shift n : Nat) :
    (if (a.val <<< shift).testBit n then (1 : ZMod 2) else 0) =
      (if shift ≤ n then (1 : ZMod 2) else 0) * bitZ a (n - shift) := by
  rw [Nat.testBit_shiftLeft]
  unfold Spqr.Gf16Field.bitZ
  by_cases hsn : shift ≤ n
  · simp only [hsn, decide_true, Bool.true_and, ge_iff_le, if_true]
    by_cases hb : a.val.testBit (n - shift) <;> simp [hb]
  · simp only [hsn, decide_false, Bool.false_and, ge_iff_le, if_false]
    simp [hsn]

/-- **Stage 1 of B-mul (carryless multiply = polynomial product).** Under the bit↔coefficient
embeddings, the extracted carryless multiply `poly_mul a b` (read as the value `polyMulV a b`,
the `u32` half of `gf_mul = poly_reduce ∘ poly_mul`) denotes EXACTLY the polynomial product:
`toPoly32 (polyMulV a b) = toPoly a * toPoly b` over `(ZMod 2)[X]`. Proved structurally from
the carryless XOR-fold matched against `Polynomial.coeff_mul` — no field laws, no value-space
`decide`, no axiom. This is the multiplicative half's first stage; the reduction (`poly_reduce`
= remainder mod `POLY_poly`) is the documented Stage 2 gap. -/
theorem toPoly32_polyMulV (a b : Std.U16) :
    toPoly32 (polyMulV a b) = toPoly a * toPoly b := by
  apply Polynomial.ext
  intro n
  -- RHS coefficient via convolution
  rw [Polynomial.coeff_mul]
  -- LHS coefficient = bitZ32 of the fold
  rw [coeff_toPoly32]
  unfold bitZ32
  rw [polyMulV_val, bitZ32_clmulPartial]
  -- each summand: rewrite the shifted bit as a product
  have hsum : ∀ shift,
      (if b.val.testBit shift then (1 : ZMod 2) else 0) *
        (if (a.val <<< shift).testBit n then (1 : ZMod 2) else 0) =
      bitZ a (n - shift) * bitZ b shift *
        (if shift ≤ n then (1 : ZMod 2) else 0) := by
    intro shift
    rw [bitZ_shiftLeft]
    unfold Spqr.Gf16Field.bitZ
    ring
  rw [Finset.sum_congr rfl (fun shift _ => hsum shift)]
  -- A single function whose sum (over a large enough range) is both sides.
  set g : Nat → ZMod 2 :=
    fun shift => bitZ a (n - shift) * bitZ b shift * (if shift ≤ n then (1 : ZMod 2) else 0)
    with hg
  -- LHS: range 16 ⊆ range (n + 16); the added terms are 0.
  have hLHS : ∑ shift ∈ Finset.range 16, g shift = ∑ shift ∈ Finset.range (n + 16), g shift := by
    apply Finset.sum_subset
    · intro x hx; simp at hx ⊢; omega
    · intro x _ hx
      simp only [Finset.mem_range] at hx
      -- x ≥ 16 ⇒ bitZ b x = 0
      have hbx : bitZ b x = 0 := by
        unfold Spqr.Gf16Field.bitZ; rw [U16_testBit_high b x (by omega)]; simp
      simp only [hg, hbx, mul_zero, zero_mul]
  -- RHS: antidiagonal = range (n+1); then reflect; range (n+1) ⊆ range (n+16) with 0 tail.
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (toPoly a).coeff i * (toPoly b).coeff j)]
  simp only [coeff_toPoly]
  have hRHS : ∑ k ∈ Finset.range (n + 1), bitZ a k * bitZ b (n - k)
            = ∑ shift ∈ Finset.range (n + 16), g shift := by
    rw [← Finset.sum_range_reflect (fun k => bitZ a k * bitZ b (n - k)) (n + 1)]
    -- reflected term at k: bitZ a (n + 1 - 1 - k) * bitZ b (n - (n + 1 - 1 - k))
    have hreidx : ∀ k ∈ Finset.range (n + 1),
        bitZ a (n + 1 - 1 - k) * bitZ b (n - (n + 1 - 1 - k)) = g k := by
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [hg]
      have h1 : n + 1 - 1 - k = n - k := by omega
      have h2 : n - (n - k) = k := by omega
      rw [h1, h2]
      have hkn : k ≤ n := by omega
      simp [hkn, mul_comm]
    rw [Finset.sum_congr rfl hreidx]
    apply Finset.sum_subset
    · intro x hx; simp at hx ⊢; omega
    · intro x _ hx
      simp only [Finset.mem_range] at hx
      -- x > n ⇒ the [x ≤ n] factor is 0
      simp [Nat.not_le.mpr (by omega : n < x)]
  rw [hLHS, hRHS]

end Spqr.Gf16Mul
