/-
  SPQR Reed–Solomon codec — Layer B-mul, STAGE 2: the extracted table reduction
  `gf.poly_reduce` realizes reduction mod `POLY_poly = x¹⁶+x¹²+x³+x+1` on the
  bit↔coefficient embedding. This closes the localized multiplicative gap
  `Spqr.Gf16Reduce.Stage2`, which discharges the `hmul` hypothesis and upgrades the
  six `Gf16FieldAssembly` ring laws from CONDITIONAL to UNCONDITIONAL.

  ## Structure (honest, IN-BOUNDARY, field-law-FREE, NO axiom / sorry / native_decide)

  The extracted reduction is `gf.poly_reduce = table-fold ∘ table-fold` with the table
  `REDUCE_BYTES[c] = (gf.reduce_from_byte c) as u16`, where `reduce_from_byte` is an
  8-step bit-fold. We bank, in order:

  * `reduceFromByteV` — the pure `U8 → U32` value of `gf.reduce_from_byte`, with `.ok` spec.
  * `reduce_from_byte_loop_spec` — the loop value spec carrying TWO simultaneous invariants:
      (I1) `mk (toPoly32 out) = 0` (every accumulated `POLY << i` is a `POLY_poly`-multiple), and
      (I2) `(out >>> 16) ^^^ a = a₀` together with the bit bounds `a < 2^i`, `out < 2^24`.
    At loop end (`i = 0`, hence `a = 0`) these give the per-byte residue fact
      (★)  `mk (toPoly (reduceFromByteV c).cast) = mk (toPoly32 ((c:U32) <<< 16))`.
  * `reduce_bytes_spec` — per-index table value spec (parametric loop invariant, the
    upstream hax `loop_invariant`): `table[c] = (reduceFromByteV c) as u16`.
  * `poly_reduce_residue` — the assembly: `mk (toPoly (poly_reduceV v)) = mk (toPoly32 v)`,
    i.e. `Spqr.Gf16Reduce.Stage2`.

  Closing `Stage2` discharges `hmul` via the banked `Gf16Reduce.stage2_imp_hmul`.
-/
import Demos.Spqr.Gf
import Demos.Spqr.Gf16Field
import Demos.Spqr.Gf16Mul
import Demos.Spqr.Gf16Reduce
import Demos.Spqr.Gf16FieldAssembly
import Mathlib.RingTheory.AdjoinRoot

open Aeneas Std Result
open Spqr.Gf
open Spqr.Gf16Mul (polyMulV toPoly32 toPoly32_polyMulV coeff_toPoly32 bitZ32 bitZ32_xor
  U32_testBit_high)
open Spqr.Gf16Field (toPoly POLY_poly POLY_poly_monic POLY_poly_natDegree)
open Spqr.Gf16Reduce (poly_reduceV poly_reduce_ok Stage2 stage2_imp_hmul)
open Polynomial

namespace Spqr.Gf16ReduceTable

/-! ### 0. `toPoly32` is additive over XOR, and `mk (POLY << i) = 0` -/

/-- `toPoly32` of a `Nat`-XOR splits as a sum (char-2 additivity over the bit embedding). -/
theorem toPoly32_xor (x y : Std.U32) :
    toPoly32 (x ^^^ y) = toPoly32 x + toPoly32 y := by
  apply Polynomial.ext; intro n
  rw [coeff_toPoly32, Polynomial.coeff_add, coeff_toPoly32, coeff_toPoly32]
  unfold bitZ32
  rw [UScalar.val_xor]
  exact bitZ32_xor x.val y.val n

/-- The numeric value of `gf.POLY` is `69643 = 0x1100b` (bits `{0,1,3,12,16}`). -/
theorem POLY_val : gf.POLY.val = 69643 := by
  have : gf.POLY = 69643#u32 := by simp only [gf.POLY]
  rw [this]; rfl

/-- Coefficient `k` of `POLY_poly` is bit `k` of `69643` (both are `1` exactly at
`k ∈ {0,1,3,12,16}`). -/
theorem coeff_POLY_poly (k : Nat) :
    POLY_poly.coeff k = (if (69643 : Nat).testBit k then (1 : ZMod 2) else 0) := by
  unfold POLY_poly
  -- expand the five-term polynomial coefficient-wise
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
  -- now both sides are decidable functions of small `k` ranges; case on whether k ≤ 16
  by_cases hk : k < 17
  · interval_cases k <;> decide
  · have h16 : ¬ k = 16 := by omega
    have h12 : ¬ k = 12 := by omega
    have h3 : ¬ k = 3 := by omega
    have h1 : ¬ k = 1 := by omega
    have h0 : ¬ k = 0 := by omega
    have hb : (69643 : Nat).testBit k = false := by
      apply Nat.testBit_eq_false_of_lt; calc (69643:Nat) < 2^17 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hb]
    simp only [if_false, h16, h12, h3, h0, if_neg (show ¬ (1:Nat) = k by omega), add_zero]
    simp

/-- `toPoly32` of the shifted reduction polynomial `(69643 <<< i)` is `POLY_poly * X^i`,
for `i ≤ 7` (so `69643 <<< i < 2^24 < 2^32` — no truncation). The single place the
`POLY_poly`-multiple structure enters `reduce_from_byte`. -/
theorem toPoly32_POLY_shift (w : Std.U32) (i : Nat) (hi : i ≤ 7)
    (hw : w.val = 69643 <<< i) :
    toPoly32 w = POLY_poly * X ^ i := by
  apply Polynomial.ext; intro n
  rw [coeff_toPoly32, Polynomial.coeff_mul_X_pow']
  unfold bitZ32
  rw [hw, Nat.testBit_shiftLeft]
  by_cases hin : i ≤ n
  · simp only [hin, decide_true, Bool.true_and, if_true, ge_iff_le]
    rw [coeff_POLY_poly]
  · simp [hin]

/-- **`mk (toPoly32 (69643 <<< i)) = 0`** for `i ≤ 7`: the accumulated reduction term is a
`POLY_poly`-multiple, so it vanishes in the quotient `AdjoinRoot POLY_poly`. -/
theorem mk_POLY_shift (w : Std.U32) (i : Nat) (hi : i ≤ 7) (hw : w.val = 69643 <<< i) :
    AdjoinRoot.mk POLY_poly (toPoly32 w) = 0 := by
  rw [toPoly32_POLY_shift w i hi hw, map_mul, AdjoinRoot.mk_self, zero_mul]

/-! ### 0b. Bit structure of the byte-fold mask `(69643 <<< j) >>> 16` (for `j ≤ 7`) -/

/-- `69643 <<< j < 2^24` for `j ≤ 7` (the reduction term never overflows the low 24 bits). -/
theorem POLY_shift_lt (j : Nat) (hj : j ≤ 7) : (69643 : Nat) <<< j < 2 ^ 24 := by
  rw [Nat.shiftLeft_eq]
  calc (69643 : Nat) * 2 ^ j ≤ 69643 * 2 ^ 7 := by
          apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_right (by norm_num) hj
    _ < 2 ^ 24 := by norm_num

/-- Bit `k` of the mask `m := (69643 <<< j) >>> 16` is set iff `k = j` or (`j ≥ 4` and `k = j-4`).
In particular every set bit is `≤ j`. -/
theorem mask_testBit (j k : Nat) (hj : j ≤ 7) :
    ((69643 <<< j) >>> 16 : Nat).testBit k
      = (69643 : Nat).testBit (k + 16 - j) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  have hge : decide (16 + k ≥ j) = true := by simp; omega
  rw [hge, Bool.true_and]
  congr 1; omega

/-- The mask `(69643 <<< j) >>> 16` is `< 2^(j+1)` (its top set bit is `j`), for `j ≤ 7`. -/
theorem mask_lt (j : Nat) (hj : j ≤ 7) : ((69643 <<< j) >>> 16 : Nat) < 2 ^ (j + 1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have hpos : 0 < (2:Nat) ^ j := by positivity
  have hstep : (69643 : Nat) * 2 ^ j < 2 ^ 17 * 2 ^ j :=
    (Nat.mul_lt_mul_right hpos).mpr (by norm_num)
  calc (69643 : Nat) * 2 ^ j < 2 ^ 17 * 2 ^ j := hstep
    _ = 2 ^ (j + 1) * 2 ^ 16 := by rw [← pow_add, ← pow_add]; ring_nf

/-- Bit `j` of the mask `(69643 <<< j) >>> 16` is set (for `j ≤ 7`): it comes from `POLY`'s
top bit `X^16`, which `>> 16` brings to `X^j`. -/
theorem mask_testBit_self (j : Nat) (hj : j ≤ 7) :
    ((69643 <<< j) >>> 16 : Nat).testBit j = true := by
  rw [mask_testBit j j hj]
  have h16 : j + 16 - j = 16 := by omega
  rw [h16]; decide

/-- Bits `> j` of the mask `(69643 <<< j) >>> 16` are all `0` (for `j ≤ 7`). -/
theorem mask_testBit_gt (j k : Nat) (hj : j ≤ 7) (hk : j < k) :
    ((69643 <<< j) >>> 16 : Nat).testBit k = false := by
  apply Nat.testBit_eq_false_of_lt
  calc ((69643 <<< j) >>> 16 : Nat) < 2 ^ (j + 1) := mask_lt j hj
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `toPoly32` of a left shift factors out `X^s`, provided the shifted Nat value matches
(`w'.val = w.val <<< s`, no overflow needed beyond `w'` being a genuine `U32`). -/
theorem toPoly32_shiftLeft (w w' : Std.U32) (s : Nat) (hw : w'.val = w.val <<< s) :
    toPoly32 w' = toPoly32 w * X ^ s := by
  apply Polynomial.ext; intro n
  rw [coeff_toPoly32, Polynomial.coeff_mul_X_pow']
  unfold bitZ32
  rw [hw, Nat.testBit_shiftLeft]
  by_cases hsn : s ≤ n
  · simp only [hsn, decide_true, Bool.true_and, if_true, ge_iff_le]
    rw [coeff_toPoly32]; unfold bitZ32; rfl
  · simp [hsn]

/-! ### 1. `reduce_from_byte` value and its residue spec (★) -/

/-- Helper: `Nat.shiftRight` distributes over `Nat.xor`. -/
theorem shiftRight_xor (x y s : Nat) : (x ^^^ y) >>> s = (x >>> s) ^^^ (y >>> s) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp [Nat.testBit_shiftRight, Nat.testBit_xor]

/-- The pure `U8 → U32` value of the extracted `gf.reduce_from_byte` (the never-taken
failure branch maps to `0`). -/
def reduceFromByteV (a : Std.U8) : Std.U32 :=
  match gf.reduce_from_byte a with
  | .ok c => c
  | _ => 0#u32

/-- `gf.reduce_from_byte a` succeeds with value `reduceFromByteV a` (from totality). -/
theorem reduceFromByteV_ok (a : Std.U8) : gf.reduce_from_byte a = .ok (reduceFromByteV a) := by
  have := Spqr.Gf.reduce_from_byte_total a
  unfold reduceFromByteV
  cases h : gf.reduce_from_byte a with
  | ok c => rfl
  | div => rw [h] at this; simp at this
  | fail e => rw [h] at this; simp at this

/-- **Loop value spec for `reduce_from_byte`.** Carries the two simultaneous invariants
(I1) `mk (toPoly32 out) = 0` and (I2) `(out >>> 16) ^^^ a = a₀`, plus the bit bounds
`a < 2^i`, `out < 2^24`. -/
theorem reduce_from_byte_loop_spec (a0 : Std.U8) :
    ∀ (a : Std.U8) (out i : Std.U32),
      i.val ≤ 8 → a.val < 2 ^ i.val → out.val < 2 ^ 24 →
      AdjoinRoot.mk POLY_poly (toPoly32 out) = 0 →
      (out.val >>> 16) ^^^ a.val = a0.val →
      gf.reduce_from_byte_loop a out i
        ⦃ r => AdjoinRoot.mk POLY_poly (toPoly32 r) = 0 ∧ (r.val >>> 16) = a0.val
               ∧ r.val < 2 ^ 24 ⦄ := by
  intro a out i hi ha hout hmk hxor
  unfold gf.reduce_from_byte_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.U32 × Std.U32 => s.2.2.val)
    (inv := fun s : Std.U8 × Std.U32 × Std.U32 =>
      s.2.2.val ≤ 8 ∧ s.1.val < 2 ^ s.2.2.val ∧ s.2.1.val < 2 ^ 24
        ∧ AdjoinRoot.mk POLY_poly (toPoly32 s.2.1) = 0
        ∧ (s.2.1.val >>> 16) ^^^ s.1.val = a0.val)
    (post := fun r : Std.U32 =>
      AdjoinRoot.mk POLY_poly (toPoly32 r) = 0 ∧ (r.val >>> 16) = a0.val ∧ r.val < 2 ^ 24)
  · rintro ⟨a1, out1, i1⟩ ⟨hi1, ha1, hout1, hmk1, hxor1⟩
    simp only at hi1 ha1 hout1 hmk1 hxor1
    simp only [gf.reduce_from_byte_loop.body]
    split
    · rename_i hlt
      have hi1pos : 0 < i1.val := by scalar_tac
      step as ⟨i2, hi2⟩       -- i2 = i1 - 1  (the bit index j)
      have hjval : i2.val = i1.val - 1 := by scalar_tac
      have hj7 : i2.val ≤ 7 := by omega
      have hsize32 : U32.size = 2 ^ 32 := by simp [Std.U32.size_def, Std.U32.numBits]
      have hsize8 : U8.size = 2 ^ 8 := by simp [Std.U8.size_def, Std.U8.numBits]
      step as ⟨i3, hi3⟩       -- i3 = 1#u8 <<< i2  (mask)
      step as ⟨i4, hi4⟩       -- i4 = i3 &&& a1   (bit test)
      have hi3v : i3.val = 2 ^ i2.val := by
        rw [hi3, hsize8, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hi4v : i4.val = 2 ^ i2.val &&& a1.val := by rw [hi4, UScalar.val_and, hi3v]
      have ha1lt : a1.val < 2 ^ (i2.val + 1) := by
        rw [show i1.val = i2.val + 1 by omega] at ha1; exact ha1
      split
      · -- bit i2 of a1 is set
        rename_i hne
        step as ⟨i5, hi5⟩      -- i5 = POLY <<< i2
        step as ⟨out2, hout2⟩  -- out2 = out1 ^^^ i5
        step as ⟨i6, hi6⟩      -- i6 = i5 >>> 16
        step as ⟨i7, hi7⟩      -- i7 = cast U8 i6
        step as ⟨a2, ha2⟩      -- a2 = a1 ^^^ i7
        -- numeric value facts
        have hpolyv : gf.POLY.val = 69643 := POLY_val
        have hshlt : (69643 : Nat) <<< i2.val < 2 ^ 24 := POLY_shift_lt i2.val hj7
        have hi5v : i5.val = 69643 <<< i2.val := by
          rw [hi5, hpolyv, hsize32, Nat.mod_eq_of_lt (by omega)]
        have hi6v : i6.val = (69643 <<< i2.val) >>> 16 := by rw [hi6, hi5v]
        have hmasklt8 : ((69643 <<< i2.val) >>> 16 : Nat) < 2 ^ 8 := by
          calc ((69643 <<< i2.val) >>> 16 : Nat) < 2 ^ (i2.val + 1) := mask_lt i2.val hj7
            _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hi7v : i7.val = (69643 <<< i2.val) >>> 16 := by
          rw [hi7, UScalar.cast_val_eq, hi6v,
            show (2:Nat) ^ UScalarTy.U8.numBits = 2 ^ 8 from rfl, Nat.mod_eq_of_lt hmasklt8]
        have hout2v : out2.val = out1.val ^^^ i5.val := by rw [hout2, UScalar.val_xor]
        have ha2v : a2.val = a1.val ^^^ i7.val := by rw [ha2, UScalar.val_xor]
        -- out2 < 2^24
        have hout2lt : out2.val < 2 ^ 24 := by
          rw [hout2v, hi5v]; exact Nat.xor_lt_two_pow hout1 hshlt
        -- mk (toPoly32 out2) = 0
        have hmk2 : AdjoinRoot.mk POLY_poly (toPoly32 out2) = 0 := by
          have : out2 = out1 ^^^ i5 := by
            apply Std.UScalar.eq_of_val_eq; rw [hout2v, UScalar.val_xor]
          rw [this, toPoly32_xor, map_add, hmk1, zero_add,
            mk_POLY_shift i5 i2.val hj7 hi5v]
        -- I2 preservation: out2 >>> 16 ^^^ a2 = a0
        have hxor2 : out2.val >>> 16 ^^^ a2.val = a0.val := by
          have hcollapse : ∀ x y z : Nat, (x ^^^ z) ^^^ (y ^^^ z) = x ^^^ y := by
            intro x y z
            apply Nat.eq_of_testBit_eq; intro k
            simp only [Nat.testBit_xor]
            cases x.testBit k <;> cases y.testBit k <;> cases z.testBit k <;> decide
          rw [hout2v, ha2v, hi7v, shiftRight_xor, hi5v,
            hcollapse (out1.val >>> 16) a1.val ((69643 <<< i2.val) >>> 16), hxor1]
        -- a2 < 2^i2.val : bit i2 set in a1, mask clears it, both < 2^(i2.val+1)
        have hbitset : a1.val.testBit i2.val = true := by
          -- i4 = 2^i2 &&& a1 ≠ 0, so bit i2 of a1 is set
          have hi4ne : i4.val ≠ 0 := by
            have hh : i4 ≠ 0#u8 := by simpa using hne
            intro hz; apply hh; apply Std.UScalar.eq_of_val_eq; simpa using hz
          by_contra hb
          simp only [Bool.not_eq_true] at hb
          apply hi4ne
          rw [hi4v]
          apply Nat.eq_of_testBit_eq; intro k
          rw [Nat.testBit_and, Nat.zero_testBit]
          by_cases hk : k = i2.val
          · subst hk; rw [hb, Bool.and_false]
          · rw [Nat.testBit_two_pow, decide_eq_false (by omega : ¬ i2.val = k), Bool.false_and]
        have ha2lt : a2.val < 2 ^ i2.val := by
          rw [ha2v, hi7v]
          apply Nat.lt_of_testBit i2.val
          · -- bit i2 of a2 is 0
            rw [Nat.testBit_xor, hbitset, mask_testBit_self i2.val hj7]; rfl
          · -- bit i2 of 2^i2 is 1
            rw [Nat.testBit_two_pow]; simp
          · -- higher bits agree (both 0)
            intro k hk
            rw [Nat.testBit_xor, mask_testBit_gt i2.val k hj7 hk, Bool.xor_false]
            rw [Nat.testBit_eq_false_of_lt (by
              calc a1.val < 2 ^ (i2.val + 1) := ha1lt
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega))]
            rw [Nat.testBit_two_pow]; simp; omega
        exact ⟨by omega, ha2lt, hout2lt, hmk2, hxor2, by omega⟩
      · -- bit i2 of a1 is NOT set: a1, out1 unchanged, i decremented
        rename_i heq
        have ha1lt2 : a1.val < 2 ^ i2.val := by
          -- bit i2 of a1 is 0 (since i4 = 0) and a1 < 2^(i2.val+1)
          have hi4z : i4.val = 0 := by simpa using heq
          have hbit0 : a1.val.testBit i2.val = false := by
            by_contra hb; simp only [Bool.not_eq_false] at hb
            have : (2 ^ i2.val &&& a1.val).testBit i2.val = true := by
              rw [Nat.testBit_and, Nat.testBit_two_pow]; simp [hb]
            rw [← hi4v, hi4z] at this; simp at this
          -- a1 < 2^(i2+1), bit i2 = 0 ⇒ a1 < 2^i2
          apply Nat.lt_of_testBit i2.val hbit0 (by rw [Nat.testBit_two_pow]; simp)
          intro k hk
          rw [Nat.testBit_eq_false_of_lt (by
            calc a1.val < 2 ^ (i2.val + 1) := ha1lt
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega))]
          rw [Nat.testBit_two_pow]; simp; omega
        refine ⟨show i2.val ≤ 8 by omega, ha1lt2, hout1, hmk1, hxor1, show i2.val < i1.val by omega⟩
    · -- i1 = 0 : done. a1 < 2^0 = 1 so a1 = 0; xor gives (out1 >>> 16) = a0
      rename_i hge
      have hi10 : i1.val = 0 := by scalar_tac
      have ha10 : a1.val = 0 := by have := ha1; rw [hi10] at this; simpa using this
      refine ⟨hmk1, ?_, hout1⟩
      rw [← hxor1, ha10, Nat.xor_zero]
  · exact ⟨hi, ha, hout, hmk, hxor⟩

/-- **Value spec of `reduce_from_byte` (the two invariants at loop exit).** For every byte `c`,
`reduceFromByteV c` satisfies (I1) `mk (toPoly32 ·) = 0`, (I2) its high half `>>> 16` is `c`,
and the bound `< 2^24`. -/
theorem reduceFromByteV_spec (c : Std.U8) :
    AdjoinRoot.mk POLY_poly (toPoly32 (reduceFromByteV c)) = 0
      ∧ (reduceFromByteV c).val >>> 16 = c.val
      ∧ (reduceFromByteV c).val < 2 ^ 24 := by
  have hc8 : c.val < 2 ^ 8 := by scalar_tac
  have htriple := reduce_from_byte_loop_spec c c 0#u32 8#u32 (by decide)
    (by show c.val < 2 ^ (8#u32).val; simpa using hc8)
    (by decide) (by
      have h0 : toPoly32 0#u32 = 0 := by
        apply Polynomial.ext; intro n; rw [coeff_toPoly32]; unfold bitZ32
        simp [show (0#u32 : Std.U32).val = 0 from by decide]
      rw [h0, map_zero])
    (by simp [show (0#u32 : Std.U32).val = 0 from by decide])
  -- the loop is exactly `gf.reduce_from_byte c`
  have heq : gf.reduce_from_byte c = .ok (reduceFromByteV c) := reduceFromByteV_ok c
  unfold gf.reduce_from_byte at heq
  rw [heq] at htriple
  simpa using htriple

/-- The low-16-bit truncation `(reduceFromByteV c) as u16` (the value stored in `REDUCE_BYTES[c]`)
as a `U16`. -/
noncomputable def tableEntry (c : Std.U8) : Std.U16 := UScalar.cast .U16 (reduceFromByteV c)

/-- `toPoly` (degree `< 16`) of a `U16` agrees with `toPoly32` of the same value (cast to `U32`),
because both read the same low-16 bits. -/
theorem toPoly_eq_toPoly32_cast (x : Std.U32) (hx : x.val < 2 ^ 16) :
    toPoly (UScalar.cast .U16 x) = toPoly32 x := by
  apply Polynomial.ext; intro n
  rw [Spqr.Gf16Mul.coeff_toPoly, coeff_toPoly32]
  unfold Spqr.Gf16Field.bitZ bitZ32
  have hcast : (UScalar.cast .U16 x).val = x.val := by
    rw [UScalar.cast_val_eq, show (2:Nat) ^ UScalarTy.U16.numBits = 2 ^ 16 from rfl,
      Nat.mod_eq_of_lt hx]
  rw [hcast]

/-- **(★) The per-byte residue fact.** The table entry `REDUCE_BYTES[c] = reduce_from_byte(c) as u16`
realizes `c · X^16` modulo `POLY_poly`: `mk (toPoly (tableEntry c)) = mk ((toPoly c-as-poly) · X^16)`,
where the RHS is `mk (toPoly32 r')` for any `U32` `r'` holding `c << 16`. We phrase the residue with
the polynomial `C-free` form `(∑_{i<8} bitⁱ(c)·X^i) · X^16`. This is the heart of the reduction
correctness — the only place a `POLY_poly`-multiple enters. -/
theorem tableEntry_residue (c : Std.U8) (csh : Std.U32) (hcsh : csh.val = c.val <<< 16) :
    AdjoinRoot.mk POLY_poly (toPoly (tableEntry c))
      = AdjoinRoot.mk POLY_poly (toPoly32 csh) := by
  obtain ⟨hmk0, hhi, hlt24⟩ := reduceFromByteV_spec c
  set r := reduceFromByteV c with hr
  -- the table entry value: low 16 bits of r
  have htev : (tableEntry c).val = r.val % 2 ^ 16 := by
    unfold tableEntry
    rw [UScalar.cast_val_eq, show (2:Nat) ^ UScalarTy.U16.numBits = 2 ^ 16 from rfl]
  -- r = low16(r) XOR csh at the Nat level (high half of r is c, low half is the entry)
  have hsplit : r.val = (r.val % 2 ^ 16) ^^^ csh.val := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_xor, hcsh]
    by_cases hk : k < 16
    · rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.testBit_shiftLeft]
      have : ¬ 16 ≤ k := by omega
      simp [this]
    · rw [Nat.testBit_mod_two_pow, decide_eq_false hk, Bool.false_and, Bool.false_xor,
        Nat.testBit_shiftLeft]
      have h16k : 16 ≤ k := by omega
      simp only [h16k, decide_true, Bool.true_and, ge_iff_le]
      rw [← hhi, Nat.testBit_shiftRight]; congr 1; omega
  -- the table entry value as a U32 (cast), to use toPoly32 additivity
  have hmod16lt : r.val % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by positivity)
  have hentry32v : (UScalar.cast .U32 (tableEntry c)).val = r.val % 2 ^ 16 := by
    rw [UScalar.cast_val_eq, show (2:Nat) ^ UScalarTy.U32.numBits = 2 ^ 32 from rfl, htev,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmod16lt (by norm_num))]
  have hcastback : UScalar.cast .U16 (UScalar.cast .U32 (tableEntry c)) = tableEntry c := by
    apply Std.UScalar.eq_of_val_eq
    rw [show (UScalar.cast .U16 (UScalar.cast .U32 (tableEntry c))).val
          = (UScalar.cast .U32 (tableEntry c)).val % 2 ^ 16 from by
        rw [UScalar.cast_val_eq]; rfl, hentry32v, htev,
      Nat.mod_mod_of_dvd _ (by norm_num : (2:Nat)^16 ∣ 2^16)]
  have hentry32 : toPoly (tableEntry c) = toPoly32 (UScalar.cast .U32 (tableEntry c)) := by
    rw [← toPoly_eq_toPoly32_cast (UScalar.cast .U32 (tableEntry c)) (by rw [hentry32v]; exact hmod16lt),
      hcastback]
  -- toPoly32 r = toPoly32 (entry) + toPoly32 csh
  have hrxor : r = (UScalar.cast .U32 (tableEntry c)) ^^^ csh := by
    apply Std.UScalar.eq_of_val_eq
    rw [UScalar.val_xor, hentry32v, ← hsplit]
  have hmk_entry : AdjoinRoot.mk POLY_poly (toPoly32 (UScalar.cast .U32 (tableEntry c)))
      = AdjoinRoot.mk POLY_poly (toPoly32 csh) := by
    have h0 := hmk0
    rw [hrxor, toPoly32_xor, map_add] at h0
    -- 0 = mk(entry) + mk(csh); the ring AdjoinRoot POLY_poly has characteristic 2 (ZMod 2 base)
    have hself : ∀ x : AdjoinRoot POLY_poly, x + x = 0 := by
      intro x
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [← map_add]
      have h2 : p + p = 0 := by
        have hcast : ((2 : ℕ) : (ZMod 2)[X]) = 0 := by
          rw [← Polynomial.C_eq_natCast, show ((2 : ℕ) : ZMod 2) = 0 from by decide, map_zero]
        calc p + p = (2 : ℕ) • p := by rw [two_nsmul]
          _ = ((2 : ℕ) : (ZMod 2)[X]) * p := by rw [nsmul_eq_mul]
          _ = 0 := by rw [hcast, zero_mul]
      rw [h2, map_zero]
    -- a + b = 0 ⇒ a = b (char 2): a = a + (a + b) = (a + a) + b = b
    set A := AdjoinRoot.mk POLY_poly (toPoly32 (UScalar.cast .U32 (tableEntry c)))
    set B := AdjoinRoot.mk POLY_poly (toPoly32 csh)
    -- h0 : 0 = A + B ; hself A : A + A = 0 ; want A = B
    have hAB : A + B = 0 := h0
    have hAA : A + A = 0 := hself A
    calc A = A + (A + B) := by rw [hAB, add_zero]
      _ = (A + A) + B := by ring
      _ = B := by rw [hAA, zero_add]
  rw [hentry32, hmk_entry]

/-! ### 2. The reduction table value spec (`reduce_bytes`) -/

/-- The table value at byte index `c`, as a `Nat`-keyed function: `reduce_from_byte(c) as u16`. -/
noncomputable def tableNat (k : Nat) : Std.U16 :=
  UScalar.cast .U16 (reduceFromByteV (UScalar.cast .U8 (Std.U32.ofNatCore (k % 2^32) (by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)))))

/-- **Loop value spec for `reduce_bytes`** (the upstream hax `loop_invariant`): the table entry at
each index `k < i` equals `tableNat k = reduce_from_byte(k) as u16`. -/
theorem reduce_bytes_loop_spec :
    ∀ (out : Array Std.U16 256#usize) (i : Std.Usize), i.val ≤ 256 →
      (∀ k, k < i.val → out.val[k]! = tableNat k) →
      gf.reduce_bytes_loop out i
        ⦃ r => ∀ k, k < 256 → r.val[k]! = tableNat k ⦄ := by
  intro out i hi hpre
  unfold gf.reduce_bytes_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 256#usize) × Std.Usize => 256 - s.2.val)
    (inv := fun s : (Array Std.U16 256#usize) × Std.Usize =>
      s.2.val ≤ 256 ∧ (∀ k, k < s.2.val → s.1.val[k]! = tableNat k))
    (post := fun r : Array Std.U16 256#usize => ∀ k, k < 256 → r.val[k]! = tableNat k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [gf.reduce_bytes_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩       -- i2 = cast u8 i1
      rw [reduceFromByteV_ok i2]
      simp only [Std.bind_tc_ok]
      step as ⟨i3, hi3⟩       -- i3 = cast u16 (reduceFromByteV i2)
      step as ⟨o2, ho2⟩       -- o2 = out.update i1 i3
      step as ⟨i4, hi4⟩       -- i4 = i1 + 1
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro k hk
      subst ho2
      by_cases hke : k = i1.val
      · subst hke
        simp_lists [hi3]
        unfold tableNat
        congr 3
        apply Std.UScalar.eq_of_val_eq
        rw [hi2, UScalar.cast_val_eq, UScalar.cast_val_eq,
          show (Std.U32.ofNatCore (i1.val % 2^32) _).val = i1.val % 2^32 from
            Std.U32.ofNatCore_val_eq _]
        have hlt : i1.val < 2 ^ 32 := by scalar_tac
        rw [Nat.mod_eq_of_lt hlt]
      · have hklt : k < i1.val := by scalar_tac
        simp_lists
        exact hpre1 k hklt
    · rename_i hge
      intro k hk; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-- Every table entry value is `< 2^16` (it is a `U16`). -/
theorem tableNat_lt (k : Nat) : (tableNat k).val < 2 ^ 16 := by
  have := (tableNat k).hBounds
  simpa [Std.U16.size_def, Std.U16.numBits] using (tableNat k).hBounds

/-- A `U32` value is `< 2^32`. -/
theorem u32_lt (x : Std.U32) : x.val < 2 ^ 32 := by
  simpa [Std.U32.size_def, Std.U32.numBits] using x.hBounds

/-- The value of the extracted `gf.reduce_bytes` table (the `Result` payload). -/
noncomputable def reduceBytesV : Array Std.U16 256#usize :=
  match gf.reduce_bytes with
  | .ok t => t
  | _ => Array.repeat 256#usize 0#u16

/-- **Value spec of `reduce_bytes`.** The extracted table at each index `k < 256` is
`tableNat k = reduce_from_byte(k) as u16`, and `gf.reduce_bytes` succeeds with that table. -/
theorem reduce_bytes_eq :
    gf.reduce_bytes = .ok reduceBytesV
      ∧ ∀ k, k < 256 → reduceBytesV.val[k]! = tableNat k := by
  have htriple : gf.reduce_bytes ⦃ r => ∀ k, k < 256 → r.val[k]! = tableNat k ⦄ := by
    unfold gf.reduce_bytes
    apply reduce_bytes_loop_spec _ 0#usize (by scalar_tac)
    intro k hk; scalar_tac
  refine ⟨?_, ?_⟩
  · unfold reduceBytesV
    cases h : gf.reduce_bytes with
    | ok t => rfl
    | div => rw [h] at htriple; simp at htriple
    | fail e => rw [h] at htriple; simp at htriple
  · intro k hk
    have : gf.reduce_bytes = .ok reduceBytesV := by
      unfold reduceBytesV
      cases h : gf.reduce_bytes with
      | ok t => rfl
      | div => rw [h] at htriple; simp at htriple
      | fail e => rw [h] at htriple; simp at htriple
    rw [this] at htriple
    exact htriple k hk

/-! ### 3. The Stage-2 assembly: `poly_reduce` realizes reduction mod `POLY_poly` -/

/-- Closed-form value spec for `gf.poly_reduce`. With `c1 = v>>24`, `t1 = (tableNat c1).val`,
`v1 = v ^^^ (t1<<<8)`, `c2 = (v1>>16)&0xFF`, `t2 = (tableNat c2).val`, the result is
`(v1 ^^^ t2) as u16`. We bank the precise `Nat`-level value of `poly_reduceV v`. -/
theorem poly_reduce_form (v : Std.U32) :
    (poly_reduceV v).val
      = ((v.val ^^^ ((tableNat (v.val >>> 24)).val <<< 8))
          ^^^ (tableNat (((v.val ^^^ ((tableNat (v.val >>> 24)).val <<< 8)) >>> 16) &&& 255)).val)
        % 2 ^ 16 := by
  have htriple : gf.poly_reduce v ⦃ r => r.val =
      ((v.val ^^^ ((tableNat (v.val >>> 24)).val <<< 8))
        ^^^ (tableNat (((v.val ^^^ ((tableNat (v.val >>> 24)).val <<< 8)) >>> 16) &&& 255)).val)
      % 2 ^ 16 ⦄ := by
    unfold gf.poly_reduce
    rw [(reduce_bytes_eq).1]
    simp only [Std.bind_tc_ok]
    step as ⟨i, hi⟩            -- i = v >>> 24
    step as ⟨i1, hi1⟩          -- i1 = cast usize i
    -- table read at index i1 (< 256)
    have hi1lt : i1.val < 256 := by scalar_tac
    have hv32 : v.val < 2 ^ 32 := by scalar_tac
    have hvsr : v.val >>> 24 < 256 := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    have hi1val : i1.val = v.val >>> 24 := by
      rw [hi1, UScalar.cast_val_eq, hi, Nat.mod_eq_of_lt]
      have hub : (256 : Nat) ≤ 2 ^ UScalarTy.Usize.numBits := by
        have hb : (8 : Nat) ≤ UScalarTy.Usize.numBits := by
          show (8 : Nat) ≤ System.Platform.numBits
          rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
        calc (256:Nat) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num) hb
      omega
    step as ⟨i2, hi2⟩          -- i2 = reduceBytesV.index i1
    have hi2val : i2 = tableNat (v.val >>> 24) := by
      have hbe := (reduce_bytes_eq).2 i1.val hi1lt
      rw [show i2 = reduceBytesV.val[i1.val]! from by simp_lists [hi2], hbe, hi1val]
    step as ⟨i3, hi3⟩          -- i3 = cast u32 i2
    -- i3.val = (tableNat (v>>24)).val, < 2^16
    have ht1lt : (tableNat (v.val >>> 24)).val < 2 ^ 16 := tableNat_lt _
    have hi3v : i3.val = (tableNat (v.val >>> 24)).val := by
      rw [hi3, UScalar.cast_val_eq, hi2val,
        show (2:Nat)^UScalarTy.U32.numBits = 2^32 from rfl, Nat.mod_eq_of_lt]
      omega
    step as ⟨i4, hi4⟩          -- i4 = i3 <<< 8
    have hi4v : i4.val = (tableNat (v.val >>> 24)).val <<< 8 := by
      rw [hi4, hi3v, show U32.size = 2 ^ 32 from by simp [Std.U32.size_def, Std.U32.numBits],
        Nat.mod_eq_of_lt]
      rw [Nat.shiftLeft_eq]
      calc (tableNat (v.val >>> 24)).val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
              Nat.mul_lt_mul_of_lt_of_le ht1lt (_root_.le_refl _) (by positivity)
        _ < 2 ^ 32 := by norm_num
    step as ⟨v1, hv1⟩          -- v1 = v ^^^ i4
    have hv1v : v1.val = v.val ^^^ ((tableNat (v.val >>> 24)).val <<< 8) := by
      rw [hv1, UScalar.val_xor, hi4v]
    step as ⟨i5, hi5⟩          -- i5 = v1 >>> 16
    step as ⟨shifted_v, hsv⟩   -- shifted_v = cast usize i5
    step as ⟨i21, hi21⟩        -- i21 = shifted_v &&& 255
    -- i21.val = (v1.val >>> 16) &&& 255
    have hi5v : i5.val = v1.val >>> 16 := by rw [hi5]
    have hsvv : shifted_v.val = v1.val >>> 16 := by
      rw [hsv, UScalar.cast_val_eq, hi5v, Nat.mod_eq_of_lt]
      have hb : (2:Nat) ^ 16 ≤ 2 ^ UScalarTy.Usize.numBits := by
        apply Nat.pow_le_pow_right (by norm_num)
        show (16:Nat) ≤ System.Platform.numBits
        rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
      have hv1lt : v1.val < 2 ^ 32 := u32_lt v1
      have : v1.val >>> 16 < 2 ^ 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
      omega
    have hi21v : i21.val = (v1.val >>> 16) &&& 255 := by
      rw [hi21, UScalar.val_and, hsvv]; rfl
    have hi21lt : i21.val < 256 := by
      rw [hi21v]; have := Nat.and_le_right (n := v1.val >>> 16) (m := 255); omega
    step as ⟨i6, hi6⟩          -- i6 = table[i21]
    have hi6val : i6 = tableNat ((v1.val >>> 16) &&& 255) := by
      have hbe := (reduce_bytes_eq).2 i21.val hi21lt
      rw [hi6, hbe, hi21v]
    step as ⟨i7, hi7⟩          -- i7 = cast u32 i6
    have ht2lt : (tableNat ((v1.val >>> 16) &&& 255)).val < 2 ^ 16 := tableNat_lt _
    have hi7v : i7.val = (tableNat ((v1.val >>> 16) &&& 255)).val := by
      rw [hi7, UScalar.cast_val_eq, hi6val,
        show (2:Nat)^UScalarTy.U32.numBits = 2^32 from rfl, Nat.mod_eq_of_lt]
      omega
    step as ⟨v2, hv2⟩          -- v2 = v1 ^^^ i7
    have hv2v : v2.val = v1.val ^^^ (tableNat ((v1.val >>> 16) &&& 255)).val := by
      rw [hv2, UScalar.val_xor, hi7v]
    -- final: result = cast u16 v2
    rw [show (UScalar.cast .U16 v2).val = v2.val % 2 ^ 16 from by
      rw [UScalar.cast_val_eq]; rfl, hv2v, hv1v]
  unfold poly_reduceV
  cases h : gf.poly_reduce v with
  | ok c => rw [h] at htriple; simpa using htriple
  | div => rw [h] at htriple; simp at htriple
  | fail e => rw [h] at htriple; simp at htriple

/-- `tableNat k = tableEntry (the byte `k % 256`)`. -/
theorem tableNat_eq_tableEntry (k : Nat) :
    tableNat k = tableEntry (Std.U8.ofNatCore (k % 256) (by
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (by show (256:Nat) ≤ 2 ^ UScalarTy.U8.numBits; norm_num))) := by
  unfold tableNat tableEntry
  congr 2
  apply Std.UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq, show (Std.U8.ofNatCore (k % 256) _).val = k % 256 from
    Std.U8.ofNatCore_val_eq _,
    show (Std.U32.ofNatCore (k % 2^32) _).val = k % 2^32 from Std.U32.ofNatCore_val_eq _,
    show (2:Nat) ^ UScalarTy.U8.numBits = 2 ^ 8 from rfl]
  omega

/-- **`tableNat` residue:** `mk (toPoly (tableNat k)) = mk (toPoly32 ⟨(k%256) <<< 16⟩)`. -/
theorem tableNat_residue (k : Nat) (csh : Std.U32) (hcsh : csh.val = (k % 256) <<< 16) :
    AdjoinRoot.mk POLY_poly (toPoly (tableNat k))
      = AdjoinRoot.mk POLY_poly (toPoly32 csh) := by
  rw [tableNat_eq_tableEntry]
  apply tableEntry_residue
  rw [hcsh, show (Std.U8.ofNatCore (k % 256) _).val = k % 256 from Std.U8.ofNatCore_val_eq _]

/-- `mk (toPoly32 ⟨x <<< s⟩) = mk (toPoly32 ⟨y⟩) ⟹ mk (toPoly32 ⟨x <<< (s+t)⟩) = mk (toPoly32 ⟨y <<< t⟩)`:
shifting both sides of an mk-equation by `X^t`. Stated via the polynomial `* X^t`. -/
theorem mk_shift_step {x y : Std.U32}
    (h : AdjoinRoot.mk POLY_poly (toPoly32 x) = AdjoinRoot.mk POLY_poly (toPoly32 y))
    (x' y' : Std.U32) (t : Nat) (hx' : x'.val = x.val <<< t) (hy' : y'.val = y.val <<< t) :
    AdjoinRoot.mk POLY_poly (toPoly32 x') = AdjoinRoot.mk POLY_poly (toPoly32 y') := by
  rw [toPoly32_shiftLeft x x' t hx', toPoly32_shiftLeft y y' t hy', map_mul, map_mul, h]

/-- Build a `U32` from a `Nat` value that is `< 2^32`. -/
noncomputable def mkU32 (n : Nat) (h : n < 2 ^ 32) : Std.U32 :=
  Std.U32.ofNatCore n (by simpa [Std.U32.numBits] using h)

theorem mkU32_val (n : Nat) (h : n < 2 ^ 32) : (mkU32 n h).val = n := by
  unfold mkU32; exact Std.U32.ofNatCore_val_eq _

/-- **Truncation lemma.** For any `U32` `x`, `mk (toPoly (cast u16 x)) = mk (toPoly32 x) +
mk (toPoly32 ⟨(x>>16) <<< 16⟩)` — the dropped high half re-enters as a correction (char 2). -/
theorem mk_cast_u16 (x : Std.U32) (hi : Std.U32) (hhi : hi.val = (x.val >>> 16) <<< 16) :
    AdjoinRoot.mk POLY_poly (toPoly (UScalar.cast .U16 x))
      = AdjoinRoot.mk POLY_poly (toPoly32 x)
        + AdjoinRoot.mk POLY_poly (toPoly32 hi) := by
  -- toPoly (cast u16 x) = toPoly32 ⟨low16 x⟩, and x = low16 x XOR (high<<16)
  have hlow16lt : x.val % 2 ^ 16 < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)
  have hsplit : x.val = (x.val % 2 ^ 16) ^^^ hi.val := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_xor, hhi]
    by_cases hk : k < 16
    · rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.testBit_shiftLeft]
      simp [show ¬ 16 ≤ k by omega]
    · rw [Nat.testBit_mod_two_pow, decide_eq_false hk, Bool.false_and, Bool.false_xor,
        Nat.testBit_shiftLeft]
      simp only [show 16 ≤ k by omega, decide_true, Bool.true_and, ge_iff_le,
        Nat.testBit_shiftRight]
      congr 1; omega
  -- cast u16 x has value x % 2^16
  have hclt : (UScalar.cast .U16 x).val = x.val % 2 ^ 16 := by
    rw [UScalar.cast_val_eq, show (2:Nat) ^ UScalarTy.U16.numBits = 2 ^ 16 from rfl]
  set low := mkU32 (x.val % 2 ^ 16) hlow16lt with hlowdef
  have hlowval : low.val = x.val % 2 ^ 16 := mkU32_val _ hlow16lt
  -- toPoly (cast u16 x) = toPoly32 low
  have hcast : toPoly (UScalar.cast .U16 x) = toPoly32 low := by
    have heq : UScalar.cast .U16 low = UScalar.cast .U16 x := by
      apply Std.UScalar.eq_of_val_eq
      rw [show (UScalar.cast .U16 low).val = low.val % 2 ^ 16 from by rw [UScalar.cast_val_eq]; rfl,
        hclt, hlowval, Nat.mod_mod_of_dvd _ (by norm_num : (2:Nat)^16 ∣ 2^16)]
    rw [← heq, toPoly_eq_toPoly32_cast low (by rw [hlowval]; exact Nat.mod_lt _ (by positivity))]
  -- x = low XOR hi
  have hxsplit : x = low ^^^ hi := by
    apply Std.UScalar.eq_of_val_eq; rw [UScalar.val_xor, hlowval, ← hsplit]
  rw [hcast]
  have hself : ∀ z : AdjoinRoot POLY_poly, z + z = 0 := fun z => by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [← map_add]
    have hcast2 : ((2 : ℕ) : (ZMod 2)[X]) = 0 := by
      rw [← Polynomial.C_eq_natCast, show ((2 : ℕ) : ZMod 2) = 0 from by decide, map_zero]
    have : p + p = 0 := by
      calc p + p = (2 : ℕ) • p := by rw [two_nsmul]
        _ = ((2:ℕ):(ZMod 2)[X]) * p := by rw [nsmul_eq_mul]
        _ = 0 := by rw [hcast2, zero_mul]
    rw [this, map_zero]
  -- mk(toPoly32 x) + mk(toPoly32 hi) = (mk(low)+mk(hi)) + mk(hi) = mk(low)
  conv_rhs => rw [hxsplit, toPoly32_xor, map_add, add_assoc, hself, add_zero]

/-- Characteristic 2 in the quotient: `z + z = 0` for every residue. -/
theorem mk_self_add (z : AdjoinRoot POLY_poly) : z + z = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [← map_add]
  have hcast2 : ((2 : ℕ) : (ZMod 2)[X]) = 0 := by
    rw [← Polynomial.C_eq_natCast, show ((2 : ℕ) : ZMod 2) = 0 from by decide, map_zero]
  have : p + p = 0 := by
    calc p + p = (2 : ℕ) • p := by rw [two_nsmul]
      _ = ((2:ℕ):(ZMod 2)[X]) * p := by rw [nsmul_eq_mul]
      _ = 0 := by rw [hcast2, zero_mul]
  rw [this, map_zero]

/-- `mk (toPoly32 ·)` of a `Nat`-XOR (held in a `U32`) splits additively in the quotient. -/
theorem mk_xor (x y w : Std.U32) (hw : w.val = x.val ^^^ y.val) :
    AdjoinRoot.mk POLY_poly (toPoly32 w)
      = AdjoinRoot.mk POLY_poly (toPoly32 x) + AdjoinRoot.mk POLY_poly (toPoly32 y) := by
  have : w = x ^^^ y := by apply Std.UScalar.eq_of_val_eq; rw [UScalar.val_xor, hw]
  rw [this, toPoly32_xor, map_add]

/-- The `(★)` residue, lifted to a placed `U32` word and shifted by `X^s`: a word `tsh` holding
`(tableNat k).val <<< s` is `mk`-equal to a word `csh` holding `(k%256) <<< (16+s)`. -/
theorem tableNat_residue_shift (k s : Nat) (tsh csh : Std.U32)
    (htsh : tsh.val = (tableNat k).val <<< s) (hcsh : csh.val = (k % 256) <<< (16 + s)) :
    AdjoinRoot.mk POLY_poly (toPoly32 tsh) = AdjoinRoot.mk POLY_poly (toPoly32 csh) := by
  -- the base residue at shift 0
  have hklt : (k % 256) <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    calc (k % 256) * 2 ^ 16 < 256 * 2 ^ 16 :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (_root_.le_refl _) (by positivity)
      _ < 2 ^ 32 := by norm_num
  set cbase := mkU32 _ hklt with hcbase
  have hcbaseval : cbase.val = (k % 256) <<< 16 := mkU32_val _ hklt
  -- tableNat k as a U32 word
  have htnlt : (tableNat k).val < 2 ^ 32 := Nat.lt_of_lt_of_le (tableNat_lt k) (by norm_num)
  set tbase := mkU32 _ htnlt with htbase
  have htbaseval : tbase.val = (tableNat k).val := mkU32_val _ htnlt
  -- base mk equality:  mk(toPoly32 tbase) = mk(toPoly32 cbase)
  have hbase : AdjoinRoot.mk POLY_poly (toPoly32 tbase) = AdjoinRoot.mk POLY_poly (toPoly32 cbase) := by
    have hres := tableNat_residue k cbase hcbaseval
    rw [← hres]
    -- toPoly (tableNat k) = toPoly32 tbase  (both read the low-16 bits of (tableNat k).val)
    have hcast : UScalar.cast .U16 tbase = tableNat k := by
      apply Std.UScalar.eq_of_val_eq
      rw [show (UScalar.cast .U16 tbase).val = tbase.val % 2 ^ 16 from by rw [UScalar.cast_val_eq]; rfl,
        htbaseval, Nat.mod_eq_of_lt (tableNat_lt k)]
    rw [← hcast, toPoly_eq_toPoly32_cast tbase (by rw [htbaseval]; exact tableNat_lt k)]
  -- shift both by X^s
  apply mk_shift_step hbase tsh csh s
  · rw [htsh, htbaseval]
  · rw [hcsh, hcbaseval]
    -- ((k%256) <<< 16) <<< s = (k%256) <<< (16 + s)
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_add]; ring

theorem poly_reduce_residue (v : Std.U32) :
    AdjoinRoot.mk POLY_poly (toPoly (poly_reduceV v))
      = AdjoinRoot.mk POLY_poly (toPoly32 v) := by
  have hv32 : v.val < 2 ^ 32 := u32_lt v
  set t1 := tableNat (v.val >>> 24) with ht1
  have ht1lt : t1.val < 2 ^ 16 := tableNat_lt _
  set v1n := v.val ^^^ (t1.val <<< 8) with hv1n
  set t2 := tableNat ((v1n >>> 16) &&& 255) with ht2
  have ht2lt : t2.val < 2 ^ 16 := tableNat_lt _
  -- the full pre-truncation word
  have hwlt : (v.val ^^^ (t1.val <<< 8)) ^^^ t2.val < 2 ^ 32 := by
    apply Nat.xor_lt_two_pow
    · apply Nat.xor_lt_two_pow hv32
      rw [Nat.shiftLeft_eq]
      calc t1.val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
            Nat.mul_lt_mul_of_lt_of_le ht1lt (_root_.le_refl _) (by positivity)
        _ < 2 ^ 32 := by norm_num
    · omega
  set wU32 := mkU32 _ hwlt with hwU32
  have hwval : wU32.val = (v.val ^^^ (t1.val <<< 8)) ^^^ t2.val := mkU32_val _ hwlt
  -- poly_reduceV v = cast u16 wU32
  have hprv : poly_reduceV v = UScalar.cast .U16 wU32 := by
    apply Std.UScalar.eq_of_val_eq
    rw [poly_reduce_form, show (UScalar.cast .U16 wU32).val = wU32.val % 2 ^ 16 from by
      rw [UScalar.cast_val_eq]; rfl, hwval]
  rw [hprv]
  -- the high half ⟨wU32 >> 16 << 16⟩
  have hhilt : (wU32.val >>> 16) <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have : wU32.val < 2 ^ 32 := u32_lt wU32
    have hd : wU32.val / 2 ^ 16 < 2 ^ 16 := by omega
    calc wU32.val / 2 ^ 16 * 2 ^ 16 < 2 ^ 16 * 2 ^ 16 :=
          Nat.mul_lt_mul_of_lt_of_le hd (_root_.le_refl _) (by positivity)
      _ = 2 ^ 32 := by norm_num
  set hiU := mkU32 _ hhilt with hhiU
  have hhival : hiU.val = (wU32.val >>> 16) <<< 16 := mkU32_val _ hhilt
  rw [mk_cast_u16 wU32 hiU hhival]
  -- Abbreviations for the two indexing bytes.
  set c1 := v.val >>> 24 with hc1
  have hc1lt : c1 < 256 := by rw [hc1, Nat.shiftRight_eq_div_pow]; omega
  set c2 := (v1n >>> 16) &&& 255 with hc2
  have hc2lt : c2 ≤ 255 := by rw [hc2]; exact Nat.and_le_right
  -- t1 < 2^16, t1<<8 < 2^24
  have ht1sh_lt : t1.val <<< 8 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    calc t1.val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
          Nat.mul_lt_mul_of_lt_of_le ht1lt (_root_.le_refl _) (by positivity)
      _ < 2 ^ 32 := by norm_num
  have ht2_lt : t2.val < 2 ^ 32 := Nat.lt_of_lt_of_le ht2lt (by norm_num)
  -- (A) the placed words c1<<24 and c2<<16
  have hc1sh_lt : c1 <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    calc c1 * 2 ^ 24 < 256 * 2 ^ 24 :=
          Nat.mul_lt_mul_of_lt_of_le hc1lt (_root_.le_refl _) (by positivity)
      _ = 2 ^ 32 := by norm_num
  have hc2sh_lt : c2 <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    calc c2 * 2 ^ 16 < 256 * 2 ^ 16 := by
          apply Nat.mul_lt_mul_of_lt_of_le (by omega) (_root_.le_refl _) (by positivity)
      _ < 2 ^ 32 := by norm_num
  set c1sh := mkU32 _ hc1sh_lt with hc1sh
  have hc1shval : c1sh.val = c1 <<< 24 := mkU32_val _ hc1sh_lt
  set c2sh := mkU32 _ hc2sh_lt with hc2sh
  have hc2shval : c2sh.val = c2 <<< 16 := mkU32_val _ hc2sh_lt
  set t1sh := mkU32 _ ht1sh_lt with ht1sh
  have ht1shval : t1sh.val = t1.val <<< 8 := mkU32_val _ ht1sh_lt
  set t2w := mkU32 _ ht2_lt with ht2w
  have ht2wval : t2w.val = t2.val := mkU32_val _ ht2_lt
  -- (★) shifted:  mk(t1<<8) = mk(c1<<24)   and   mk(t2) = mk(c2<<16)
  have hAeq : AdjoinRoot.mk POLY_poly (toPoly32 t1sh) = AdjoinRoot.mk POLY_poly (toPoly32 c1sh) := by
    apply tableNat_residue_shift (v.val >>> 24) 8 t1sh c1sh ht1shval
    rw [hc1shval, hc1, Nat.mod_eq_of_lt (by rw [Nat.shiftRight_eq_div_pow]; omega)]
  have hBeq : AdjoinRoot.mk POLY_poly (toPoly32 t2w) = AdjoinRoot.mk POLY_poly (toPoly32 c2sh) := by
    apply tableNat_residue_shift ((v1n >>> 16) &&& 255) 0 t2w c2sh ht2wval
    rw [hc2shval, hc2, Nat.mod_eq_of_lt (by omega)]
  -- mk(wU32) = mk(v) + mk(t1<<8) + mk(t2)
  have hwU32_decomp : AdjoinRoot.mk POLY_poly (toPoly32 wU32)
      = AdjoinRoot.mk POLY_poly (toPoly32 v)
        + AdjoinRoot.mk POLY_poly (toPoly32 t1sh)
        + AdjoinRoot.mk POLY_poly (toPoly32 t2w) := by
    -- wU32 = (v ^^^ t1sh) ^^^ t2w  at the value level
    set inner := mkU32 (v.val ^^^ (t1.val <<< 8)) (by
        apply Nat.xor_lt_two_pow hv32 ht1sh_lt) with hinner
    have hinnerval : inner.val = v.val ^^^ (t1.val <<< 8) := mkU32_val _ _
    rw [mk_xor inner t2w wU32 (by rw [hwval, hinnerval, ht2wval]),
        mk_xor v t1sh inner (by rw [hinnerval, ht1shval])]
  -- (C) hiU = c1<<24 XOR c2<<16  at the value level
  have hhi_struct : hiU.val = (c1 <<< 24) ^^^ (c2 <<< 16) := by
    rw [hhival, hwval]
    apply Nat.eq_of_testBit_eq; intro k
    -- LHS: ((W >> 16) << 16).testBit k  ;  RHS bit pattern
    rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
    by_cases hk16 : 16 ≤ k
    · simp only [hk16, decide_true, Bool.true_and, ge_iff_le]
      rw [Nat.testBit_shiftRight]
      have hkk : 16 + (k - 16) = k := by omega
      rw [hkk, Nat.testBit_xor, Nat.testBit_xor]
      -- t2 < 2^16 ⇒ bit k ≥ 16 of t2 is 0
      have ht2bit : t2.val.testBit k = false :=
        Nat.testBit_eq_false_of_lt
          (Nat.lt_of_lt_of_le ht2lt (Nat.pow_le_pow_right (by norm_num) hk16))
      rw [ht2bit, Bool.xor_false]
      by_cases hk24 : 24 ≤ k
      · -- k ≥ 24 : only `v` contributes (t1<<8 < 2^24, c2<<16 < 2^24)
        have ht1sh24 : t1.val <<< 8 < 2 ^ 24 := by
          rw [Nat.shiftLeft_eq]
          calc t1.val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
                Nat.mul_lt_mul_of_lt_of_le ht1lt (_root_.le_refl _) (by positivity)
            _ = 2 ^ 24 := by norm_num
        have ht1bit : (t1.val <<< 8).testBit k = false :=
          Nat.testBit_eq_false_of_lt
            (Nat.lt_of_lt_of_le ht1sh24 (Nat.pow_le_pow_right (by norm_num) hk24))
        have hc2bit : c2.testBit (k - 16) = false := by
          apply Nat.testBit_eq_false_of_lt
          calc c2 ≤ 255 := hc2lt
            _ < 2 ^ (k - 16) := by
                calc (255:Nat) < 2 ^ 8 := by norm_num
                  _ ≤ 2 ^ (k - 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [ht1bit, Bool.xor_false, hc2bit, Bool.xor_false]
        -- LHS = v.testBit k ; RHS = (c1<<24).testBit k = c1.testBit (k-24) = v.testBit k
        rw [show c1 = v.val >>> 24 from hc1, Nat.testBit_shiftRight]
        rw [show decide (24 ≤ k) = true from by simp [hk24], Bool.true_and]
        have : 24 + (k - 24) = k := by omega
        rw [this]
      · -- 16 ≤ k < 24 : only c2 region (c1<<24 bit 0 here)
        rw [show decide (24 ≤ k) = false from by simp [show ¬ 24 ≤ k by omega], Bool.false_and,
          Bool.false_xor]
        -- LHS = (v ^^^ t1<<8).testBit k ; RHS = c2.testBit (k-16)
        rw [show c2 = (v1n >>> 16) &&& 255 from hc2,
          Nat.testBit_and, Nat.testBit_shiftRight]
        have hmaskbit : (255 : Nat).testBit (k - 16) = true := by
          rw [show (255:Nat) = 2^8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
          simp; omega
        rw [hmaskbit, Bool.and_true, hv1n]
        have : 16 + (k - 16) = k := by omega
        rw [Nat.testBit_xor, this]
    · -- k < 16 : LHS bit 0 ; RHS both shifted past k (decide conditions false)
      rw [show decide (16 ≤ k) = false from by simp [show ¬ 16 ≤ k by omega],
        show decide (24 ≤ k) = false from by simp [show ¬ 24 ≤ k by omega]]
      simp
  -- combine
  set MV := AdjoinRoot.mk POLY_poly (toPoly32 v) with hMV
  set MA := AdjoinRoot.mk POLY_poly (toPoly32 c1sh) with hMA
  set MB := AdjoinRoot.mk POLY_poly (toPoly32 c2sh) with hMB
  have hhiU_decomp : AdjoinRoot.mk POLY_poly (toPoly32 hiU) = MA + MB := by
    rw [mk_xor c1sh c2sh hiU (by rw [hhi_struct, hc1shval, hc2shval])]
  rw [hwU32_decomp, hAeq, hBeq, hhiU_decomp]
  -- (MV + MA + MB) + (MA + MB) = MV
  calc MV + MA + MB + (MA + MB)
      = MV + (MA + MA) + (MB + MB) := by ring
    _ = MV := by rw [mk_self_add, mk_self_add, add_zero, add_zero]

/-! ### 4. Stage 2 is closed; the multiplicative bridge `hmul`; UNCONDITIONAL ring laws

`poly_reduce_residue` is exactly `Spqr.Gf16Reduce.Stage2`. Composing with the banked
`Gf16Reduce.stage2_imp_hmul` (Stage 2 ⇒ `hmul`) proves the multiplicative bridge for the
extracted `gfMulV` UNCONDITIONALLY, which discharges the `hmul` premise of the six
`Gf16FieldAssembly` ring laws — turning them from CONDITIONAL into UNCONDITIONAL theorems
ABOUT the extracted `gf.gf_mul` / `gf.gf_add`. -/

open Spqr.Gf16FieldAssembly (phi)

/-- **Stage 2 (closed).** The extracted table reduction `gf.poly_reduce` realizes reduction
mod `POLY_poly` on the bit↔coefficient embedding — the precise `Spqr.Gf16Reduce.Stage2`
statement, now proved (NO axiom, NO `sorry`, NO `native_decide`). -/
theorem stage2_proved : Stage2 := poly_reduce_residue

/-- **The multiplicative bridge `hmul` (proved).** For the extracted field multiply,
`phi (gfMulV a b) = phi a * phi b` UNCONDITIONALLY — discharged from `Stage2` via the banked
`Gf16Reduce.stage2_imp_hmul`. This is the residue correctness of `gf.gf_mul = poly_reduce ∘ poly_mul`. -/
theorem hmul_proved (a b : Std.U16) : phi (gfMulV a b) = phi a * phi b :=
  stage2_imp_hmul stage2_proved a b

/-! #### The six `Gf16FieldAssembly` ring laws, now UNCONDITIONAL (headlines about `gfMulV`) -/

/-- **`gfMulV` is commutative** (UNCONDITIONAL — `hmul` discharged via Stage 2). -/
theorem gfMulV_comm (a b : Std.U16) : gfMulV a b = gfMulV b a :=
  Spqr.Gf16FieldAssembly.gfMulV_comm hmul_proved a b

/-- **`gfMulV` is associative** (UNCONDITIONAL). -/
theorem gfMulV_assoc (a b c : Std.U16) :
    gfMulV (gfMulV a b) c = gfMulV a (gfMulV b c) :=
  Spqr.Gf16FieldAssembly.gfMulV_assoc hmul_proved a b c

/-- **`1#u16` is a right identity for `gfMulV`** (UNCONDITIONAL). -/
theorem gfMulV_one (a : Std.U16) : gfMulV a 1#u16 = a :=
  Spqr.Gf16FieldAssembly.gfMulV_one hmul_proved a

/-- **`1#u16` is a left identity for `gfMulV`** (UNCONDITIONAL). -/
theorem gfMulV_one_left (a : Std.U16) : gfMulV 1#u16 a = a :=
  Spqr.Gf16FieldAssembly.gfMulV_one_left hmul_proved a

/-- **`gfMulV` distributes over `gfAddV`** (left, UNCONDITIONAL). -/
theorem gfMulV_gfAddV_distrib (a b c : Std.U16) :
    gfMulV a (gfAddV b c) = gfAddV (gfMulV a b) (gfMulV a c) :=
  Spqr.Gf16FieldAssembly.gfMulV_gfAddV_distrib hmul_proved a b c

/-- **`gfMulV` distributes over `gfAddV`** (right, UNCONDITIONAL). -/
theorem gfMulV_gfAddV_distrib_right (a b c : Std.U16) :
    gfMulV (gfAddV a b) c = gfAddV (gfMulV a c) (gfMulV b c) :=
  Spqr.Gf16FieldAssembly.gfMulV_gfAddV_distrib_right hmul_proved a b c

end Spqr.Gf16ReduceTable
