/-
  SPQR Reed–Solomon codec — Layer C, the DIVISION = FIELD-INVERSE bridge.

  ## What this file establishes

  The decoder's scaling step uses `gf.gf_div numer denom`, a Fermat-inverse ladder
  (`Extracted/Gf.lean`): starting from `square = denom`, `out = numer`, `i = 1`, it runs
  15 squaring iterations (`i : 1 → 16`), each doing

      square ← gfMulV square square ;  out ← gfMulV out square ;  i ← i + 1

  so the loop computes  `out = numer · denom^(2 + 4 + … + 2¹⁵) = numer · denom^(2¹⁶ − 2)`.

  We bank, in two strata, the in-boundary characterization of `gf.gf_div`:

    D1. **`gf_div_eq_fermat` (UNCONDITIONAL, field-law-FREE).** Read into the genuine
        GF(2¹⁶) commutative ring `GF16`, `gfDivV numer denom = numer · denom^(2¹⁶ − 2)`.
        This is a pure value spec of the Fermat ladder, using ONLY the unconditional
        `CommRing` (`mul_eq_gfMulV`, `pow_succ`); no irreducibility, no field inverse.

    D2. **`gf_div_eq_inv` (CONDITIONAL on `Irreducible POLY_poly` ALONE).** Over the field
        `GF16` (which is a field exactly when `POLY_poly` is irreducible — the documented
        WALL, strictly weaker than the prior `hmul + Irreducible` pair since `hmul` is
        discharged), for `denom ≠ 0`, `gfDivV numer denom = numer · denom⁻¹`. This is the
        missing ingredient the Lagrange-basis identification needs: it reads the extracted
        Fermat ladder as the genuine field inverse. The cardinality `|GF16| = 2¹⁶` (via the
        ring iso to `AdjoinRoot POLY_poly`, whose `ZMod 2`-finrank is `natDegree POLY_poly =
        16`) gives `denom^(2¹⁶ − 1) = 1` (`FiniteField.pow_card_sub_one_eq_one`), so
        `denom^(2¹⁶ − 2) = denom⁻¹`.

  Both mention `gf.gf_div` (via its value `gfDivV`), so they are in-boundary headlines about
  the extracted code. NO `axiom`, NO `sorry`, NO `native_decide`, NO `decide` over the value
  space. The only open premise in D2 is `Irreducible POLY_poly`, carried as a `Fact`, never an
  axiom; it is satisfiable, so D2 is non-vacuous.

  ## What this file does NOT do (the honest open obligation)

  - It does NOT discharge `Irreducible POLY_poly` (the WALL). D2 is conditional on it.
  - It does NOT, by itself, complete the full interpolation bridge (identifying the
    `prepare`/`complete`/`divFold` recurrences with Mathlib's `Lagrange.interpolate`). D2 is
    the field-inverse ingredient that bridge requires; the structural basis-polynomial
    matching is the remaining piece.
-/
import Demos.Spqr.RsInterp
import Demos.Spqr.Gf16FieldInstance
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdjoinRoot

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsInterp (gfDivV gf_div_eq)
open Spqr.Gf16Field (toPoly POLY_poly POLY_poly_ne_zero POLY_poly_natDegree)
open Spqr.Gf16FieldInstance (GF16 add_eq_gfAddV mul_eq_gfMulV zero_eq one_eq gfRingEquiv)
open Polynomial

namespace Spqr.RsDivInverse

/-! ### D0. The Fermat ladder as a pure fold over `GF16`. -/

/-- The pure functional model of `gf.gf_div_loop`. State `(square, out)` at loop index `i`;
each step `i < 16` squares `square` and multiplies it into `out`. Mirrors the body line for
line, kept as `gfMulV` (the banked value spec of `gf.gf_mul`). Returns `out`. -/
def fermatFold : Std.U16 → Std.U16 → Nat → Std.U16
  | square, out, i =>
    if i < 16 then
      let square' := gfMulV square square
      fermatFold square' (gfMulV out square') (i + 1)
    else out
  termination_by _ _ i => 16 - i
  decreasing_by rename_i h; omega

/-- **Value spec of the Fermat-ladder loop.** `gf.gf_div_loop square out i` returns exactly the
pure fold `fermatFold square out i.val` — pinning the `gfMulV` squaring recurrence the loop forms,
field-law-free. -/
theorem gf_div_loop_eq :
    ∀ (square out : Std.U16) (i : Std.Usize),
      gf.gf_div_loop square out i
        ⦃ r => r = fermatFold square out i.val ⦄ := by
  intro square out i
  unfold gf.gf_div_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.U16 × Std.Usize => 16 - s.2.2.val)
    (inv := fun s : Std.U16 × Std.U16 × Std.Usize =>
      fermatFold s.1 s.2.1 s.2.2.val = fermatFold square out i.val)
    (post := fun r : Std.U16 => r = fermatFold square out i.val)
  · rintro ⟨sq, o1, i1⟩ hinv
    simp only [gf.gf_div_loop.body]
    split
    · rename_i hlt
      rw [gf_mul_eq]
      simp only [Std.bind_tc_ok]
      rw [gf_mul_eq]
      step as ⟨i2, hi2⟩
      refine ⟨?_, by scalar_tac⟩
      simp only [hinv.symm]
      conv_rhs => rw [fermatFold]
      rw [if_pos (by scalar_tac)]
      simp only [hi2]
    · rename_i hge
      have h : ¬ i1.val < 16 := by scalar_tac
      conv at hinv => rw [fermatFold, if_neg h]
      exact hinv
  · rfl

/-- **Value spec of `gf.gf_div`** (entry point). `gf.gf_div numer denom` succeeds with value
`gfDivV numer denom = fermatFold denom numer 1` — the Fermat ladder. -/
theorem gfDivV_eq_fermat (numer denom : Std.U16) :
    gfDivV numer denom = fermatFold denom numer 1 := by
  have hok : gf.gf_div numer denom = .ok (gfDivV numer denom) := gf_div_eq numer denom
  -- `gf.gf_div numer denom` reduces to `gf.gf_div_loop denom numer 1`
  have hloop : gf.gf_div numer denom
      ⦃ r => r = fermatFold denom numer (1#usize).val ⦄ := gf_div_loop_eq denom numer 1#usize
  rw [hok] at hloop
  simpa using hloop

/-! ### D1. The Fermat ladder computes `numer · denom^(2¹⁶ − 2)` over `GF16` (UNCONDITIONAL). -/

/-- **Generalized Fermat-ladder accumulator (over the `GF16` CommRing).** Starting from
`square`, `out` at loop index `i ≤ 16` with `d = 16 - i` steps remaining, the ladder accumulates
the exponent `2^(d+1) − 2` of `square` into `out`:
`ofU16 (fermatFold square out i) = ofU16 out · (ofU16 square)^(2^(d+1) − 2)`. UNCONDITIONAL —
uses only the `CommRing` (`mul_eq_gfMulV` + `pow` arithmetic). -/
theorem fermatFold_pow (d : Nat) :
    ∀ (square out : Std.U16) (i : Nat), 16 - i = d → i ≤ 16 →
      GF16.ofU16 (fermatFold square out i)
        = GF16.ofU16 out * (GF16.ofU16 square) ^ (2 ^ (d + 1) - 2) := by
  induction d with
  | zero =>
    intro square out i hd hi
    have hi16 : i = 16 := by omega
    subst hi16
    rw [fermatFold, if_neg (by omega)]
    simp
  | succ d ih =>
    intro square out i hd hi
    have hilt : i < 16 := by omega
    rw [fermatFold, if_pos hilt]
    simp only []
    rw [ih (gfMulV square square) (gfMulV out (gfMulV square square)) (i + 1) (by omega) (by omega)]
    rw [← mul_eq_gfMulV, ← mul_eq_gfMulV]
    -- ofU16 out * (s*s) * ((s*s) ^ (2^(d+1)-2))
    set s := GF16.ofU16 square
    set o := GF16.ofU16 out
    rw [mul_assoc, ← pow_two s, ← pow_mul]
    rw [← pow_add]
    congr 2
    -- 2 + 2 * (2^(d+1) - 2) = 2^((d+1)+1) - 2
    have h2 : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ]; ring
    omega

/-- **`gf.gf_div` computes `numer · denom^(2¹⁶ − 2)` over `GF16`** (UNCONDITIONAL, in-boundary,
field-law-FREE). The extracted Fermat-inverse ladder, read into the genuine GF(2¹⁶) commutative
ring, is exactly `ofU16 numer · (ofU16 denom)^(2¹⁶ − 2)`. This pins the value of `gf.gf_div`
WITHOUT the field inverse — only the unconditional `CommRing`. -/
theorem gf_div_eq_fermat (numer denom : Std.U16) :
    GF16.ofU16 (gfDivV numer denom)
      = GF16.ofU16 numer * (GF16.ofU16 denom) ^ (2 ^ 16 - 2) := by
  rw [gfDivV_eq_fermat]
  have := fermatFold_pow 15 denom numer 1 (by norm_num) (by norm_num)
  -- d = 16 - 1 = 15, so exponent is 2^(15+1) - 2 = 2^16 - 2
  simpa using this

/-! ### D2. The Fermat ladder is the field inverse (CONDITIONAL on `Irreducible POLY_poly`).

`AdjoinRoot POLY_poly` is a field exactly when `POLY_poly` is irreducible (the documented WALL).
Its `ZMod 2`-finrank is `natDegree POLY_poly = 16`, so it is finite with `2¹⁶` elements; hence
`a^(2¹⁶ − 1) = 1` for `a ≠ 0` (`FiniteField.pow_card_sub_one_eq_one`), giving `a^(2¹⁶ − 2) = a⁻¹`.
Combined with the unconditional D1 (`gfDivV` ladder = `numer · denom^(2¹⁶ − 2)`), this reads the
extracted `gf.gf_div` as the genuine field inverse `numer · denom⁻¹`. -/

/-- `AdjoinRoot POLY_poly` is module-finite over `ZMod 2` (it has the degree-16 power basis). -/
theorem adjoinRoot_finite : Module.Finite (ZMod 2) (AdjoinRoot POLY_poly) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis POLY_poly_ne_zero).basis

/-- The `ZMod 2`-dimension of `AdjoinRoot POLY_poly` is `natDegree POLY_poly = 16`. -/
theorem adjoinRoot_finrank : Module.finrank (ZMod 2) (AdjoinRoot POLY_poly) = 16 := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis POLY_poly_ne_zero), AdjoinRoot.powerBasis_dim,
    POLY_poly_natDegree]

/-- `AdjoinRoot POLY_poly` has exactly `2¹⁶` elements (a degree-16 quotient over `ZMod 2`). -/
theorem adjoinRoot_card : Nat.card (AdjoinRoot POLY_poly) = 2 ^ 16 := by
  haveI := adjoinRoot_finite
  haveI : Finite (AdjoinRoot POLY_poly) := Module.finite_of_finite (ZMod 2)
  have h := FiniteField.pow_finrank_eq_natCard 2 (AdjoinRoot POLY_poly)
  rw [adjoinRoot_finrank] at h
  exact h.symm

/-- In the field `AdjoinRoot POLY_poly` (when irreducible), `a^(2¹⁶ − 2) = a⁻¹` for `a ≠ 0`,
since `a^(2¹⁶ − 1) = 1` by Fermat's little theorem over the order-`2¹⁶` field. -/
theorem adjoinRoot_pow_eq_inv [Fact (Irreducible POLY_poly)]
    (a : AdjoinRoot POLY_poly) (ha : a ≠ 0) :
    a ^ (2 ^ 16 - 2) = a⁻¹ := by
  haveI := adjoinRoot_finite
  haveI : Finite (AdjoinRoot POLY_poly) := Module.finite_of_finite (ZMod 2)
  haveI : Fintype (AdjoinRoot POLY_poly) := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot POLY_poly) = 2 ^ 16 := by
    rw [← Nat.card_eq_fintype_card]; exact adjoinRoot_card
  have h1 : a ^ (2 ^ 16 - 2) * a = 1 := by
    rw [← pow_succ, show 2 ^ 16 - 2 + 1 = 2 ^ 16 - 1 by norm_num, ← hc]
    exact FiniteField.pow_card_sub_one_eq_one a ha
  exact eq_inv_of_mul_eq_one_left h1

/-- **`gf.gf_div` is the field inverse `numer · denom⁻¹`** (CONDITIONAL on `Irreducible POLY_poly`
ALONE, in-boundary). Reflected through the ring iso `gfRingEquiv : GF16 ≃+* AdjoinRoot POLY_poly`,
the extracted Fermat-inverse division `gf.gf_div numer denom` (value `gfDivV`) equals
`phi numer * (phi denom)⁻¹` in the field `AdjoinRoot POLY_poly`, for `denom ≠ 0#u16`. This reads
the extracted ladder as the genuine GF(2¹⁶) field inverse — the ingredient the Lagrange-basis
identification needs. The only open premise is irreducibility, carried as a `Fact`, never an axiom. -/
theorem gf_div_eq_inv [Fact (Irreducible POLY_poly)]
    (numer denom : Std.U16) (hd : denom ≠ 0#u16) :
    gfRingEquiv (GF16.ofU16 (gfDivV numer denom))
      = gfRingEquiv (GF16.ofU16 numer) * (gfRingEquiv (GF16.ofU16 denom))⁻¹ := by
  rw [Gf16FieldInstance.gfRingEquiv_ofU16, Gf16FieldInstance.gfRingEquiv_ofU16,
    Gf16FieldInstance.gfRingEquiv_ofU16]
  -- push D1 (over GF16) through the ring iso to AdjoinRoot
  have hD1 : GF16.ofU16 (gfDivV numer denom)
      = GF16.ofU16 numer * (GF16.ofU16 denom) ^ (2 ^ 16 - 2) := gf_div_eq_fermat numer denom
  have := congrArg gfRingEquiv hD1
  rw [map_mul, map_pow, Gf16FieldInstance.gfRingEquiv_ofU16, Gf16FieldInstance.gfRingEquiv_ofU16,
    Gf16FieldInstance.gfRingEquiv_ofU16] at this
  rw [this]
  -- `phi denom ≠ 0` since `gfRingEquiv` is injective and sends `0#u16 ↦ 0`
  have hdne : Spqr.Gf16FieldAssembly.phi denom ≠ 0 := by
    rw [← Gf16FieldInstance.gfRingEquiv_ofU16]
    intro h
    apply hd
    have : GF16.ofU16 denom = (0 : GF16) := by
      apply gfRingEquiv.injective; rw [map_zero]; exact h
    rw [Gf16FieldInstance.zero_eq] at this
    exact this
  rw [adjoinRoot_pow_eq_inv (Spqr.Gf16FieldAssembly.phi denom) hdne]

end Spqr.RsDivInverse
