/-
  SPQR Reed–Solomon codec — Layer C, the LAGRANGE ASSEMBLY bridge: the extracted
  `gf.lagrange_interpolate` builds the basis-weighted sum `Σ_i scale_i · ℓ̃_i` over the
  genuine GF(2¹⁶) commutative ring, and (conditional on `Irreducible POLY_poly` alone) IS
  Mathlib's `Lagrange.interpolate` of the samples.

  ## What this file establishes

  `gf.lagrange_interpolate xs ys n` (Extracted/Gf.lean) is, by construction:

      template = prepare xs n                                  -- nodal product ∏(X − xs[k])
      working₀ = complete template xs ys n 0                   -- scale₀ · X · ℓ̃₀
      out      = loop0 n out₀ working₀ 0                        -- out[k] = working₀[k+1]  (÷ X)
      out      = loop1 xs ys n out template working₀ 1          -- for i=1..n-1:
                   workingᵢ = complete template xs ys n i       --   scaleᵢ · X · ℓ̃ᵢ
                   out[j] ⊕= workingᵢ[j+1]                       --   accumulate (÷ X)

  Each `complete` produces (banked `RsCompleteBridge.complete_prepare_eq_scaled_basis`)
  `gpoly workingᵢ (n+1) = C(scaleᵢ) · X · basisNumerᵢ`, where `basisNumerᵢ = ∏_{k≠i}(X − xs[k])`
  has degree `n−1 < n`. The loop0/loop1 shift `out[k] = working[k+1]` divides out the `× X`
  (the upstream "working is x · <basis poly>" offset), leaving the genuine basis numerator. The
  loop1 driver accumulates these per-`i` numerators (`gfAddV` = `+`). So over GF16:

    L1. **`lagrange_interpolate_eq_basis_sum` (UNCONDITIONAL, in-boundary).** For `n ≤ 36`,
        `gf.lagrange_interpolate xs ys n` succeeds with array `out` whose `GF16` coefficient
        polynomial `gpoly out n` equals the basis-weighted sum
        `Σ_{i<n} C(scaleᵢ) · basisNumerᵢ` — the Lagrange interpolant in numerator/weight form,
        over the genuine GF(2¹⁶) commutative ring, NO field inverse, NO irreducibility.

    L2. **`lagrange_interpolate_eq_interpolate` (CONDITIONAL on `Irreducible POLY_poly` ALONE).**
        Over the field GF16 (a field exactly when `POLY_poly` is irreducible — the WALL), the
        basis sum IS Mathlib's `Lagrange.interpolate`: reading `scaleᵢ = ysᵢ / ∏(xsᵢ − xsⱼ)` as
        the genuine Lagrange weight (`RsDivInverse.gf_div_eq_inv`, the field inverse) and matching
        `scaleᵢ · basisNumerᵢ` against `Lagrange.basis`. Strictly weaker premise than the prior
        `hmul + Irreducible` pair (`hmul` is discharged by Stage 2).

  Both mention `gf.lagrange_interpolate` (via the banked `complete`/`prepare` value specs), so
  they are in-boundary headlines about the extracted code. NO `axiom`, NO `sorry`, NO
  `native_decide`, NO `decide` over the value space.

  ## What this file does NOT do (the honest open obligation)

  - It does NOT discharge `Irreducible POLY_poly` (the WALL). L2 is conditional on it.
  - The full `decode ∘ encode = id` capstone (`RsCapstone.decode_value_at_roundtrip` /
    `RsFieldBridge.decode_value_at_roundtrip_gf16`) still needs L2 plumbed through `eval` to
    discharge `hbridge`; that final composition is the next step.
-/
import Demos.Spqr.RsCompleteBridge
import Demos.Spqr.RsDivInverse

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsInterp (gfDivV denomV complete_eq complete_loop0_eq0
  lagrange_interpolate_loop0_eq lagrange_interpolate_loop1_loop0_eq prepare_eq)
open Spqr.RsEvalBridge (gpoly eval_gpoly)
open Spqr.RsPrepareBridge (nodal nodal_natDegree)
open Spqr.RsCompleteBridge (basisNumer complete_prepare_eq_scaled_basis)
open Spqr.Gf16FieldInstance (GF16 add_eq_gfAddV mul_eq_gfMulV zero_eq one_eq)
open Polynomial

namespace Spqr.RsLagrangeBridge

/-! ### `gpoly` coefficients and the divide-by-`X` shift. -/

/-- The `k`-th coefficient of `gpoly c len` is `ofU16 (c k)` for `k < len`, else `0`. -/
theorem gpoly_coeff (c : Nat → Std.U16) (len k : Nat) :
    (gpoly c len).coeff k = if k < len then GF16.ofU16 (c k) else 0 := by
  unfold gpoly
  rw [finset_sum_coeff]
  by_cases hk : k < len
  · rw [if_pos hk]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbk
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hkmem
      exact absurd (Finset.mem_range.mpr hk) hkmem
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_range] at hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- **The divide-by-`X` shift.** If a coefficient function `out` reads off the higher coefficients
of `working` (`ofU16 (out k) = (gpoly working (n+1)).coeff (k+1)` for `k < n`) and the working
polynomial is `X · Q` with `Q.natDegree < n`, then `gpoly out n = Q`. This is exactly the
loop0/loop1 read of `working[k+1]` stripping the `× X` factor that `complete` produces. -/
theorem gpoly_shift_eq (out : Nat → Std.U16) (working : Nat → Std.U16) (n : Nat) (Q : GF16[X])
    (hQdeg : Q.natDegree < n)
    (hwork : gpoly working (n + 1) = X * Q)
    (hout : ∀ k, k < n → GF16.ofU16 (out k) = (gpoly working (n + 1)).coeff (k + 1)) :
    gpoly out n = Q := by
  apply Polynomial.ext
  intro k
  rw [gpoly_coeff]
  by_cases hk : k < n
  · rw [if_pos hk, hout k hk, hwork, coeff_X_mul]
  · rw [if_neg hk]
    -- Q.coeff k = 0 since k ≥ n > natDegree Q
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ### The accumulate step: one `loop1_loop0` adds one basis numerator to the running sum. -/

/-- **One `lagrange_interpolate_loop1_loop0` accumulation step adds `Q` to the running sum.**
For `n ≤ 36`, if the incoming `out` array has `GF16` polynomial `gpoly out n = P` and the
`working` array has polynomial `gpoly working (n+1) = X · Q` (the `complete` output: a basis
numerator times `X`), then the result of `lagrange_interpolate_loop1_loop0 n out working 0`
has polynomial `gpoly result n = P + Q` — the `gfAddV out[j] working[j+1]` accumulation reads
off `working[j+1] = (X·Q).coeff (j+1) = Q.coeff j`, stripping the `× X` and adding `Q`. -/
theorem loop1_loop0_accum (n : Std.Usize) (out working : Array Std.U16 37#usize)
    (hn : n.val ≤ 36) (P Q : GF16[X]) (hQdeg : Q.natDegree < n.val)
    (hP : gpoly (fun k => out.val[k]!) n.val = P)
    (hwork : gpoly (fun k => working.val[k]!) (n.val + 1) = X * Q) :
    gf.lagrange_interpolate_loop1_loop0 n out working 0#usize
      ⦃ r => gpoly (fun k => r.val[k]!) n.val = P + Q ⦄ := by
  have hspec := lagrange_interpolate_loop1_loop0_eq n working hn out 0#usize (by simp)
  apply Std.WP.spec_mono hspec
  rintro r ⟨hacc, _, _⟩
  -- pointwise coefficient identity
  apply Polynomial.ext
  intro k
  rw [coeff_add, ← hP, gpoly_coeff, gpoly_coeff]
  by_cases hk : k < n.val
  · rw [if_pos hk, if_pos hk]
    -- r[k] = gfAddV out[k] working[k+1]
    rw [hacc k (by simp) hk, ← add_eq_gfAddV]
    congr 1
    -- ofU16 working[k+1] = (X*Q).coeff (k+1) = Q.coeff k
    have : GF16.ofU16 working.val[k + 1]! = (gpoly (fun j => working.val[j]!) (n.val + 1)).coeff (k + 1) := by
      rw [gpoly_coeff, if_pos (by omega)]
    rw [this, hwork, coeff_X_mul]
  · rw [if_neg hk, if_neg hk]
    rw [coeff_eq_zero_of_natDegree_lt (by omega), add_zero]

/-! ### The basis numerator is monic of degree `n − 1`; the `complete` output as `X · Qᵢ`. -/

/-- `basisNumer xs n i` is monic of degree `(range n).erase i |>.card`. -/
theorem basisNumer_natDegree (xs : Array Std.U16 36#usize) (n i : Nat) (hi : i < n) :
    (basisNumer xs n i).natDegree = n - 1 := by
  unfold basisNumer
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hi), Finset.card_range]

/-- The per-`i` basis term `Qᵢ = C(scaleᵢ) · basisNumerᵢ`, the Lagrange-weighted basis numerator
that `complete` produces (times `X`). Its degree is `< n`. -/
noncomputable def basisTerm (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat) : GF16[X] :=
  C (GF16.ofU16 (gfDivV ys.val[i]! (denomV xs n xs.val[i]! 1#u16 0))) * basisNumer xs n.val i

theorem basisTerm_natDegree_lt (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat)
    (hn : n.val ≤ 36) (hi : i < n.val) :
    (basisTerm xs ys n i).natDegree < n.val := by
  unfold basisTerm
  have h1 := natDegree_C_mul_le (GF16.ofU16 (gfDivV ys.val[i]! (denomV xs n xs.val[i]! 1#u16 0)))
    (basisNumer xs n.val i)
  rw [basisNumer_natDegree xs n.val i hi] at h1
  omega

/-- The `complete` output polynomial (banked `complete_prepare_eq_scaled_basis`) in `X · Qᵢ` form:
`gpoly workingᵢ (n+1) = X · basisTerm i`. -/
theorem complete_prepare_eq_X_basisTerm (coeffs : Array Std.U16 37#usize)
    (xs ys : Array Std.U16 36#usize) (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val)
    (hprep : gpoly (fun k => coeffs.val[k]!) (n.val + 1) = nodal xs n.val) :
    gf.complete coeffs xs ys n i
      ⦃ r => gpoly (fun k => r.val[k]!) (n.val + 1) = X * basisTerm xs ys n i.val ⦄ := by
  have hce := complete_prepare_eq_scaled_basis coeffs xs ys n i hn hi hprep
  apply Std.WP.spec_mono hce
  intro r hr
  rw [hr]
  unfold basisTerm
  ring

/-! ### The basis-weighted sum and the `lagrange_interpolate_loop1` driver. -/

/-- The Lagrange interpolant in numerator/weight form: `Σ_{i<m} C(scaleᵢ) · basisNumerᵢ`,
the partial sum of the per-`i` basis terms over the first `m` indices. -/
noncomputable def basisSum (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (m : Nat) : GF16[X] :=
  ∑ i ∈ Finset.range m, basisTerm xs ys n i

theorem basisSum_succ (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (m : Nat) :
    basisSum xs ys n (m + 1) = basisSum xs ys n m + basisTerm xs ys n m := by
  unfold basisSum; rw [Finset.sum_range_succ]

/-- **Value spec of the `lagrange_interpolate_loop1` driver.** For `n ≤ 36`, when `template` is
the `gf.prepare` nodal product (`gpoly template (n+1) = nodal xs n`), starting at index `i` with a
running sum `gpoly out n = basisSum xs ys n i` (the partial Lagrange interpolant over the first `i`
basis terms), the loop `lagrange_interpolate_loop1 xs ys n out template working i` (which for each
`i ≤ k < n` recomputes `complete template xs ys n k` and accumulates its `X`-shifted basis term)
produces an array whose `GF16` polynomial is the full sum `basisSum xs ys n n` — the Lagrange
interpolant `Σ_{k<n} C(scaleₖ) · basisNumerₖ`. Field-law-free: only the `GF16` CommRing. -/
theorem lagrange_interpolate_loop1_eq (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (template : Array Std.U16 37#usize) (hn : n.val ≤ 36)
    (hprep : gpoly (fun k => template.val[k]!) (n.val + 1) = nodal xs n.val) :
    ∀ (out working : Array Std.U16 37#usize) (i : Std.Usize), i.val ≤ n.val →
      gpoly (fun k => out.val[k]!) n.val = basisSum xs ys n i.val →
      gf.lagrange_interpolate_loop1 xs ys n out template working i
        ⦃ r => gpoly (fun k => r.val[k]!) n.val = basisSum xs ys n n.val ⦄ := by
  intro out working i hile hsum
  unfold gf.lagrange_interpolate_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × (Array Std.U16 37#usize) × Std.Usize =>
      n.val - s.2.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × (Array Std.U16 37#usize) × Std.Usize =>
      s.2.2.val ≤ n.val ∧ gpoly (fun k => s.1.val[k]!) n.val = basisSum xs ys n s.2.2.val)
    (post := fun r : Array Std.U16 37#usize =>
      gpoly (fun k => r.val[k]!) n.val = basisSum xs ys n n.val)
  · rintro ⟨o1, w1, i1⟩ ⟨hi1n, hsum1⟩
    simp only [gf.lagrange_interpolate_loop1.body]
    split
    · rename_i hlt
      -- working1 = complete template xs ys n i1, with polynomial X * basisTerm i1
      have hcomp := complete_prepare_eq_X_basisTerm template xs ys n i1 hn hlt hprep
      step with hcomp as ⟨working1, hworking1⟩
      -- out1 = loop1_loop0 n o1 working1 0, polynomial = basisSum i1 + basisTerm i1
      have hacc := loop1_loop0_accum n o1 working1 hn
        (basisSum xs ys n i1.val) (basisTerm xs ys n i1.val)
        (basisTerm_natDegree_lt xs ys n i1.val hn hlt) hsum1 hworking1
      step with hacc as ⟨out1, hout1⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2, basisSum_succ]
      exact hout1
    · rename_i hge
      have hie : i1.val = n.val := by scalar_tac
      rw [hie] at hsum1; exact hsum1
  · exact ⟨hile, hsum⟩

/-! ### L1. `gf.lagrange_interpolate` computes the basis-weighted sum (UNCONDITIONAL, in-boundary). -/

/-- **`gf.lagrange_interpolate` computes the Lagrange interpolant in numerator/weight form over
GF(2¹⁶)** (UNCONDITIONAL, in-boundary). For `n ≤ 36`, the extracted `gf.lagrange_interpolate xs ys n`
succeeds with a coefficient array `out` whose `GF16` polynomial `gpoly out n` equals the
basis-weighted sum

    Σ_{i<n} C(ofU16 (gfDivV ys[i] (denomV xs n xs[i] 1 0))) · ∏_{k ∈ (range n).erase i}(X − C(ofU16 xs[k]))

i.e. `Σ_i scaleᵢ · ℓ̃ᵢ` — each `gf.complete` produces `scaleᵢ · X · ℓ̃ᵢ` (the banked
`complete_prepare_eq_scaled_basis`), the `loop0`/`loop1` shift divides out the `× X` offset, and
the `loop1` driver accumulates the per-`i` numerators (`gfAddV` = `+`). Assembled from
`RsPrepareBridge.prepare_eq_nodal` (`gf.prepare` = nodal product), `RsInterp`'s
`complete`/`loop0`/`loop1_loop0` value specs, `complete_prepare_eq_scaled_basis`, the divide-by-`X`
shift `gpoly_shift_eq`, and the `lagrange_interpolate_loop1` driver. Field-law-FREE: only the
unconditional `GF16` CommRing (`hmul` discharged by Stage 2) — NO field inverse, NO irreducibility,
NO `axiom`/`sorry`/`native_decide`/`decide` over the value space. -/
theorem lagrange_interpolate_eq_basis_sum (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (hn : n.val ≤ 36) :
    gf.lagrange_interpolate xs ys n
      ⦃ r => gpoly (fun k => r.val[k]!) n.val = basisSum xs ys n n.val ⦄ := by
  unfold gf.lagrange_interpolate
  -- the all-zeros output base
  set out0 := Array.repeat 37#usize (0#u16) with hout0
  by_cases hn0 : n.val = 0
  · -- n = 0: the loop is skipped, output is all-zeros, both polynomials are 0 (empty sum/range)
    have hne : n = 0#usize := by
      apply Std.UScalar.eq_of_val_eq; simpa using hn0
    rw [if_pos hne]
    rw [Std.WP.spec_ok]
    -- gpoly _ 0 = empty sum = 0; basisSum _ 0 = empty sum = 0
    rw [hn0]
    unfold gpoly basisSum
    simp
  · -- n ≥ 1: prepare → complete₀ → loop0 → loop1
    have hne : ¬ n = 0#usize := by
      intro h; apply hn0; rw [h]; simp
    rw [if_neg hne]
    have hnpos : 0 < n.val := by omega
    -- template = prepare xs n = nodal product
    have hprep := Spqr.RsPrepareBridge.prepare_eq_nodal xs n hn
    step with hprep as ⟨template, htemplate⟩
    -- working₀ = complete template xs ys n 0 = X * basisTerm 0
    have hcomp0 := complete_prepare_eq_X_basisTerm template xs ys n 0#usize hn
      (by simpa using hnpos) htemplate
    step with hcomp0 as ⟨working0, hworking0⟩
    -- out1 = loop0 n out0 working0 0 : out1[k] = working0[k+1] for k < n
    have hloop0 := lagrange_interpolate_loop0_eq n working0 hn out0 0#usize (by simp) (by simp)
    step with hloop0 as ⟨out1, hbelow, _⟩
    -- gpoly out1 n = basisTerm 0 (divide-by-X shift)
    have hsum1 : gpoly (fun k => out1.val[k]!) n.val = basisSum xs ys n (1#usize).val := by
      have hshift : gpoly (fun k => out1.val[k]!) n.val = basisTerm xs ys n 0 := by
        apply gpoly_shift_eq (out := fun k => out1.val[k]!) (working := fun k => working0.val[k]!)
          (n := n.val) (Q := basisTerm xs ys n 0)
          (basisTerm_natDegree_lt xs ys n 0 hn hnpos) hworking0
        intro k hk
        rw [hbelow k hk, gpoly_coeff, if_pos (by omega)]
      rw [hshift]
      unfold basisSum
      rw [show (1#usize).val = 1 from rfl, Finset.sum_range_one]
    -- the loop1 driver from i = 1 with running sum basisTerm 0
    exact lagrange_interpolate_loop1_eq xs ys n template hn htemplate out1 working0 1#usize
      (by scalar_tac) hsum1

/-! ### L2 ingredient: the denominator product `denomV` over GF16.

`complete_loop0`'s accumulator `denomV xs n pix denom j` multiplies, for `j ≤ k < n` with
`pix ≠ xs[k]`, one factor `gfAddV pix xs[k] = pix ⊕ xs[k]`. Over GF16 (char 2) `pix ⊕ xs[k]`
IS `pix − xs[k]` (= `pix + xs[k]`), so the denominator is the product of the linear differences
that the Lagrange weight inverts. This is field-law-FREE (the CommRing suffices for the value). -/

/-- The per-index denominator factor over GF16: `pix ⊕ xs[k]` when `pix ≠ xs[k]`, else `1`
(the conditional multiply of `complete_loop0`). -/
noncomputable def denomFactor (xs : Array Std.U16 36#usize) (pix : Std.U16) (k : Nat) : GF16 :=
  if pix ≠ xs.val[k]! then GF16.ofU16 pix + GF16.ofU16 xs.val[k]! else 1

/-- **`denomV` is the difference product over GF16** (UNCONDITIONAL). Read into GF16,
`denomV xs n pix denom j` is `ofU16 denom · ∏_{k ∈ Ico j n} denomFactor k`, where each factor is
`pix ⊕ xs[k]` (= `pix − xs[k]` in char 2) when `pix ≠ xs[k]` and `1` otherwise — mirroring the
loop's conditional multiply exactly. -/
theorem denomV_eq_prod (xs : Array Std.U16 36#usize) (n : Std.Usize) (pix : Std.U16)
    (hn : n.val ≤ 36) :
    ∀ (d : Nat) (denom : Std.U16) (j : Nat), n.val - j = d → j ≤ n.val →
      GF16.ofU16 (denomV xs n pix denom j)
        = GF16.ofU16 denom * ∏ k ∈ Finset.Ico j n.val, denomFactor xs pix k := by
  intro d
  induction d with
  | zero =>
    intro denom j hd hj
    have hje : j = n.val := by omega
    subst hje
    rw [denomV, if_neg (by omega)]
    rw [show Finset.Ico n.val n.val = ∅ from Finset.Ico_self _]
    rw [Finset.prod_empty, mul_one]
  | succ d ih =>
    intro denom j hd hj
    have hjlt : j < n.val := by omega
    rw [denomV, if_pos (by scalar_tac)]
    -- peel the bottom factor k = j off the Ico product
    rw [Finset.prod_eq_prod_Ico_succ_bot hjlt]
    by_cases hpe : pix ≠ xs.val[j]!
    · -- conditional multiply taken: denom' = gfMulV denom (gfAddV pix xs[j])
      rw [if_pos hpe]
      rw [ih (gfMulV denom (gfAddV pix xs.val[j]!)) (j + 1) (by omega) (by omega)]
      -- ofU16 (gfMulV denom (gfAddV pix xs[j])) = ofU16 denom * (ofU16 pix + ofU16 xs[j])
      rw [← mul_eq_gfMulV, ← add_eq_gfAddV]
      unfold denomFactor
      rw [if_pos hpe]
      ring
    · -- not taken: denom unchanged
      rw [if_neg hpe]
      rw [ih denom (j + 1) (by omega) (by omega)]
      unfold denomFactor
      rw [if_neg hpe]
      ring

/-! ### L2. Identifying the basis sum with Mathlib's `Lagrange.interpolate` (CONDITIONAL on
`Irreducible POLY_poly`).

Over the field `GF16` (a field exactly when `POLY_poly` is irreducible — the documented WALL),
the basis-weighted sum `Σ_i scaleᵢ · ℓ̃ᵢ` IS Mathlib's `Lagrange.interpolate`: with nodes
`node k = ofU16 xs[k]` and values `value k = ofU16 ys[k]`, indexed by `s = Finset.range n`,

  * the denominator `denomᵢ = ∏_{k≠i}(node i − node k)` is `denomV` read through char-2 XOR=−
    and the distinct-node filter (`denomV_eq_prod`),
  * the Lagrange weight `(∏_{k≠i}(node i − node k))⁻¹` is `denomᵢ⁻¹`, so the extracted Fermat
    scale `scaleᵢ = ysᵢ · denomᵢ⁻¹` (`RsDivInverse.gf_div_eq_inv`, the field inverse) is the genuine
    Lagrange weight `valueᵢ · weightᵢ`,
  * `Lagrange.basis s node i = C(weightᵢ) · ℓ̃ᵢ` (`Lagrange.leadingCoeff_basis`), so
    `C(scaleᵢ) · ℓ̃ᵢ = C(valueᵢ) · Lagrange.basis s node i`, and summing gives `interpolate`.

The only carried algebraic premise is irreducibility (carried as `[Fact …]`, satisfiable, never an
axiom) plus the genuine distinct-nodes hypothesis. -/

open Spqr.Gf16Field (POLY_poly)
open Spqr.RsDivInverse (gf_div_eq_inv)

variable [Fact (Irreducible POLY_poly)]

/-! ### The denominator as the erased difference product (distinct nodes, char 2).

These stay over the unconditional `CommRing GF16` (subtraction `node i − node k` is the ring
operation); NO `Field GF16` instance is introduced here, so `GF16[X]` keeps a single `CommRing`
and the L2 identification can be carried out cleanly over the canonical-field carrier
`AdjoinRoot POLY_poly` (mapped via `gfRingEquiv`). -/

/-- The Lagrange node map for the extracted node array: `node k = ofU16 xs[k]` in GF16. -/
noncomputable def node (xs : Array Std.U16 36#usize) (k : Nat) : GF16 := GF16.ofU16 xs.val[k]!

/-- **The extracted denominator IS the erased difference product** (CONDITIONAL on distinct nodes).
With distinct nodes (`hdist`), `ofU16 (denomV xs n xs[i] 1 0) = ∏_{k ∈ (range n).erase i}(node i − node k)`
— the Lagrange-weight denominator. Combines `denomV_eq_prod` (the conditional-multiply product over
`Ico 0 n`), the char-2 fact `node i + node k = node i − node k` (`RsPrepareBridge.neg_eq`), and the
distinct-node fact that `xs[i] = xs[k]` (for `k < n`) iff `k = i` (so the `pix ≠ xs[k]` filter is
exactly `erase i`). -/
theorem denomV_eq_erase_prod (xs : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat)
    (hn : n.val ≤ 36) (hi : i < n.val)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b) :
    GF16.ofU16 (denomV xs n xs.val[i]! 1#u16 0)
      = ∏ k ∈ (Finset.range n.val).erase i, (node xs i - node xs k) := by
  rw [denomV_eq_prod xs n xs.val[i]! hn n.val 1#u16 0 (by omega) (by omega)]
  have h1 : GF16.ofU16 1#u16 = (1 : GF16) := one_eq.symm
  rw [h1, show Finset.Ico 0 n.val = Finset.range n.val from by rw [Finset.range_eq_Ico]]
  rw [show (1 : GF16) * (∏ k ∈ Finset.range n.val, denomFactor xs xs.val[i]! k)
      = ∏ k ∈ Finset.range n.val, denomFactor xs xs.val[i]! k from one_mul _]
  -- the product over range n with denomFactor = product over erase i of differences
  rw [← Finset.prod_erase (Finset.range n.val)
        (f := denomFactor xs xs.val[i]!) (a := i)]
  · -- now product over erase i; each factor matches node i - node k
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_erase, Finset.mem_range] at hk
    obtain ⟨hki, hkn⟩ := hk
    unfold denomFactor node
    have hne : xs.val[i]! ≠ xs.val[k]! := by
      intro h; exact hki ((hdist k i hkn hi h.symm))
    rw [if_pos hne]
    -- ofU16 xs[i] + ofU16 xs[k] = ofU16 xs[i] - ofU16 xs[k]  (char 2)
    rw [sub_eq_add_neg]
    congr 1
    exact (Spqr.RsPrepareBridge.neg_eq _).symm
  · -- the erased factor at k = i is 1 (pix = xs[i])
    unfold denomFactor
    rw [if_neg (by simp)]

/-- **The mapped denominator is the erased difference product over `AdjoinRoot`** (CONDITIONAL on
distinct nodes). Pushes `denomV_eq_erase_prod` through the ring iso `gfRingEquiv` into the field
`AdjoinRoot POLY_poly`: `gfRingEquiv (ofU16 (denomV xs n xs[i] 1 0)) = ∏_{k≠i}(phi xs[i] − phi xs[k])`.
This is the value the Lagrange weight inverts, now over the genuine field carrier. -/
theorem map_denomV_eq_erase_prod (xs : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat)
    (hn : n.val ≤ 36) (hi : i < n.val)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b) :
    Spqr.Gf16FieldInstance.gfRingEquiv (GF16.ofU16 (denomV xs n xs.val[i]! 1#u16 0))
      = ∏ k ∈ (Finset.range n.val).erase i,
          (Spqr.Gf16FieldAssembly.phi xs.val[i]! - Spqr.Gf16FieldAssembly.phi xs.val[k]!) := by
  rw [Spqr.Gf16FieldInstance.gfRingEquiv_ofU16]
  have h := congrArg Spqr.Gf16FieldInstance.gfRingEquiv (denomV_eq_erase_prod xs n i hn hi hdist)
  rw [Spqr.Gf16FieldInstance.gfRingEquiv_ofU16] at h
  rw [h, map_prod]
  apply Finset.prod_congr rfl
  intro k _
  unfold node
  rw [map_sub, Spqr.Gf16FieldInstance.gfRingEquiv_ofU16, Spqr.Gf16FieldInstance.gfRingEquiv_ofU16]

/-- **The Lagrange denominators are nonzero, DERIVED from distinct nodes** (CONDITIONAL on
`Irreducible POLY_poly` + distinct nodes). In the genuine GF(2¹⁶) field `AdjoinRoot POLY_poly`
(a field under the irreducibility `Fact`), the denominator `denomV xs n xs[i] 1 0` is nonzero:
its image under the ring iso is `∏_{k≠i}(phi xs[i] − phi xs[k])`, a product of differences of
DISTINCT field elements (`phi` injective + `hdist`), hence nonzero in the integral domain. Since
`gfRingEquiv` is injective and sends `0` to `0`, `denomV ≠ 0`. This DERIVES the `hdenom` premise
that the L2/L3 bridge headlines previously carried — dropping it as a separate assumption. -/
theorem denomV_ne_zero (xs : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat)
    (hn : n.val ≤ 36) (hi : i < n.val)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b) :
    denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16 := by
  intro hzero
  -- the image of the denominator is the erased difference product
  have hmap := map_denomV_eq_erase_prod xs n i hn hi hdist
  -- but if denomV = 0 then its image is 0
  rw [hzero] at hmap
  rw [← zero_eq, map_zero] at hmap
  -- so the product of nonzero factors is 0 — contradiction (field is a domain)
  have hprod_ne : (∏ k ∈ (Finset.range n.val).erase i,
      (Spqr.Gf16FieldAssembly.phi xs.val[i]! - Spqr.Gf16FieldAssembly.phi xs.val[k]!)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    rw [Finset.mem_erase, Finset.mem_range] at hk
    obtain ⟨hki, hkn⟩ := hk
    -- phi xs[i] ≠ phi xs[k] since xs[i] ≠ xs[k] (distinct nodes) and phi injective
    rw [sub_ne_zero]
    intro hphi
    exact hki (hdist i k hi hkn (Spqr.Gf16FieldAssembly.phi_injective hphi)).symm
  exact hprod_ne hmap.symm

/-! ### L2 (AdjoinRoot route): the basis sum maps to Mathlib's `Lagrange.interpolate`.

To avoid the `GF16[X]` Field/CommRing typeclass diamond, we push `basisSum` through the ring iso
`gfRingEquiv : GF16 ≃+* AdjoinRoot POLY_poly` (a `Polynomial.map`), landing in `(AdjoinRoot POLY_poly)[X]`
where there is a SINGLE canonical `Field` instance (`AdjoinRoot.instField`). Over that carrier we match
the mapped basis sum against `Lagrange.interpolate` with nodes `rnode k = phi xs[k]` and values
`rvalue k = phi ys[k]`. -/

/-- The image of `basisNumer` under the ring iso is the basis numerator over `AdjoinRoot`:
`∏_{k≠i}(X − C(phi xs[k]))`. -/
theorem map_basisNumer (xs : Array Std.U16 36#usize) (n i : Nat) :
    Polynomial.map Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom (basisNumer xs n i)
      = ∏ k ∈ (Finset.range n).erase i, (X - C (Spqr.Gf16FieldAssembly.phi xs.val[k]!)) := by
  unfold basisNumer
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro k _
  congr 2

/-- **`Lagrange.basis` over `AdjoinRoot` factors as weight · numerator.** -/
theorem lagrange_basis_adjoin (xs : Array Std.U16 36#usize) (n i : Nat) :
    Lagrange.basis (Finset.range n) (fun k => Spqr.Gf16FieldAssembly.phi xs.val[k]!) i
      = C ((∏ k ∈ (Finset.range n).erase i,
              (Spqr.Gf16FieldAssembly.phi xs.val[i]! - Spqr.Gf16FieldAssembly.phi xs.val[k]!))⁻¹)
        * ∏ k ∈ (Finset.range n).erase i, (X - C (Spqr.Gf16FieldAssembly.phi xs.val[k]!)) := by
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod, ← Finset.prod_inv_distrib]

/-- **The mapped per-`i` basis term IS the Lagrange basis term over `AdjoinRoot`** (CONDITIONAL on
irreducibility + distinct nodes). Mapping `basisTerm xs ys n i` through the ring iso `gfRingEquiv`
gives `C(phi ys[i]) · Lagrange.basis (range n) (phi ∘ xs) i`. Combines `gf_div_eq_inv` (the scale is
the field inverse), `denomV_eq_erase_prod` (the denominator is the erased difference product, mapped),
`lagrange_basis_adjoin`, and `map_basisNumer`. -/
theorem map_basisTerm_eq_lagrange (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (i : Nat)
    (hn : n.val ≤ 36) (hi : i < n.val)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdenom : denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16) :
    Polynomial.map Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom (basisTerm xs ys n i)
      = C (Spqr.Gf16FieldAssembly.phi ys.val[i]!)
        * Lagrange.basis (Finset.range n.val) (fun k => Spqr.Gf16FieldAssembly.phi xs.val[k]!) i := by
  unfold basisTerm
  rw [Polynomial.map_mul, Polynomial.map_C, map_basisNumer]
  rw [lagrange_basis_adjoin]
  -- map (C scale) = C (phi scale) ; reassociate so the weight folds into scale.
  rw [show Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom (GF16.ofU16 (gfDivV ys.val[i]! (denomV xs n xs.val[i]! 1#u16 0)))
        = Spqr.Gf16FieldInstance.gfRingEquiv (GF16.ofU16 (gfDivV ys.val[i]! (denomV xs n xs.val[i]! 1#u16 0)))
      from rfl]
  -- gfRingEquiv (ofU16 (gfDivV ys[i] denom)) = phi ys[i] * (phi denom)⁻¹  (the field inverse)
  rw [gf_div_eq_inv ys.val[i]! _ hdenom]
  -- (phi denom)⁻¹ = (∏ erase (phi xs[i] - phi xs[k]))⁻¹  (mapped denominator)
  rw [map_denomV_eq_erase_prod xs n i hn hi hdist, Spqr.Gf16FieldInstance.gfRingEquiv_ofU16]
  -- C (phi ys[i] * weight) = C (phi ys[i]) * C weight ; reassociate
  rw [map_mul]
  ring

/-- **`gf.lagrange_interpolate` (mapped to `AdjoinRoot`) IS Mathlib's `Lagrange.interpolate`**
(CONDITIONAL on `Irreducible POLY_poly` + distinct nodes). Mapping the basis sum
`basisSum xs ys n n` through the ring iso `gfRingEquiv` into `(AdjoinRoot POLY_poly)[X]` gives exactly
`Lagrange.interpolate (range n) (phi ∘ xs) (phi ∘ ys)` — the genuine Lagrange interpolant of the
decoded samples over the GF(2¹⁶) field. Sums `map_basisTerm_eq_lagrange` over `i < n`. -/
theorem map_basisSum_eq_interpolate (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdenom : ∀ i, i < n.val → denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16) :
    Polynomial.map Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom (basisSum xs ys n n.val)
      = Lagrange.interpolate (Finset.range n.val) (fun k => Spqr.Gf16FieldAssembly.phi xs.val[k]!)
          (fun k => Spqr.Gf16FieldAssembly.phi ys.val[k]!) := by
  unfold basisSum
  rw [Polynomial.map_sum]
  rw [Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact map_basisTerm_eq_lagrange xs ys n i hn hi hdist (hdenom i hi)

/-! ### L2 HEADLINE. `gf.lagrange_interpolate` computes Mathlib's `Lagrange.interpolate`. -/

/-- **`gf.lagrange_interpolate` reconstructs Mathlib's `Lagrange.interpolate` over GF(2¹⁶)**
(CONDITIONAL on `Irreducible POLY_poly` + distinct nodes — strictly weaker than the prior
`hmul + Irreducible` premise, since `hmul` is discharged by Stage 2). For `n ≤ 36`, with distinct
nodes (`hdist`) and nonzero Lagrange denominators (`hdenom`), the extracted `gf.lagrange_interpolate
xs ys n` succeeds with a coefficient array `out` whose `GF16` coefficient polynomial `gpoly out n`,
MAPPED into the genuine field `AdjoinRoot POLY_poly` through the ring iso `gfRingEquiv`, equals
Mathlib's Lagrange interpolant

    Lagrange.interpolate (range n) (k ↦ phi xs[k]) (k ↦ phi ys[k])

— the unique degree-`<n` polynomial through the decoded samples. This is the interpolation-correctness
identification the full `decode ∘ encode = id` bridge (`RsCapstone.hbridge`) rests on: the SPQR
`prepare`/`complete`/`divFold` machinery (L1: `gpoly out n = Σ scaleᵢ · ℓ̃ᵢ`, UNCONDITIONAL) computes
exactly the Lagrange basis-weighted sum, with `gfDivV` read as the field inverse
(`RsDivInverse.gf_div_eq_inv`) and the denominator as the erased difference product
(`denomV_eq_erase_prod`). Mentions `gf.lagrange_interpolate` (via L1 and the banked `complete`/`prepare`
specs). The only carried algebraic premise is irreducibility, plus the genuine non-degeneracy
hypotheses (distinct nodes, nonzero denominators) — never an axiom. -/
theorem lagrange_interpolate_eq_interpolate (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdenom : ∀ i, i < n.val → denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16) :
    gf.lagrange_interpolate xs ys n
      ⦃ r => Polynomial.map Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom
                 (gpoly (fun k => r.val[k]!) n.val)
               = Lagrange.interpolate (Finset.range n.val)
                   (fun k => Spqr.Gf16FieldAssembly.phi xs.val[k]!)
                   (fun k => Spqr.Gf16FieldAssembly.phi ys.val[k]!) ⦄ := by
  have hbs := lagrange_interpolate_eq_basis_sum xs ys n hn
  apply Std.WP.spec_mono hbs
  intro r hr
  rw [hr]
  exact map_basisSum_eq_interpolate xs ys n hn hdist hdenom

/-! ### L3 HEADLINE. The full `hbridge` premise, DISCHARGED conditional on `Irreducible POLY_poly`.

Composing the EVALUATION side (`RsEvalBridge.decode_value_at_eval`, UNCONDITIONAL: the decoder
re-evaluates its reconstructed coefficient polynomial `gpoly poly n` at `x` over `GF16`) with the
INTERPOLATION side (L2 `lagrange_interpolate_eq_interpolate`, conditional on irreducibility: that
mapped coefficient polynomial IS Mathlib's `Lagrange.interpolate`), through the ring-hom
eval-commute `gfRingEquiv (eval r p) = eval (gfRingEquiv r) (p.map gfRingEquiv)`. This is exactly the
`hbridge` premise of `RsCapstone.decode_value_at_roundtrip` / `RsFieldBridge.decode_value_at_roundtrip_gf16`
(at `F = AdjoinRoot POLY_poly`, `dec = φ`, nodes `φ ∘ xs`, samples `ys`), so it is now a DERIVED fact
under irreducibility + non-degeneracy — no longer an assumed premise. -/

open Spqr.Gf16FieldAssembly (phi)
open Spqr.Gf16FieldInstance (gfRingEquiv gfRingEquiv_ofU16)

/-- **The interpolation-correctness bridge `hbridge`, DISCHARGED** (CONDITIONAL on
`Irreducible POLY_poly` + distinct nodes + nonzero denominators — strictly weaker than the prior
`hmul + Irreducible` premise, `hmul` discharged by Stage 2). For `n ≤ 36`, the extracted
`gf.decode_value_at xs ys n x`, decoded through the genuine GF(2¹⁶) embedding `φ = mk ∘ toPoly`,
equals `eval (φ x) (Lagrange.interpolate (range n) (k ↦ φ xs[k]) (k ↦ φ ys[k]))` — i.e. the decoder
evaluates Mathlib's Lagrange interpolant of the `φ`-decoded samples at the `φ`-decoded query point.

Mentions `gf.decode_value_at` / `gf.lagrange_interpolate`. Assembled by composing the UNCONDITIONAL
evaluation half `RsEvalBridge.decode_value_at_eval` (decode = `eval (ofU16 x) (gpoly poly n)`) with
the L2 interpolation half `lagrange_interpolate_eq_interpolate` (map of `gpoly poly n` through the
ring iso = `Lagrange.interpolate`), via the eval-commutes-with-ring-hom identity
`gfRingEquiv (eval r p) = eval (gfRingEquiv r) (p.map gfRingEquiv)`. This is precisely the `hbridge`
premise of `RsCapstone.decode_value_at_roundtrip` instantiated at the real field carrier
`AdjoinRoot POLY_poly` with `dec = φ`; it is therefore now DERIVED, not assumed. NO `axiom`, NO
`sorry`, NO `native_decide`. The only carried algebraic premise is `Irreducible POLY_poly`, plus the
genuine non-degeneracy hypotheses (distinct nodes, nonzero denominators) — never an axiom. -/
theorem decode_value_at_eval_eq_interpolate (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (x : Std.U16) (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdenom : ∀ i, i < n.val → denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v))
      = .ok (eval (phi x)
          (Lagrange.interpolate (Finset.range n.val)
            (fun k => phi xs.val[k]!) (fun k => phi ys.val[k]!))) := by
  -- (A) evaluation side: decode_value_at = .ok r, ofU16 r = eval (ofU16 x) (gpoly poly n)
  obtain ⟨r, hdec, poly, hpolyA, hevalA⟩ :=
    Std.WP.spec_imp_exists (Spqr.RsEvalBridge.decode_value_at_eval xs ys n x hn)
  -- (B) interpolation side on that same `poly`
  obtain ⟨poly', hpolyB, hmapB⟩ :=
    Std.WP.spec_imp_exists (lagrange_interpolate_eq_interpolate xs ys n hn hdist hdenom)
  -- the two `poly` agree (both are the value of gf.lagrange_interpolate)
  have hpoly : poly = poly' := by
    rw [hpolyA] at hpolyB; exact (Std.Result.ok.injEq _ _).mp hpolyB
  subst hpoly
  -- reduce the bind: decode_value_at = .ok r
  rw [hdec]
  simp only [Std.bind_tc_ok]
  congr 1
  -- phi r = gfRingEquiv (ofU16 r) ; use (A) then eval-commute then (B)
  have hphir : phi r = gfRingEquiv (Spqr.Gf16FieldInstance.GF16.ofU16 r) := (gfRingEquiv_ofU16 r).symm
  rw [hphir, hevalA]
  -- gfRingEquiv (eval r p) = eval (gfRingEquiv r) (map gfRingEquiv p)  (eval commutes with the ring hom)
  have hcommute : ∀ (p : GF16[X]) (z : GF16),
      gfRingEquiv.toRingHom (eval z p)
        = eval (gfRingEquiv.toRingHom z) (Polynomial.map gfRingEquiv.toRingHom p) := by
    intro p z
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval_map]
  -- gfRingEquiv x = gfRingEquiv.toRingHom x  (defeq coercions)
  show gfRingEquiv.toRingHom (eval (Spqr.Gf16FieldInstance.GF16.ofU16 x)
        (gpoly (fun k => poly.val[k]!) n.val)) = _
  rw [hcommute]
  -- the eval point: gfRingEquiv.toRingHom (ofU16 x) = phi x ; and the mapped poly = interpolate (B)
  rw [show (gfRingEquiv.toRingHom (Spqr.Gf16FieldInstance.GF16.ofU16 x))
        = gfRingEquiv (Spqr.Gf16FieldInstance.GF16.ofU16 x) from rfl, gfRingEquiv_ofU16]
  rw [hmapB]

/-! ### L2/L3 with `hdenom` DERIVED (CONDITIONAL on `Irreducible POLY_poly` + distinct nodes ONLY).

The prior headlines carried the nonzero-Lagrange-denominator hypothesis `hdenom` as a separate
premise. In the genuine GF(2¹⁶) field it FOLLOWS from distinct nodes (`denomV_ne_zero`: a product
of differences of distinct field elements is nonzero in an integral domain). These upgraded
headlines DROP `hdenom`, carrying only irreducibility (the WALL) and the genuine distinct-nodes
hypothesis — a strict reduction of the assumption surface. -/

/-- **`gf.lagrange_interpolate` reconstructs Mathlib's `Lagrange.interpolate`, `hdenom` DERIVED**
(CONDITIONAL on `Irreducible POLY_poly` + distinct nodes ONLY). Identical to
`lagrange_interpolate_eq_interpolate` but with the nonzero-denominator premise `hdenom` DISCHARGED
from `hdist` via `denomV_ne_zero` (the Lagrange denominators are products of differences of distinct
nodes, nonzero in the field). Mentions `gf.lagrange_interpolate`. The only carried algebraic premise
is irreducibility; the only non-degeneracy premise is distinct nodes. NO `axiom`/`sorry`/`native_decide`. -/
theorem lagrange_interpolate_eq_interpolate_of_dist (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b) :
    gf.lagrange_interpolate xs ys n
      ⦃ r => Polynomial.map Spqr.Gf16FieldInstance.gfRingEquiv.toRingHom
                 (gpoly (fun k => r.val[k]!) n.val)
               = Lagrange.interpolate (Finset.range n.val)
                   (fun k => Spqr.Gf16FieldAssembly.phi xs.val[k]!)
                   (fun k => Spqr.Gf16FieldAssembly.phi ys.val[k]!) ⦄ :=
  lagrange_interpolate_eq_interpolate xs ys n hn hdist
    (fun i hi => denomV_ne_zero xs n i hn hi hdist)

/-- **The interpolation-correctness bridge `hbridge`, DISCHARGED with `hdenom` DERIVED** (CONDITIONAL
on `Irreducible POLY_poly` + distinct nodes ONLY). Identical to `decode_value_at_eval_eq_interpolate`
but the nonzero-denominator premise is DISCHARGED from `hdist` via `denomV_ne_zero`. This is exactly
the `hbridge` premise of `RsCapstone.decode_value_at_roundtrip` / `RsFieldBridge.*_gf16` at
`F = AdjoinRoot POLY_poly`, `dec = φ`, now derived from irreducibility + distinct nodes alone.
Mentions `gf.decode_value_at` / `gf.lagrange_interpolate`. NO `axiom`/`sorry`/`native_decide`. -/
theorem decode_value_at_eval_eq_interpolate_of_dist (xs ys : Array Std.U16 36#usize) (n : Std.Usize)
    (x : Std.U16) (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v))
      = .ok (eval (phi x)
          (Lagrange.interpolate (Finset.range n.val)
            (fun k => phi xs.val[k]!) (fun k => phi ys.val[k]!))) :=
  decode_value_at_eval_eq_interpolate xs ys n x hn hdist
    (fun i hi => denomV_ne_zero xs n i hn hi hdist)

end Spqr.RsLagrangeBridge
