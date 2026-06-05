/-
  SPQR Reed–Solomon codec — Layer C, the EVALUATION bridge over the genuine GF(2¹⁶) ring.

  ## What this file establishes (genuine, IN-BOUNDARY, UNCONDITIONAL — no irreducibility)

  The decoder's re-evaluation kernel `gf.compute_at` (hence `gf.decode_value_at`) does NOT need
  the field structure — only the COMMUTATIVE RING. Stage 2 (`Gf16ReduceTable`) discharged `hmul`
  unconditionally, so the extracted `(gfAddV, gfMulV, 0#u16, 1#u16)` IS a `CommRing` (the `GF16`
  instance, transported from `AdjoinRoot POLY_poly` through the bijection `φ`, with `+`/`*` the
  extracted ops — `Gf16FieldInstance.add_eq_gfAddV`/`mul_eq_gfMulV`). Over that ring we close the
  EVALUATION half of the interpolation bridge UNCONDITIONALLY:

    E1. **`compute_at`'s power table is genuine field powers.** The squaring recurrence
        `powers[j] = gfMulV powers[j/2] powers[j/2+j%2]` (banked `RsBridge.compute_at_loop0`)
        with `powers[0]=1`, `powers[1]=x` builds EXACTLY `powers[j] = x^j` in `GF16` — proved by
        strong induction using ONLY the `CommRing` law `x^(a+b) = x^a*x^b` (no irreducibility,
        no `hmul` as a free premise — it is discharged). (`powerTable_eq_pow`)

    E2. **`dotV` is `Polynomial.eval` of the coefficient polynomial.** The banked dot-product
        recurrence `RsBridge.dotV coeffs powers len 0 0` equals `Σ_{k<len} coeffs[k] ⊗ powers[k]`,
        which under E1 is `eval (ofU16 x) (gpoly coeffs len)` where `gpoly` is the coefficient-array
        polynomial `∑_{k<len} C(ofU16 coeffs[k]) X^k`. (`dotV_eq_eval`)

    E3. **`gf.compute_at` evaluates the coefficient polynomial over `GF16`** (UNCONDITIONAL,
        in-boundary). `gf.compute_at coeffs len x`, read into `GF16`, equals
        `eval (ofU16 x) (gpoly coeffs len)`. (`compute_at_eval`)

    E4. **`gf.decode_value_at` evaluates the RECONSTRUCTED polynomial over `GF16`** (UNCONDITIONAL,
        in-boundary). `gf.decode_value_at xs ys n x` = `eval (ofU16 x) (gpoly poly n)` where `poly`
        is the value of the extracted `gf.lagrange_interpolate xs ys n`. This is the
        "decode = EVALUATE(reconstructed poly)" identity over the genuine ring — the structural
        `decode_value_at_eq` upgraded from a raw `dotV` to a `Polynomial.eval`. (`decode_value_at_eval`)

  These mention `gf.compute_at` / `gf.decode_value_at` / `gf.lagrange_interpolate` (via `dotV` and
  the power recurrence), so they are IN-BOUNDARY headlines about the extracted code. NO `axiom`,
  NO `sorry`, NO `native_decide`, NO `decide` over the value space, NO irreducibility.

  ## What this file does NOT do (the honest open obligation)

  - It does NOT identify the reconstructed coefficient polynomial `gpoly poly n` with Mathlib's
    `Lagrange.interpolate` of the samples. THAT is the remaining interpolation half: it needs
    `gfDivV` read as the field inverse (the Fermat-ladder value spec) and the basis-polynomial
    matching — both requiring `Irreducible POLY_poly` (the WALL) to get the genuine `Field`. So the
    `hbridge` premise of `RsCapstone.decode_value_at_roundtrip` is NOT discharged here; this file
    closes the EVALUATION side that connects the decoder output to `Polynomial.eval` over the
    genuine GF(2¹⁶) commutative ring, which is the prerequisite the evaluation step of `hbridge`
    rests on.
-/
import Demos.Spqr.RsCapstone
import Demos.Spqr.Gf16FieldInstance

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsBridge (dotV compute_at_eq)
open Spqr.Gf16FieldInstance (GF16 add_eq_gfAddV mul_eq_gfMulV zero_eq one_eq)
open Polynomial

namespace Spqr.RsEvalBridge

/-! ### The coefficient-array polynomial over `GF16`. -/

/-- The `GF16` polynomial denoted by a coefficient-reading function `c : Nat → U16` truncated to
the first `len` coefficients: `∑_{k<len} C(ofU16 (c k)) * X^k`. -/
noncomputable def gpoly (c : Nat → Std.U16) (len : Nat) : GF16[X] :=
  ∑ k ∈ Finset.range len, C (GF16.ofU16 (c k)) * X ^ k

/-- Evaluating `gpoly` at a point: `eval p (gpoly c len) = ∑_{k<len} (ofU16 (c k)) * p^k`. -/
theorem eval_gpoly (c : Nat → Std.U16) (len : Nat) (p : GF16) :
    eval p (gpoly c len) = ∑ k ∈ Finset.range len, GF16.ofU16 (c k) * p ^ k := by
  unfold gpoly
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-! ### E1. The power table is genuine field powers `x^j` in `GF16`. -/

/-- **The squaring-recurrence power table computes genuine field powers.** If `powers[0] = 1`,
`powers[1] = x`, and for `2 ≤ j < len` the squaring recurrence
`powers[j] = gfMulV powers[j/2] powers[j/2 + j%2]` holds, then for every `j < len`,
`ofU16 powers[j] = (ofU16 x)^j` in `GF16`. UNCONDITIONAL — uses only the `CommRing` law
`x^(a+b) = x^a * x^b` (`hmul` is discharged by Stage 2; no irreducibility). -/
theorem powerTable_eq_pow (powers : Array Std.U16 37#usize) (x : Std.U16) (len : Nat)
    (hp0 : powers.val[0]! = 1#u16) (hp1 : powers.val[1]! = x)
    (hrec : ∀ j, 2 ≤ j → j < len →
      powers.val[j]! = gfMulV powers.val[j / 2]! powers.val[j / 2 + j % 2]!) :
    ∀ j, j < len → GF16.ofU16 powers.val[j]! = (GF16.ofU16 x) ^ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    match j, hj with
    | 0, _ => rw [hp0, ← one_eq, pow_zero]
    | 1, _ => rw [hp1, pow_one]
    | (m + 2), hj =>
      have hjge : 2 ≤ m + 2 := by omega
      rw [hrec (m + 2) hjge hj]
      rw [← mul_eq_gfMulV]
      -- the two read indices are < j, so the IH applies
      have h1 : (m + 2) / 2 < m + 2 := by omega
      have h2 : (m + 2) / 2 + (m + 2) % 2 < m + 2 := by omega
      rw [ih ((m + 2) / 2) h1 (by omega), ih ((m + 2) / 2 + (m + 2) % 2) h2 (by omega)]
      rw [← pow_add]
      congr 1
      omega

/-! ### E2. `dotV` is `Polynomial.eval` of the coefficient polynomial. -/

/-- `dotV` accumulated from `out` at index `k`, read into `GF16`, equals
`ofU16 out + ∑_{i < len - k} (ofU16 coeffs[k+i]) * (ofU16 powers[k+i])`. The general accumulator
form that drives the induction. UNCONDITIONAL. -/
theorem dotV_acc (coeffs powers : Array Std.U16 37#usize) (len : Std.Usize)
    (out : Std.U16) (k : Nat) (hk : k ≤ len.val) :
    GF16.ofU16 (dotV coeffs powers len out k)
      = GF16.ofU16 out
        + ∑ i ∈ Finset.range (len.val - k),
            GF16.ofU16 coeffs.val[k + i]! * GF16.ofU16 powers.val[k + i]! := by
  -- induct on the number of remaining steps `len - k`
  have hmeas : ∀ d k out, len.val - k = d → k ≤ len.val →
      GF16.ofU16 (dotV coeffs powers len out k)
        = GF16.ofU16 out
          + ∑ i ∈ Finset.range (len.val - k),
              GF16.ofU16 coeffs.val[k + i]! * GF16.ofU16 powers.val[k + i]! := by
    intro d
    induction d with
    | zero =>
      intro k out hd hk
      have hke : k = len.val := by omega
      subst hke
      rw [dotV, if_neg (by omega)]
      simp
    | succ d ih =>
      intro k out hd hk
      have hklt : k < len.val := by omega
      rw [dotV, if_pos hklt]
      rw [ih (k + 1) (gfAddV out (gfMulV coeffs.val[k]! powers.val[k]!)) (by omega) (by omega)]
      rw [← add_eq_gfAddV, ← mul_eq_gfMulV]
      -- peel the bottom term (i = 0) off the range sum on the RHS
      have hlen : len.val - k = (len.val - (k + 1)) + 1 := by omega
      rw [hlen, Finset.sum_range_succ']
      -- the shifted sum on the RHS equals the IH sum S'
      have hshift : (∑ i ∈ Finset.range (len.val - (k + 1)),
            GF16.ofU16 coeffs.val[k + (i + 1)]! * GF16.ofU16 powers.val[k + (i + 1)]!)
          = ∑ i ∈ Finset.range (len.val - (k + 1)),
            GF16.ofU16 coeffs.val[(k + 1) + i]! * GF16.ofU16 powers.val[(k + 1) + i]! := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show k + (i + 1) = (k + 1) + i by omega]
      rw [hshift, Nat.add_zero]
      -- both sides are `(O + T) + S` vs `O + (S + T)`; close by an abstract add identity
      have hreassoc : ∀ O T S : GF16, O + T + S = O + (S + T) := by
        intro O T S; rw [add_assoc, add_comm T S]
      exact hreassoc _ _ _
  exact hmeas (len.val - k) k out rfl hk

/-- **`dotV` is `Polynomial.eval` of the coefficient polynomial.** The full dot product
`dotV coeffs powers len 0 0`, read into `GF16`, equals `eval (ofU16 x) (gpoly coeffs len)`
PROVIDED the power table is the genuine powers `ofU16 powers[k] = (ofU16 x)^k` for `k < len`.
UNCONDITIONAL. -/
theorem dotV_eq_eval (coeffs powers : Array Std.U16 37#usize) (len : Std.Usize) (x : Std.U16)
    (hpow : ∀ k, k < len.val → GF16.ofU16 powers.val[k]! = (GF16.ofU16 x) ^ k) :
    GF16.ofU16 (dotV coeffs powers len 0#u16 0)
      = eval (GF16.ofU16 x) (gpoly (fun k => coeffs.val[k]!) len.val) := by
  rw [dotV_acc coeffs powers len 0#u16 0 (by omega)]
  rw [← zero_eq]
  simp only [zero_add, Nat.sub_zero, Nat.zero_add]
  rw [eval_gpoly]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [hpow i hi]

/-! ### E3. `gf.compute_at` evaluates the coefficient polynomial over `GF16`. -/

/-- **`gf.compute_at` is `Polynomial.eval` of the coefficient polynomial over `GF16`**
(UNCONDITIONAL, in-boundary). For `len ≤ 37`, `gf.compute_at coeffs len x` succeeds with a value
`r` such that, read into `GF16`, `ofU16 r = eval (ofU16 x) (gpoly coeffs len)` — the decoder's
evaluation kernel genuinely evaluates the coefficient polynomial at `x` over the GF(2¹⁶)
commutative ring. Assembled from the banked `RsBridge.compute_at_eq` (power-table + dot-product
value spec), `powerTable_eq_pow` (the squaring recurrence builds genuine powers), and
`dotV_eq_eval`. NO field inverse, NO irreducibility — only the unconditional `CommRing`. -/
theorem compute_at_eval (coeffs : Array Std.U16 37#usize) (len : Std.Usize) (x : Std.U16)
    (hlen : len.val ≤ 37) :
    gf.compute_at coeffs len x
      ⦃ r => GF16.ofU16 r = eval (GF16.ofU16 x) (gpoly (fun k => coeffs.val[k]!) len.val) ⦄ := by
  have hce := compute_at_eq coeffs len x hlen
  apply Std.WP.spec_mono hce
  rintro r ⟨powers, hp0, hp1, hrec, hr⟩
  -- the power table is genuine powers of `x`
  have hpow : ∀ k, k < len.val → GF16.ofU16 powers.val[k]! = (GF16.ofU16 x) ^ k :=
    powerTable_eq_pow powers x len.val hp0 hp1 (fun j hj2 hjlen => hrec j hj2 hjlen)
  rw [hr]
  exact dotV_eq_eval coeffs powers len x hpow

/-! ### E4. `gf.decode_value_at` evaluates the reconstructed polynomial over `GF16`. -/

/-- **`gf.decode_value_at` evaluates the RECONSTRUCTED interpolant over `GF16`** (UNCONDITIONAL,
in-boundary). For `n ≤ 36`, `gf.decode_value_at xs ys n x` succeeds, and there is a coefficient
array `poly` — the value of the extracted `gf.lagrange_interpolate xs ys n` — such that, read into
`GF16`, the result is `eval (ofU16 x) (gpoly poly n)`: the decoder reconstructs the coefficient
polynomial `poly` from the samples and RE-EVALUATES it at `x` over the GF(2¹⁶) commutative ring.

This upgrades the structural `RsCapstone.decode_value_at_eq` (which exposed only the raw `dotV`)
to a genuine `Polynomial.eval`. The remaining open obligation is to identify `gpoly poly n` with
Mathlib's `Lagrange.interpolate` of the samples — that needs `gfDivV` as the field inverse and the
basis-polynomial matching, both gated on `Irreducible POLY_poly`. NO field inverse here, NO
irreducibility — only the unconditional `CommRing`. -/
theorem decode_value_at_eval (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    (hn : n.val ≤ 36) :
    gf.decode_value_at xs ys n x
      ⦃ r => ∃ poly : Array Std.U16 37#usize,
               gf.lagrange_interpolate xs ys n = .ok poly ∧
               GF16.ofU16 r = eval (GF16.ofU16 x) (gpoly (fun k => poly.val[k]!) n.val) ⦄ := by
  unfold gf.decode_value_at
  obtain ⟨poly, hpoly, -⟩ :=
    Std.WP.spec_imp_exists (Spqr.Gf.lagrange_interpolate_total xs ys n hn)
  rw [hpoly]
  simp only [Std.bind_tc_ok]
  have hce := compute_at_eval poly n x (by scalar_tac)
  apply Std.WP.spec_mono hce
  rintro r hr
  exact ⟨poly, rfl, hr⟩
