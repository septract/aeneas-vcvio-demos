/-
  SPQR Reed–Solomon codec — Layer C, the PREPARE bridge: the extracted `gf.prepare`
  builds the master nodal polynomial `∏_{i<n}(X − xs[i])` over the genuine GF(2¹⁶) ring.

  ## What this file establishes (genuine, IN-BOUNDARY, UNCONDITIONAL — no irreducibility)

  `RsInterp.prepare_eq` characterized `gf.prepare xs n` as the iterated window-fold
  `prepareFoldFn xs n (prepareInit n) 0` (each iteration one `mult_xdiff_trailing` =
  one `(X − xs[i])` multiply in the leading-coefficient-first layout). This file closes
  the polynomial-algebra half: that fold, read into the GF(2¹⁶) commutative ring `GF16`
  via the coefficient-array polynomial `gpoly`, IS the nodal product `∏_{i<n}(X − xs[i])`.

  Because Stage 2 (`Gf16ReduceTable`) discharged `hmul`, `(gfAddV, gfMulV, 0#u16, 1#u16)`
  is UNCONDITIONALLY a `CommRing` (the `GF16` instance), and `gfAddV` = `+`, `gfMulV` = `*`
  (`Gf16FieldInstance`). In characteristic two, the loop's XOR carry `c j ⊕ xs[i]·c(j+1)`
  is exactly the subtraction `c j − xs[i]·c(j+1)` that polynomial multiplication by
  `(X − xs[i])` performs in the trailing-window layout.

    P1. **`gf.prepare` computes the nodal product** (`prepare_eq_nodal`, UNCONDITIONAL,
        in-boundary). For `n ≤ 36`, `gf.prepare xs n` succeeds with a coefficient array
        `p` whose GF16 polynomial `gpoly p (n+1)` equals `∏_{i<n}(X − C(ofU16 xs[i]))`.

  This mentions `gf.prepare` (via the banked `prepareFoldFn`/`prepare_eq`), so it is an
  in-boundary headline about the extracted code. NO `axiom`, NO `sorry`, NO `native_decide`,
  NO `decide` over the value space, NO irreducibility — only the unconditional `CommRing`.

  ## What this file does NOT do (the honest open obligation)

  - It does NOT identify `gf.complete`/`gf.lagrange_interpolate` with the Lagrange basis
    polynomials (that is the next layer: it needs `gfDivV` read as the field inverse —
    banked in `RsDivInverse` conditional on `Irreducible POLY_poly` — and the basis-sum
    matching). The nodal product `∏(X − xs[i])` proved here is the master polynomial the
    Lagrange basis `ℓ_i = ∏_{j≠i}(X − xs[j])` is built from by dividing out one factor.
-/
import Demos.Spqr.RsInterp
import Demos.Spqr.RsEvalBridge

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsInterp (xdiffStepFn prepareFoldFn prepareInit prepare_eq)
open Spqr.RsEvalBridge (gpoly eval_gpoly)
open Spqr.Gf16FieldInstance (GF16 add_eq_gfAddV mul_eq_gfMulV zero_eq one_eq)
open Polynomial

namespace Spqr.RsPrepareBridge

/-! ### The GF16 coefficient polynomial of a coefficient function, and char-2 facts. -/

/-- The `xdiffStepFn` window-update, read into GF16: in characteristic two the XOR
`^^^` IS the ring addition (`add_eq_gfAddV`), and `gfMulV` IS the ring multiply
(`mul_eq_gfMulV`). -/
theorem ofU16_xdiffStepFn (len start : Nat) (difference : Std.U16) (c : Nat → Std.U16) (j : Nat) :
    GF16.ofU16 (xdiffStepFn len start difference c j)
      = if start - 1 ≤ j ∧ j < len - 1 then
          GF16.ofU16 (c j) + GF16.ofU16 (c (j + 1)) * GF16.ofU16 difference
        else GF16.ofU16 (c j) := by
  unfold xdiffStepFn
  split
  · rw [show (c j ^^^ gfMulV (c (j + 1)) difference)
        = gfAddV (c j) (gfMulV (c (j + 1)) difference) from rfl]
    rw [← add_eq_gfAddV, ← mul_eq_gfMulV]
  · rfl

/-- `GF16` is nontrivial (`0 ≠ 1`): `GF16.ofU16` is the identity on the underlying `U16`, and
`0#u16 ≠ 1#u16`. Needed for `natDegree_X_sub_C` (which requires `[Nontrivial R]`). -/
instance : Nontrivial GF16 :=
  ⟨0, 1, by
    rw [Spqr.Gf16FieldInstance.zero_eq, Spqr.Gf16FieldInstance.one_eq]
    intro h
    have : (0#u16 : Std.U16) = 1#u16 := h
    exact absurd this (by decide)⟩

/-- `ofU16 a + ofU16 a = 0` over `GF16`: `gfAddV a a = 0#u16` (XOR of a word with itself),
transported by `add_eq_gfAddV`; then `ofU16 0 = 0`. -/
theorem ofU16_add_self (a : Std.U16) : GF16.ofU16 a + GF16.ofU16 a = 0 := by
  rw [add_eq_gfAddV, Spqr.Gf16Field.gfAddV_self, ← Spqr.Gf16FieldInstance.zero_eq]

/-- `GF16` has characteristic two: `x + x = 0` for every element (every `GF16` value is
`ofU16` of its underlying word, and `ofU16 a + ofU16 a = 0`). -/
theorem add_self (x : GF16) : x + x = 0 := by
  rw [← GF16.ofU16_toU16 x]; exact ofU16_add_self x.toU16

/-- In characteristic two, negation is the identity on `GF16`. -/
theorem neg_eq (x : GF16) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self x)

/-! ### The nodal product `∏_{i<n}(X − xs[i])` over GF16. -/

/-- The master nodal polynomial `∏_{k<m}(X − C(ofU16 xs[k]))` over GF16: the product of the
linear factors at the first `m` nodes. Monic of degree `m`. -/
noncomputable def nodal (xs : Array Std.U16 36#usize) (m : Nat) : GF16[X] :=
  ∏ k ∈ Finset.range m, (X - C (GF16.ofU16 xs.val[k]!))

@[simp] theorem nodal_zero (xs : Array Std.U16 36#usize) : nodal xs 0 = 1 := by
  unfold nodal; simp

theorem nodal_succ (xs : Array Std.U16 36#usize) (m : Nat) :
    nodal xs (m + 1) = nodal xs m * (X - C (GF16.ofU16 xs.val[m]!)) := by
  unfold nodal; rw [Finset.prod_range_succ]

theorem nodal_monic (xs : Array Std.U16 36#usize) (m : Nat) : (nodal xs m).Monic := by
  unfold nodal
  apply monic_prod_of_monic
  intro k _
  exact monic_X_sub_C _

theorem nodal_natDegree (xs : Array Std.U16 36#usize) (m : Nat) :
    (nodal xs m).natDegree = m := by
  unfold nodal
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-! ### The loop invariant: the trailing window of `c` represents `X^start · (partial nodal)`. -/

/-- The state invariant after the fold has processed `i` factors (loop index `i`, so the active
window starts at `start = n − i`): below `start` every GF16 coefficient is zero, and the window
`[start, n]` holds the coefficients of the partial nodal product `∏_{k<i}(X − xs[k])`. -/
def WinInv (xs : Array Std.U16 36#usize) (n : Nat) (c : Nat → Std.U16) (i : Nat) : Prop :=
  (∀ j, j < n - i → GF16.ofU16 (c j) = 0) ∧
  (∀ t, GF16.ofU16 (c (n - i + t)) = (nodal xs i).coeff t)

/-! ### The coefficient identity for multiplication by `(X − C d)` over GF16. -/

/-- The coefficient of `P * (X − C d)` over GF16, in characteristic two: at `0` it is
`d · P.coeff 0`; at `a + 1` it is `P.coeff a + d · P.coeff (a+1)`. (The `coeff_X_sub_C_mul`
engine, with `− = +` in characteristic two: `a + a = 0`.) -/
theorem coeff_mul_X_sub_C (P : GF16[X]) (d : GF16) :
    ∀ t, (P * (X - C d)).coeff t
      = (if t = 0 then 0 else P.coeff (t - 1)) + d * P.coeff t := by
  intro t
  rw [mul_comm]
  cases t with
  | zero =>
    simp only [↓reduceIte, zero_add]
    -- ((X - C d) * P).coeff 0 = (X*P).coeff 0 − (C d * P).coeff 0 = − d · P.coeff 0
    rw [sub_mul, coeff_sub, coeff_X_mul_zero, zero_sub]
    rw [show (C d * P).coeff 0 = d * P.coeff 0 by rw [coeff_C_mul]]
    exact neg_eq _
  | succ a =>
    simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero a)]
    -- coeff_X_sub_C_mul : ((X - C d)*P).coeff (a+1) = P.coeff a − d · P.coeff (a+1)
    rw [coeff_X_sub_C_mul]
    rw [sub_eq_add_neg, neg_eq]

/-! ### One fold step preserves the window invariant. -/

/-- **One `xdiffStepFn` step preserves `WinInv`.** If `WinInv xs n c i` holds and `i < n`, then
after one window-update at `start = n − i`, `difference = xs[i]`, the new coefficient function
satisfies `WinInv xs n · (i+1)` — i.e. the window now holds `∏_{k<i+1}(X − xs[k])`. This is the
characteristic-two multiply-by-`(X − xs[i])`-then-divide-by-`X` step in the trailing-window
(leading-coefficient-first) layout: `coeff_mul_X_sub_C` provides the coefficient identity. -/
theorem WinInv_step (xs : Array Std.U16 36#usize) (n : Nat) (c : Nat → Std.U16) (i : Nat)
    (hi : i < n) (hinv : WinInv xs n c i) :
    WinInv xs n (xdiffStepFn (n + 1) (n - i) xs.val[i]! c) (i + 1) := by
  obtain ⟨hbelow, hwin⟩ := hinv
  set d := GF16.ofU16 xs.val[i]! with hd
  set P := nodal xs i with hP
  have hdeg : P.natDegree = i := nodal_natDegree xs i
  constructor
  · -- below the new window `n-(i+1) = n-i-1`: untouched by the step, and old-below = 0.
    intro j hj
    rw [ofU16_xdiffStepFn]
    rw [if_neg (by omega)]      -- j is below the step window `[n-i-1, n)`
    exact hbelow j (by omega)
  · -- the new window holds `(nodal xs (i+1)).coeff t = (P * (X - C d)).coeff t`.
    intro t
    rw [nodal_succ, ← hP, coeff_mul_X_sub_C]
    -- evaluate the new coeff function at index `m = n-(i+1)+t = n-i-1+t`
    have hmrw : n - (i + 1) + t = n - i - 1 + t := by omega
    rw [hmrw, ofU16_xdiffStepFn]
    by_cases htw : n - i - 1 + t < n
    · -- in the step window: `c' m = c m + c(m+1)·d`
      have hcond : n - i - 1 ≤ n - i - 1 + t ∧ n - i - 1 + t < (n + 1) - 1 := by omega
      rw [if_pos hcond]
      -- c(m+1) = c(n-i + t) → P.coeff t (old window)
      have hm1 : n - i - 1 + t + 1 = n - i + t := by omega
      rw [hm1, hwin t]
      -- c(m) : t = 0 → below (0); t ≥ 1 → c(n-i + (t-1)) → P.coeff (t-1)
      cases t with
      | zero =>
        simp only [↓reduceIte]
        rw [show n - i - 1 + 0 = n - i - 1 by omega]
        rw [hbelow (n - i - 1) (by omega), mul_comm, zero_add]
      | succ a =>
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero a)]
        rw [show n - i - 1 + (a + 1) = n - i + a by omega, hwin a]
        rw [mul_comm]
    · -- past the window (`t > i`): `c' m = c m = c(n-i + (t-1)) = P.coeff (t-1)`, and `d·P.coeff t = 0`.
      have ht : i < t := by omega
      rw [if_neg (by omega)]
      have htne : t ≠ 0 := by omega
      have hm : n - i - 1 + t = n - i + (t - 1) := by omega
      rw [hm, hwin (t - 1)]
      rw [if_neg htne]
      -- P.coeff t = 0 since t > natDegree P = i
      have hzero : P.coeff t = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [hzero, mul_zero, add_zero]

/-! ### The base case and the fold. -/

/-- The initial coefficient function `prepareInit n` (`1` at index `n`, else `0`) satisfies the
window invariant at step `0`: the empty product `∏_{k<0}(…) = 1` sits as the constant `1` at the
top index `n` of the trailing-window layout. -/
theorem WinInv_init (xs : Array Std.U16 36#usize) (n : Std.Usize) :
    WinInv xs n.val (prepareInit n) 0 := by
  constructor
  · intro j hj
    unfold prepareInit
    rw [if_neg (by omega), ← Spqr.Gf16FieldInstance.zero_eq]
  · intro t
    unfold prepareInit
    rw [nodal_zero]
    cases t with
    | zero =>
      rw [show n.val - 0 + 0 = n.val by omega, if_pos rfl, ← Spqr.Gf16FieldInstance.one_eq,
        coeff_one]
      simp
    | succ a =>
      rw [if_neg (by omega), ← Spqr.Gf16FieldInstance.zero_eq, coeff_one]
      simp

/-- **The full prepare fold preserves the window invariant down to step `n`.** Starting from any
`c` with `WinInv xs n.val c i`, iterating `prepareFoldFn` (steps `i, i+1, …, n−1`) yields a
coefficient function with `WinInv xs n.val · n.val`, i.e. whose window (now starting at `0`) holds
the full nodal product `∏_{k<n}(X − xs[k])`. Induction on the number of remaining steps `n − i`. -/
theorem WinInv_fold (xs : Array Std.U16 36#usize) (n : Std.Usize) :
    ∀ (d : Nat) (c : Nat → Std.U16) (i : Nat), n.val - i = d → i ≤ n.val → WinInv xs n.val c i →
      WinInv xs n.val (prepareFoldFn xs n c i) n.val := by
  intro d
  induction d with
  | zero =>
    intro c i hd hile hinv
    have hin : ¬ i < n.val := by omega
    rw [prepareFoldFn, if_neg hin]
    have hie : i = n.val := by omega
    rw [hie] at hinv
    exact hinv
  | succ d ih =>
    intro c i hd hile hinv
    have hilt : i < n.val := by omega
    rw [prepareFoldFn, if_pos hilt]
    exact ih (xdiffStepFn (n.val + 1) (n.val - i) xs.val[i]! c) (i + 1) (by omega) (by omega)
      (WinInv_step xs n.val c i hilt hinv)

/-! ### From the final window invariant to `gpoly = nodal`. -/

/-- If a coefficient function `c` has, for every `t`, `ofU16 (c t) = (nodal xs n).coeff t` (exactly
the `WinInv … n` window at floor `0`), then its `GF16` coefficient polynomial truncated to `n + 1`
coefficients IS the nodal product: `gpoly c (n+1) = ∏_{k<n}(X − xs[k])`. Uses that `nodal` has
degree `n`, so `Polynomial.as_sum_range` truncates exactly at `n + 1`. -/
theorem gpoly_eq_nodal (xs : Array Std.U16 36#usize) (n : Nat) (c : Nat → Std.U16)
    (hc : ∀ t, t < n + 1 → GF16.ofU16 (c t) = (nodal xs n).coeff t) :
    gpoly c (n + 1) = nodal xs n := by
  unfold gpoly
  -- rewrite each coefficient via `hc`, then recognize `∑ C(coeff k) X^k` as the polynomial.
  have hstep : (∑ k ∈ Finset.range (n + 1), C (GF16.ofU16 (c k)) * X ^ k)
      = ∑ k ∈ Finset.range (n + 1), (monomial k) ((nodal xs n).coeff k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hc k hk, C_mul_X_pow_eq_monomial]
  rw [hstep]
  -- `nodal xs n = ∑_{k < natDegree+1} monomial k (coeff k)`, and natDegree = n.
  conv_rhs => rw [Polynomial.as_sum_range (nodal xs n), nodal_natDegree]

/-! ### P1. `gf.prepare` computes the nodal product (UNCONDITIONAL, in-boundary). -/

/-- **`gf.prepare` computes the nodal product `∏_{i<n}(X − xs[i])` over GF(2¹⁶)** (UNCONDITIONAL,
in-boundary). For `n ≤ 36`, the extracted `gf.prepare xs n` succeeds with a coefficient array `p`
whose `GF16` polynomial `gpoly (p[·]) (n+1)` equals `∏_{i<n}(X − C(ofU16 xs[i]))` — the master
nodal/numerator polynomial of the Lagrange interpolation. Assembled from the banked
`RsInterp.prepare_eq` (`gf.prepare` = the iterated `xdiffStepFn` fold, each iteration one
`mult_xdiff_trailing` = one `(X − xs[i])` multiply) and the window-invariant induction
(`WinInv_init`/`WinInv_step`/`WinInv_fold`) over the genuine `GF16` commutative ring. NO field
inverse, NO irreducibility — only the unconditional `CommRing` (`hmul` discharged by Stage 2).
NO `axiom`, `sorry`, `native_decide`, or `decide` over the value space. -/
theorem prepare_eq_nodal (xs : Array Std.U16 36#usize) (n : Std.Usize) (hn : n.val ≤ 36) :
    gf.prepare xs n
      ⦃ r => gpoly (fun k => r.val[k]!) (n.val + 1) = nodal xs n.val ⦄ := by
  have hpe := prepare_eq xs n hn
  apply Std.WP.spec_mono hpe
  intro r hr
  -- the final coefficient function has `WinInv … n` (window floor `0`).
  have hfinal : WinInv xs n.val (prepareFoldFn xs n (prepareInit n) 0) n.val :=
    WinInv_fold xs n (n.val) (prepareInit n) 0 rfl (by omega) (WinInv_init xs n)
  obtain ⟨_, hwin⟩ := hfinal
  -- `r.val[k]! = prepareFoldFn … k`, and `ofU16 (final k) = (nodal xs n).coeff k`.
  apply gpoly_eq_nodal
  intro t ht
  -- `t < n+1 ≤ 37`, so the extracted array value matches the fold value.
  have hrt : r.val[t]! = prepareFoldFn xs n (prepareInit n) 0 t := hr t (by omega)
  rw [hrt]
  have := hwin t
  rw [show n.val - n.val + t = t by omega] at this
  exact this

end Spqr.RsPrepareBridge
