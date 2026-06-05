/-
  SPQR Reed–Solomon codec — Layer B-irr (PARTIAL): structural factor-exclusion toward
  `Irreducible POLY_poly`, the multiplicative-side WALL.

  ## Context

  With Stage 2 closed (`Gf16ReduceTable`) the six `Gf16FieldAssembly` ring laws on the
  extracted `gfMulV` are UNCONDITIONAL, and the `decode ∘ encode = id` capstone
  (`RsFieldBridge.decode_value_at_roundtrip_gf16_of_dist`) is conditional on a SINGLE
  remaining algebraic premise: `Irreducible (POLY_poly : (ZMod 2)[X])`, where
  `POLY_poly = X¹⁶ + X¹² + X³ + X + 1`. This was the documented WALL (see `Gf16Field.lean` §4)
  — now CLOSED UNCONDITIONALLY in `Gf16IrreducibleBridge.lean`
  (`Spqr.Gf16IrreducibleBridge.POLY_poly_irreducible`). The route:

    * plain `decide` IS genuinely dead on `(ZMod 2)[X]` (the `Finsupp`/`AddMonoidAlgebra`
      representation does not kernel-reduce — verified at `coeff 0`); that obstruction is real.
    * A `Nat`/`BitVec` bit-trick mirror was ALSO kernel-infeasible: its `decide` recursed
      through `Nat.bitwise` (a single `Nat.log2 69643` already took ≈109 s), so the full
      mirror `decide` deterministic-timed-out / degenerated to `sorryAx` under a real
      `lake build`. **That failure was specific to the `Nat`/`BitVec` representation.**
    * The WORKING route (in `Gf16IrreducibleMirror.lean`) is a `List Bool` mirror of `F2[x]`
      (coeffs low-to-high, `true = 1`, `xor = +`) with schoolbook polynomial remainder. Its
      headline `noSmallFactor POLY 8 = true` — "no monic divisor of degree `1..8` divides
      `POLY`" — kernel-`decide`s in a few seconds and reports NO axioms at all (pure kernel
      Bool reduction; verified by `#print axioms`, NOT by the native evaluator, which had
      given a false positive on the old `Nat` mirror). `Gf16IrreducibleBridge.lean` then
      transports this to `(ZMod 2)[X]` (a `toPoly` map, the `bmod = %ₘ` correspondence, and
      enumeration completeness) and assembles `Irreducible POLY_poly` via
      `Monic.irreducible_iff_lt_natDegree_lt` — `#print axioms` shows only the three standard
      Mathlib axioms (`propext, Classical.choice, Quot.sound`), no `sorryAx`/`ofReduceBool`.

  The structural factor-exclusion lemmas banked below remain valid, kernel-checked
  CORROBORATION (they are now subsumed by the bridge's uniform all-monics `decide`). For the
  record, the original structural argument: a monic
  degree-16 polynomial over a field is irreducible iff it has no monic factor of degree
  `1..8` (`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`). This file banks the
  factor-exclusion STRATA proved structurally — no `decide` over `(ZMod 2)[X]`, no
  `native_decide`, no axiom:

    * degree 1 — already banked in `Gf16Field.lean` (`POLY_poly_no_linear_factor`);
    * **degree 2 — banked HERE** (`POLY_poly_no_quadratic_factor`): the UNIQUE monic
      irreducible quadratic over `ZMod 2` is `X² + X + 1`; we show it does not divide
      `POLY_poly` by evaluating in `GF(4) = (ZMod 2)[X] ⧸ (X²+X+1)`, where the root `α`
      satisfies `α³ = 1`, giving `POLY_poly(α) = α¹⁶ + α¹² + α³ + α + 1 = 1 ≠ 0`.
    * **degree 3 — banked HERE** (`POLY_poly_no_cubic_factor_a`, `POLY_poly_no_cubic_factor_b`):
      the exactly TWO monic irreducible cubics over `ZMod 2` are `X³ + X + 1` and `X³ + X² + 1`
      (a cubic over a field is irreducible iff it has no root). Each generates `GF(8)`, whose
      root has multiplicative order `7` (`β⁷ = 1`). Evaluating `POLY_poly` at the root and
      reducing the exponents mod 7 gives `POLY_poly(β) = β + 1 ≠ 0` for the first cubic and
      `POLY_poly(γ) = 1 ≠ 0` for the second — so neither divides `POLY_poly`, closing the
      entire degree-3 stratum. The char-2 cancellations are discharged by `linear_combination`
      against the root relation and `2 = 0` (no `decide` over `(ZMod 2)[X]`, no axiom).
    * **degree 4 — banked HERE** (`POLY_poly_no_quartic_factor_a/_b/_c`): the exactly THREE
      monic irreducible quartics over `ZMod 2` are `X⁴+X+1`, `X⁴+X³+1`, `X⁴+X³+X²+X+1`.
      Each generates `GF(16)`; evaluating `POLY_poly` at the root and reducing the exponents
      through the root relation (the root order divides 15) gives `POLY_poly = r²+r`, `s³+s`,
      `t³+t²+1` respectively — each a nonzero residue of degree `< 4`, certified nonzero by the
      uniform degree-gap engine `mk_ne_zero_of_degree_lt` (which never assumes `AdjoinRoot Q` is
      a domain, so it does not beg the irreducibility question). The power reductions climb one
      step at a time (`rⁿ = r·rⁿ⁻¹`) so every `linear_combination` coefficient is exact over ℤ,
      with `+ … * h2` correction terms exactly at the char-2 doubling steps — no `decide` over
      `(ZMod 2)[X]`, no axiom.
    * **degrees 5, 6, 7, 8 — banked HERE** (`POLY_poly_no_quintic_factor_*`,
      `POLY_poly_no_deg6_factor_*`, `POLY_poly_no_deg7_factor_*`, `POLY_poly_no_deg8_factor_*`):
      the SIX monic irreducible quintics, NINE sextics, EIGHTEEN septics and THIRTY octics over
      `ZMod 2` (63 polynomials in total — the full degree-5..8 stratum of the half-degree bound).
      Each generates `GF(2^d)`; `POLY_poly` is evaluated at the root and the powers `r⁵..r¹⁶` are
      reduced one step at a time by the SAME uniform `rⁿ = r·rⁿ⁻¹` engine (the single `r^d` per
      step reduced through the root relation, char-2 doublings corrected by `2 = 0`), yielding in
      every case a nonzero residue of degree `< d`, certified nonzero by `mk_ne_zero_of_degree_lt`
      (the single deg-8 case whose residue is the constant `1` is closed by `one_ne_zero`). The
      63 polynomials and their exact ℤ `linear_combination` certificates were enumerated by an
      off-line GF(2) Rabin/Frobenius script; the Lean proofs are fully kernel-checked — no
      `decide` over `(ZMod 2)[X]`, no `native_decide`, no axiom.

  ## Honest status (NOT faked)

  This banks the COMPLETE factor-exclusion data for `POLY_poly`: every monic IRREDUCIBLE
  polynomial of degree `1..8` (= `natDegree POLY_poly / 2`) is proved NOT to divide `POLY_poly`,
  across all eight degree strata. (`POLY_poly` is in fact irreducible — its root generates
  `GF(2¹⁶)` — verified off-line by the Rabin test; these lemmas are the sound, kernel-checked
  Lean witnesses of that fact's computational content.)

  These per-degree lemmas alone do NOT assemble into `Irreducible POLY_poly`: the completeness
  bridge `Monic.irreducible_iff_lt_natDegree_lt` requires `¬ q ∣ POLY_poly` for EVERY monic `q`
  of degree `1..8`, not just the listed irreducibles. That gap is NOW CLOSED, unconditionally,
  in `Gf16IrreducibleBridge.lean` (`POLY_poly_irreducible`): rather than enumerate over
  `(ZMod 2)[X]` (where `decide` is dead) or match the 63 irreducibles to a completeness list,
  the bridge tests ALL monic divisors of degree `1..8` via the computable `List Bool` mirror's
  kernel `decide` and transports the result. So `decode ∘ encode = id` is now UNCONDITIONAL: the
  `[Fact (Irreducible POLY_poly)]` instance is supplied by `fact_POLY_poly_irreducible`, and the
  unconditional capstone wrapper `decode_value_at_roundtrip_gf16_unconditional` lives in the
  bridge file. The lemmas below are kept as independent, kernel-checked CORROBORATION of the same
  fact (all EIGHT excluded strata, deg 1..8) — genuine sub-results, now subsumed but not deleted.

  These lemmas are ABOUT `(ZMod 2)[X]` (abstract), NOT about the extracted `gf.*` code, so —
  exactly like `POLY_poly_no_linear_factor` and `RsRoundtrip`'s abstract Lagrange facts —
  they are BUILDING BLOCKS, deliberately NOT registered as Audit headlines.
-/
import Demos.Spqr.Gf16Field
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

open Polynomial
open Spqr.Gf16Field (POLY_poly)

namespace Spqr.Gf16Irreducible

/-- `2` is prime — makes `ZMod 2` a field (hence an integral domain), which the
`AdjoinRoot.nontrivial` instance below needs. Standard, not a field-law cheat. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The unique monic irreducible quadratic over `ZMod 2`, `X² + X + 1`. -/
noncomputable def Q2 : (ZMod 2)[X] := X ^ 2 + X + 1

/-- `Q2 = X² + X + 1` is monic. -/
theorem Q2_monic : Q2.Monic := by unfold Q2; monicity!

/-- `Q2` has degree exactly 2. -/
theorem Q2_degree : Q2.degree = 2 := by unfold Q2; compute_degree!

/-- `Q2` has `natDegree` 2. -/
theorem Q2_natDegree : Q2.natDegree = 2 := by
  have := Q2_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q2; exact Q2_monic.ne_zero)] at this
  exact_mod_cast this

/-- The quotient `(ZMod 2)[X] ⧸ (Q2)` = `GF(4)` is nontrivial (since `deg Q2 ≠ 0`). -/
instance : Nontrivial (AdjoinRoot Q2) :=
  AdjoinRoot.nontrivial Q2 (by rw [Q2_degree]; decide)

/-- `(ZMod 2)[X] ⧸ (Q2)` has characteristic 2 (it is a `ZMod 2`-algebra, and the structure map
is injective into a nontrivial ring). This lets us reason in characteristic 2. -/
instance : CharP (AdjoinRoot Q2) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q2)).injective) 2

/-- **The root relation in `GF(4)`:** the canonical root `α = root Q2` satisfies `α² = α + 1`
(from `mk Q2 (X²+X+1) = 0` and characteristic 2). -/
theorem root_sq : (AdjoinRoot.root Q2) ^ 2 = AdjoinRoot.root Q2 + 1 := by
  have h0 : (AdjoinRoot.mk Q2) Q2 = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q2) Q2 = (AdjoinRoot.root Q2) ^ 2 + AdjoinRoot.root Q2 + 1 := by
    unfold Q2; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he, add_assoc, CharTwo.add_eq_zero] at h0
  exact h0

/-- **`α³ = 1` in `GF(4)`:** `α` is a primitive cube root of unity (`α·α² = α·(α+1) = α²+α =
(α+1)+α = 1`). -/
theorem root_cube : (AdjoinRoot.root Q2) ^ 3 = 1 := by
  set α := AdjoinRoot.root Q2 with hα
  have e : α ^ 3 = α ^ 2 * α := by ring
  rw [e, root_sq, add_mul, one_mul, ← pow_two, root_sq]
  rw [show α + 1 + α = (α + α) + 1 by ring, CharTwo.add_self_eq_zero, zero_add]

/-- **`POLY_poly` has no quadratic factor `X² + X + 1`** over `ZMod 2`, i.e. `Q2 ∤ POLY_poly`.
Proved by evaluating `POLY_poly` at the root `α` of `Q2` in `GF(4)`: with `α³ = 1` we get
`α¹⁶ = α`, `α¹² = 1`, `α³ = 1`, so `POLY_poly(α) = α + 1 + 1 + α + 1 = 1 ≠ 0`. Since `X²+X+1`
is the only monic irreducible quadratic over `ZMod 2`, this closes the entire degree-2 stratum
of the factor-exclusion criterion. (Building block toward `Irreducible POLY_poly`, NOT the
irreducibility theorem; degrees 3..8 remain the documented gap.) -/
theorem POLY_poly_no_quadratic_factor : ¬ Q2 ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set α := AdjoinRoot.root Q2 with hα
  -- evaluate POLY_poly at α
  have hmkP : AdjoinRoot.mk Q2 POLY_poly = α ^ 16 + α ^ 12 + α ^ 3 + α + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hα]
  rw [hmkP]
  -- reduce powers via α³ = 1
  have h16 : α ^ 16 = α := by
    rw [show (16 : ℕ) = 3 * 5 + 1 by norm_num, pow_add, pow_mul, root_cube, one_pow, pow_one,
      one_mul]
  have h12 : α ^ 12 = 1 := by
    rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul, root_cube, one_pow]
  rw [h16, h12, root_cube]
  -- α + 1 + 1 + α + 1 = 1  in characteristic 2
  rw [show α + 1 + 1 + α + 1 = (α + α) + (1 + 1) + 1 by ring, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, zero_add, zero_add]
  exact one_ne_zero

/-! ### Degree-3 stratum: no cubic factor

There are exactly TWO monic irreducible cubics over `ZMod 2`: `X³ + X + 1` and `X³ + X² + 1`
(a cubic is irreducible over a field iff it has no root; the eight monic cubics minus the six
with a root in `ZMod 2` leave these two). Each generates `GF(8)`, where the root has
multiplicative order `7` (`β⁷ = 1`). We exclude both by evaluating `POLY_poly` at the root in
the corresponding `GF(8)` and showing the value is nonzero — the same `AdjoinRoot` evaluation
technique as the quadratic stratum, no `decide` over `(ZMod 2)[X]`, no axiom. -/

/-- First monic irreducible cubic over `ZMod 2`: `X³ + X + 1`. -/
noncomputable def Q3a : (ZMod 2)[X] := X ^ 3 + X + 1

theorem Q3a_monic : Q3a.Monic := by unfold Q3a; monicity!
theorem Q3a_degree : Q3a.degree = 3 := by unfold Q3a; compute_degree!
theorem Q3a_natDegree : Q3a.natDegree = 3 := by
  have := Q3a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q3a; exact Q3a_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q3a) :=
  AdjoinRoot.nontrivial Q3a (by rw [Q3a_degree]; decide)

instance : CharP (AdjoinRoot Q3a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q3a)).injective) 2

/-- `GF(8) = (ZMod 2)[X] ⧸ (X³+X+1)` root relation: `β³ = β + 1`. -/
theorem root_cube_a : (AdjoinRoot.root Q3a) ^ 3 = AdjoinRoot.root Q3a + 1 := by
  have h0 : (AdjoinRoot.mk Q3a) Q3a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q3a) Q3a = (AdjoinRoot.root Q3a) ^ 3 + AdjoinRoot.root Q3a + 1 := by
    unfold Q3a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he, add_assoc, CharTwo.add_eq_zero] at h0
  exact h0

/-- `β⁷ = 1` in `GF(8)` (the root is a primitive 7th root of unity). Derived purely from
`β³ = β + 1` and characteristic 2 (via `linear_combination` against `2 = 0`). -/
theorem root_order_a : (AdjoinRoot.root Q3a) ^ 7 = 1 := by
  set β := AdjoinRoot.root Q3a with hβ
  have h3 : β ^ 3 = β + 1 := root_cube_a
  have h2 : (2 : AdjoinRoot Q3a) = 0 := CharTwo.two_eq_zero
  -- β⁷ = (β³)²·β; substitute β³ = β+1 and cancel char-2 cross terms.
  linear_combination (β ^ 4 + β ^ 2 + β + 1) * h3 + (β ^ 2 + β) * h2

/-- **`POLY_poly` has no cubic factor `X³ + X + 1`.** Evaluate at `β` in `GF(8)`: with `β⁷ = 1`,
`β¹⁶ = β²`, `β¹² = β⁵`, `β³ = β+1`; reducing gives `POLY_poly(β) = β + 1 ≠ 0`. -/
theorem POLY_poly_no_cubic_factor_a : ¬ Q3a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set β := AdjoinRoot.root Q3a with hβ
  have hmkP : AdjoinRoot.mk Q3a POLY_poly = β ^ 16 + β ^ 12 + β ^ 3 + β + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hβ]
  rw [hmkP]
  have h7 : β ^ 7 = 1 := root_order_a
  have h3 : β ^ 3 = β + 1 := root_cube_a
  have h2 : (2 : AdjoinRoot Q3a) = 0 := CharTwo.two_eq_zero
  -- β¹⁶ = β², β¹² = β⁵, β⁵ = β²+β+1, β³ = β+1; sum collapses to β + 1 in char 2.
  have h16 : β ^ 16 = β ^ 2 := by
    rw [show (16 : ℕ) = 7 * 2 + 2 by norm_num, pow_add, pow_mul, h7, one_pow, one_mul]
  have h12 : β ^ 12 = β ^ 5 := by
    rw [show (12 : ℕ) = 7 + 5 by norm_num, pow_add, h7, one_mul]
  have h5 : β ^ 5 = β ^ 2 + β + 1 := by
    linear_combination (β ^ 2 + 1) * h3
  have hval : β ^ 16 + β ^ 12 + β ^ 3 + β + 1 = β + 1 := by
    rw [h16, h12, h5, h3]
    linear_combination (β ^ 2 + β + 1) * h2
  rw [hval]
  -- goal: β + 1 ≠ 0.  If β + 1 = 0 then β = 1, contradicting β³ = β + 1 (gives 1 = 0).
  intro hc
  have hβ1 : β = 1 := by
    have := CharTwo.add_eq_zero.mp hc
    simpa using this
  rw [hβ1] at h3
  simp only [one_pow] at h3
  -- h3 : 1 = 1 + 1 = 0
  exact one_ne_zero (by linear_combination h3 + h2)

/-- Second monic irreducible cubic over `ZMod 2`: `X³ + X² + 1`. -/
noncomputable def Q3b : (ZMod 2)[X] := X ^ 3 + X ^ 2 + 1

theorem Q3b_monic : Q3b.Monic := by unfold Q3b; monicity!
theorem Q3b_degree : Q3b.degree = 3 := by unfold Q3b; compute_degree!
theorem Q3b_natDegree : Q3b.natDegree = 3 := by
  have := Q3b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q3b; exact Q3b_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q3b) :=
  AdjoinRoot.nontrivial Q3b (by rw [Q3b_degree]; decide)

instance : CharP (AdjoinRoot Q3b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q3b)).injective) 2

/-- `GF(8) = (ZMod 2)[X] ⧸ (X³+X²+1)` root relation: `γ³ = γ² + 1`. -/
theorem root_cube_b : (AdjoinRoot.root Q3b) ^ 3 = (AdjoinRoot.root Q3b) ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q3b) Q3b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q3b) Q3b = (AdjoinRoot.root Q3b) ^ 3 + (AdjoinRoot.root Q3b) ^ 2 + 1 := by
    unfold Q3b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he, add_assoc, CharTwo.add_eq_zero] at h0
  exact h0

/-- `γ⁷ = 1` in this `GF(8)`. Derived from `γ³ = γ² + 1` and characteristic 2. -/
theorem root_order_b : (AdjoinRoot.root Q3b) ^ 7 = 1 := by
  set γ := AdjoinRoot.root Q3b with hγ
  have h3 : γ ^ 3 = γ ^ 2 + 1 := root_cube_b
  have h2 : (2 : AdjoinRoot Q3b) = 0 := CharTwo.two_eq_zero
  -- γ⁷ = (γ³)²·γ; substitute γ³ = γ²+1 and cancel char-2 cross terms.
  linear_combination (γ ^ 4 + γ ^ 3 + γ ^ 2 + 1) * h3 + (γ ^ 4 + γ ^ 2) * h2

/-- **`POLY_poly` has no cubic factor `X³ + X² + 1`.** Evaluate at `γ` in `GF(8)`: with `γ⁷ = 1`,
`γ¹⁶ = γ²`, `γ¹² = γ⁵`; reducing gives `POLY_poly(γ) = 1 ≠ 0`. -/
theorem POLY_poly_no_cubic_factor_b : ¬ Q3b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set γ := AdjoinRoot.root Q3b with hγ
  have hmkP : AdjoinRoot.mk Q3b POLY_poly = γ ^ 16 + γ ^ 12 + γ ^ 3 + γ + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hγ]
  rw [hmkP]
  have h7 : γ ^ 7 = 1 := root_order_b
  have h3 : γ ^ 3 = γ ^ 2 + 1 := root_cube_b
  have h2 : (2 : AdjoinRoot Q3b) = 0 := CharTwo.two_eq_zero
  have h16 : γ ^ 16 = γ ^ 2 := by
    rw [show (16 : ℕ) = 7 * 2 + 2 by norm_num, pow_add, pow_mul, h7, one_pow, one_mul]
  have h12 : γ ^ 12 = γ ^ 5 := by
    rw [show (12 : ℕ) = 7 + 5 by norm_num, pow_add, h7, one_mul]
  -- γ⁵ = γ²·γ³ = γ²(γ²+1) = γ⁴ + γ²; with γ⁴ = γ²+γ+1 ⇒ γ⁵ = γ + 1.
  have h5 : γ ^ 5 = γ + 1 := by
    linear_combination (γ ^ 2 + γ + 1) * h3 + (γ ^ 2) * h2
  have hval : γ ^ 16 + γ ^ 12 + γ ^ 3 + γ + 1 = 1 := by
    rw [h16, h12, h5, h3]
    linear_combination (γ ^ 2 + γ + 1) * h2
  rw [hval]
  exact one_ne_zero

/-! ### Degree-4 stratum: no quartic factor

There are exactly THREE monic irreducible quartics over `ZMod 2`:
`X⁴+X+1`, `X⁴+X³+1`, `X⁴+X³+X²+X+1`. (The 16 monic quartics, minus the 8 with a `ZMod 2`
root and the 1 reducible-into-two-irreducible-quadratics product `(X²+X+1)²`, leave 3.)
Each generates `GF(16)`, whose root has multiplicative order dividing `15`; we use only
`r¹⁵ = 1`, evaluate `POLY_poly` at the root, and reduce the exponents — the same `AdjoinRoot`
evaluation technique as the lower strata, no `decide` over `(ZMod 2)[X]`, no axiom. Excluding
all monic quartic factors closes the degree-4 stratum of `irreducible_iff_lt_natDegree_lt`
(any monic quartic divisor either is one of these three irreducibles, or factors through a
lower-degree monic irreducible already excluded by the degree-1/2 strata). -/

/-- **Degree-gap non-divisibility:** a nonzero polynomial `g` of degree strictly less than
`deg Q` is not divisible by `Q`, so its image `mk Q g` in `(ZMod 2)[X] ⧸ Q` is nonzero. This is
the uniform engine that turns "`POLY_poly` evaluates to a small nonzero residue at the root of
`Q`" into "`Q ∤ POLY_poly`" without ever assuming `AdjoinRoot Q` is a domain (which would beg
the irreducibility question). Purely a degree argument (`Polynomial.degree_le_of_dvd`). -/
theorem mk_ne_zero_of_degree_lt {Q g : (ZMod 2)[X]} (hg : g ≠ 0) (hlt : g.degree < Q.degree) :
    AdjoinRoot.mk Q g ≠ 0 := by
  intro hz
  rw [AdjoinRoot.mk_eq_zero] at hz
  exact absurd (Polynomial.degree_le_of_dvd hz hg) (not_le.mpr hlt)

/-- First monic irreducible quartic: `X⁴ + X + 1`. -/
noncomputable def Q4a : (ZMod 2)[X] := X ^ 4 + X + 1

theorem Q4a_monic : Q4a.Monic := by unfold Q4a; monicity!
theorem Q4a_degree : Q4a.degree = 4 := by unfold Q4a; compute_degree!
theorem Q4a_natDegree : Q4a.natDegree = 4 := by
  have := Q4a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q4a; exact Q4a_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q4a) :=
  AdjoinRoot.nontrivial Q4a (by rw [Q4a_degree]; decide)

instance : CharP (AdjoinRoot Q4a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q4a)).injective) 2

/-- `GF(16) = (ZMod 2)[X] ⧸ (X⁴+X+1)` root relation: `r⁴ = r + 1`. -/
theorem root_quartic_a : (AdjoinRoot.root Q4a) ^ 4 = AdjoinRoot.root Q4a + 1 := by
  have h0 : (AdjoinRoot.mk Q4a) Q4a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q4a) Q4a = (AdjoinRoot.root Q4a) ^ 4 + AdjoinRoot.root Q4a + 1 := by
    unfold Q4a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he, add_assoc, CharTwo.add_eq_zero] at h0
  exact h0

/-- **`POLY_poly` has no quartic factor `X⁴ + X + 1`.** Evaluate at `r` in `GF(16)`: with
`r⁴ = r+1` one gets `r¹⁵ = 1` (so `r¹⁶ = r`) and `r¹² = r³+r²+r+1`, giving
`POLY_poly(r) = r² + r ≠ 0`. -/
theorem POLY_poly_no_quartic_factor_a : ¬ Q4a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q4a with hr
  have hmkP : AdjoinRoot.mk Q4a POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h4 : r ^ 4 = r + 1 := root_quartic_a
  have h2 : (2 : AdjoinRoot Q4a) = 0 := CharTwo.two_eq_zero
  -- Climb the powers one step at a time via `rⁿ = r · rⁿ⁻¹`, reducing the single `r⁴` that
  -- appears each step through `h4` (coefficient 0 or 1 — no doubling), and discharging the only
  -- char-2 cancellations (a doubled `r` ↦ `r · 2`) with `h2 : 2 = 0`. Each `linear_combination`
  -- coefficient is exact over ℤ; the `+ r * h2` terms appear precisely at the doubling steps.
  have h5 : r ^ 5 = r ^ 2 + r := by linear_combination r * h4
  have h6 : r ^ 6 = r ^ 3 + r ^ 2 := by linear_combination r * h5
  have h7 : r ^ 7 = r ^ 3 + r + 1 := by linear_combination r * h6 + h4
  have h8 : r ^ 8 = r ^ 2 + 1 := by linear_combination r * h7 + h4 + r * h2
  have h9 : r ^ 9 = r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 2 + r + 1 := by linear_combination r * h9 + h4
  have h11 : r ^ 11 = r ^ 3 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h4
  have h13 : r ^ 13 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h4 + r * h2
  have h14 : r ^ 14 = r ^ 3 + 1 := by linear_combination r * h13 + h4 + r * h2
  have h15 : r ^ 15 = 1 := by linear_combination r * h14 + h4 + r * h2
  have h16 : r ^ 16 = r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  -- r² + r = mk Q4a (X² + X), a nonzero residue of degree 2 < 4, so it is ≠ 0.
  have hrw : r ^ 2 + r = AdjoinRoot.mk Q4a (X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 2 + X : (ZMod 2)[X]).degree = 2 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q4a_degree]
    have hd : (X ^ 2 + X : (ZMod 2)[X]).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Second monic irreducible quartic: `X⁴ + X³ + 1`. -/
noncomputable def Q4b : (ZMod 2)[X] := X ^ 4 + X ^ 3 + 1

theorem Q4b_monic : Q4b.Monic := by unfold Q4b; monicity!
theorem Q4b_degree : Q4b.degree = 4 := by unfold Q4b; compute_degree!
theorem Q4b_natDegree : Q4b.natDegree = 4 := by
  have := Q4b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q4b; exact Q4b_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q4b) :=
  AdjoinRoot.nontrivial Q4b (by rw [Q4b_degree]; decide)

instance : CharP (AdjoinRoot Q4b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q4b)).injective) 2

/-- `GF(16) = (ZMod 2)[X] ⧸ (X⁴+X³+1)` root relation: `s⁴ = s³ + 1`. -/
theorem root_quartic_b : (AdjoinRoot.root Q4b) ^ 4 = (AdjoinRoot.root Q4b) ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q4b) Q4b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q4b) Q4b = (AdjoinRoot.root Q4b) ^ 4 + (AdjoinRoot.root Q4b) ^ 3 + 1 := by
    unfold Q4b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he, add_assoc, CharTwo.add_eq_zero] at h0
  exact h0

/-- **`POLY_poly` has no quartic factor `X⁴ + X³ + 1`.** -/
theorem POLY_poly_no_quartic_factor_b : ¬ Q4b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set s := AdjoinRoot.root Q4b with hs
  have hmkP : AdjoinRoot.mk Q4b POLY_poly = s ^ 16 + s ^ 12 + s ^ 3 + s + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hs]
  rw [hmkP]
  have h4 : s ^ 4 = s ^ 3 + 1 := root_quartic_b
  have h2 : (2 : AdjoinRoot Q4b) = 0 := CharTwo.two_eq_zero
  -- Climb the powers one step at a time via `sⁿ = s · sⁿ⁻¹`, reducing the single `s⁴` that
  -- appears each step through `h4` (coefficient 0 or 1 — no doubling), and discharging the only
  -- char-2 cancellations (a doubled `s³` ↦ `s³ · 2`) with `h2 : 2 = 0`. Each `linear_combination`
  -- coefficient is exact over ℤ; the `+ s³ * h2` terms appear precisely at the doubling steps.
  have h5 : s ^ 5 = s ^ 3 + s + 1 := by linear_combination (s + 1) * h4
  have h6 : s ^ 6 = s ^ 3 + s ^ 2 + s + 1 := by linear_combination s * h5 + h4
  have h7 : s ^ 7 = s ^ 2 + s + 1 := by linear_combination s * h6 + h4 + s ^ 3 * h2
  have h8 : s ^ 8 = s ^ 3 + s ^ 2 + s := by linear_combination s * h7
  have h9 : s ^ 9 = s ^ 2 + 1 := by linear_combination s * h8 + h4 + s ^ 3 * h2
  have h10 : s ^ 10 = s ^ 3 + s := by linear_combination s * h9
  have h11 : s ^ 11 = s ^ 3 + s ^ 2 + 1 := by linear_combination s * h10 + h4
  have h12 : s ^ 12 = s + 1 := by linear_combination s * h11 + h4 + s ^ 3 * h2
  have h13 : s ^ 13 = s ^ 2 + s := by linear_combination s * h12
  have h14 : s ^ 14 = s ^ 3 + s ^ 2 := by linear_combination s * h13
  have h15 : s ^ 15 = 1 := by linear_combination s * h14 + h4 + s ^ 3 * h2
  have h16 : s ^ 16 = s := by linear_combination s * h15
  have hval : s ^ 16 + s ^ 12 + s ^ 3 + s + 1 = s ^ 3 + s := by
    rw [h16, h12]; linear_combination (s + 1) * h2
  rw [hval]
  have hrw : s ^ 3 + s = AdjoinRoot.mk Q4b (X ^ 3 + X) := by
    rw [hs]; simp only [map_add, map_pow, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 3 + X : (ZMod 2)[X]).degree = 3 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q4b_degree]
    have hd : (X ^ 3 + X : (ZMod 2)[X]).degree ≤ 3 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Third monic irreducible quartic: `X⁴ + X³ + X² + X + 1`. -/
noncomputable def Q4c : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X ^ 2 + X + 1

theorem Q4c_monic : Q4c.Monic := by unfold Q4c; monicity!
theorem Q4c_degree : Q4c.degree = 4 := by unfold Q4c; compute_degree!
theorem Q4c_natDegree : Q4c.natDegree = 4 := by
  have := Q4c_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q4c; exact Q4c_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q4c) :=
  AdjoinRoot.nontrivial Q4c (by rw [Q4c_degree]; decide)

instance : CharP (AdjoinRoot Q4c) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q4c)).injective) 2

/-- `GF(16) = (ZMod 2)[X] ⧸ (X⁴+X³+X²+X+1)` root relation: `t⁴ = t³ + t² + t + 1`. -/
theorem root_quartic_c :
    (AdjoinRoot.root Q4c) ^ 4
      = (AdjoinRoot.root Q4c) ^ 3 + (AdjoinRoot.root Q4c) ^ 2 + AdjoinRoot.root Q4c + 1 := by
  have h0 : (AdjoinRoot.mk Q4c) Q4c = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q4c) Q4c
      = (AdjoinRoot.root Q4c) ^ 4 + (AdjoinRoot.root Q4c) ^ 3
        + (AdjoinRoot.root Q4c) ^ 2 + AdjoinRoot.root Q4c + 1 := by
    unfold Q4c; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [he] at h0
  -- t⁴ + t³ + t² + t + 1 = 0  ⇒  t⁴ = t³ + t² + t + 1  (char 2: move the tail across, 2 = 0)
  have h2 : (2 : AdjoinRoot Q4c) = 0 := CharTwo.two_eq_zero
  linear_combination h0
    - ((AdjoinRoot.root Q4c) ^ 3 + (AdjoinRoot.root Q4c) ^ 2 + AdjoinRoot.root Q4c + 1) * h2

/-- **`POLY_poly` has no quartic factor `X⁴ + X³ + X² + X + 1`.** Evaluate at `t` in `GF(16)`:
since `Q4c = (X⁵ - 1)/(X - 1)`, the root satisfies `t⁵ = 1`, hence `t¹⁶ = t` and `t¹² = t²`;
reducing gives `POLY_poly(t) = t³ + t² + 1 ≠ 0` (a nonzero residue of degree 3 < 4). -/
theorem POLY_poly_no_quartic_factor_c : ¬ Q4c ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set t := AdjoinRoot.root Q4c with ht
  have hmkP : AdjoinRoot.mk Q4c POLY_poly = t ^ 16 + t ^ 12 + t ^ 3 + t + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, ht]
  rw [hmkP]
  have h4 : t ^ 4 = t ^ 3 + t ^ 2 + t + 1 := root_quartic_c
  have h2 : (2 : AdjoinRoot Q4c) = 0 := CharTwo.two_eq_zero
  -- t⁵ = t·t⁴ = t⁴ + t³ + t² + t = 1 (char 2): the two copies of t³,t²,t cancel.
  have h5 : t ^ 5 = 1 := by
    linear_combination (t + 1) * h4 + (t ^ 3 + t ^ 2 + t) * h2
  -- t¹⁶ = (t⁵)³·t = t,  t¹² = (t⁵)²·t² = t²
  have h16 : t ^ 16 = t := by
    rw [show (16 : ℕ) = 5 * 3 + 1 by norm_num, pow_add, pow_mul, h5, one_pow, pow_one, one_mul]
  have h12 : t ^ 12 = t ^ 2 := by
    rw [show (12 : ℕ) = 5 * 2 + 2 by norm_num, pow_add, pow_mul, h5, one_pow, one_mul]
  -- POLY_poly(t) = t + t² + t³ + t + 1 = t³ + t² + 1 in char 2.
  have hval : t ^ 16 + t ^ 12 + t ^ 3 + t + 1 = t ^ 3 + t ^ 2 + 1 := by
    rw [h16, h12]
    linear_combination t * h2
  rw [hval]
  -- t³ + t² + 1 = mk Q4c (X³ + X² + 1), a nonzero residue of degree 3 < 4.
  have hrw : t ^ 3 + t ^ 2 + 1 = AdjoinRoot.mk Q4c (X ^ 3 + X ^ 2 + 1) := by
    rw [ht]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 3 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q4c_degree]
    have hd : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 3 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)


/-! ### Degree-5 stratum: no quintic factor

There are exactly SIX monic irreducible quintics over `ZMod 2`. Each generates `GF(32)`;
we evaluate `POLY_poly` at the root and reduce the exponents one step at a time
(`rⁿ = r·rⁿ⁻¹`, reducing the single `r⁵` per step through the root relation, char-2
doublings corrected by `2 = 0`) — the same `AdjoinRoot` evaluation engine as the lower
strata, no `decide` over `(ZMod 2)[X]`, no axiom. In every case `POLY_poly` reduces to a
nonzero residue of degree `< 5`, certified nonzero by `mk_ne_zero_of_degree_lt`. This
closes the degree-5 stratum of the factor-exclusion criterion. -/

/-- Monic irreducible quintic #1: `X ^ 5 + X ^ 2 + 1`. -/
noncomputable def Q5a : (ZMod 2)[X] := X ^ 5 + X ^ 2 + 1
theorem Q5a_monic : Q5a.Monic := by unfold Q5a; monicity!
theorem Q5a_degree : Q5a.degree = 5 := by unfold Q5a; compute_degree!
theorem Q5a_natDegree : Q5a.natDegree = 5 := by
  have := Q5a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5a; exact Q5a_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5a) :=
  AdjoinRoot.nontrivial Q5a (by rw [Q5a_degree]; decide)
instance : CharP (AdjoinRoot Q5a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5a)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 2 + 1)`: `r⁵ = r ^ 2 + 1`. -/
theorem root_Q5a : (AdjoinRoot.root Q5a) ^ 5 = AdjoinRoot.root Q5a ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q5a) Q5a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5a) Q5a = (AdjoinRoot.root Q5a) ^ 5 + (AdjoinRoot.root Q5a) ^ 2 + 1 := by
    unfold Q5a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5a) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5a ^ 2 + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_quintic_factor_a : ¬ Q5a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5a with hr
  have hmkP : AdjoinRoot.mk Q5a POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 2 + 1 := root_Q5a
  have h2 : (2 : AdjoinRoot Q5a) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 3 + r := by linear_combination r * h5
  have h7 : r ^ 7 = r ^ 4 + r ^ 2 := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h7 + h5
  have h9 : r ^ 9 = r ^ 4 + r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 4 + 1 := by linear_combination r * h9 + h5 + (r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 2 + r + 1 := by linear_combination r * h10 + h5
  have h12 : r ^ 12 = r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h13 + h5
  have h15 : r ^ 15 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h14 + h5
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h15 + h5 + (r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q5a (X ^ 4 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5a_degree]
    have hd : (X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible quintic #2: `X ^ 5 + X ^ 3 + 1`. -/
noncomputable def Q5b : (ZMod 2)[X] := X ^ 5 + X ^ 3 + 1
theorem Q5b_monic : Q5b.Monic := by unfold Q5b; monicity!
theorem Q5b_degree : Q5b.degree = 5 := by unfold Q5b; compute_degree!
theorem Q5b_natDegree : Q5b.natDegree = 5 := by
  have := Q5b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5b; exact Q5b_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5b) :=
  AdjoinRoot.nontrivial Q5b (by rw [Q5b_degree]; decide)
instance : CharP (AdjoinRoot Q5b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5b)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 3 + 1)`: `r⁵ = r ^ 3 + 1`. -/
theorem root_Q5b : (AdjoinRoot.root Q5b) ^ 5 = AdjoinRoot.root Q5b ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q5b) Q5b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5b) Q5b = (AdjoinRoot.root Q5b) ^ 5 + (AdjoinRoot.root Q5b) ^ 3 + 1 := by
    unfold Q5b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5b) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5b ^ 3 + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_quintic_factor_b : ¬ Q5b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5b with hr
  have hmkP : AdjoinRoot.mk Q5b POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 3 + 1 := root_Q5b
  have h2 : (2 : AdjoinRoot Q5b) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 4 + r := by linear_combination r * h5
  have h7 : r ^ 7 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h6 + h5
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h8 + h5
  have h10 : r ^ 10 = r ^ 4 + r + 1 := by linear_combination r * h9 + h5 + (r ^ 3) * h2
  have h11 : r ^ 11 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h5
  have h12 : r ^ 12 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h12 + h5 + (r ^ 3) * h2
  have h14 : r ^ 14 = r + 1 := by linear_combination r * h13 + h5 + (r ^ 3) * h2
  have h15 : r ^ 15 = r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 3 + r ^ 2 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r ^ 2 + r) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 + 1 = AdjoinRoot.mk Q5b (X ^ 4 + X ^ 3 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5b_degree]
    have hd : (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible quintic #3: `X ^ 5 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q5c : (ZMod 2)[X] := X ^ 5 + X ^ 3 + X ^ 2 + X + 1
theorem Q5c_monic : Q5c.Monic := by unfold Q5c; monicity!
theorem Q5c_degree : Q5c.degree = 5 := by unfold Q5c; compute_degree!
theorem Q5c_natDegree : Q5c.natDegree = 5 := by
  have := Q5c_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5c; exact Q5c_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5c) :=
  AdjoinRoot.nontrivial Q5c (by rw [Q5c_degree]; decide)
instance : CharP (AdjoinRoot Q5c) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5c)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 3 + X ^ 2 + X + 1)`: `r⁵ = r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q5c : (AdjoinRoot.root Q5c) ^ 5 = AdjoinRoot.root Q5c ^ 3 + AdjoinRoot.root Q5c ^ 2 + AdjoinRoot.root Q5c + 1 := by
  have h0 : (AdjoinRoot.mk Q5c) Q5c = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5c) Q5c = (AdjoinRoot.root Q5c) ^ 5 + (AdjoinRoot.root Q5c) ^ 3 + (AdjoinRoot.root Q5c) ^ 2 + AdjoinRoot.root Q5c + 1 := by
    unfold Q5c; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5c) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5c ^ 3 + AdjoinRoot.root Q5c ^ 2 + AdjoinRoot.root Q5c + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_quintic_factor_c : ¬ Q5c ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5c with hr
  have hmkP : AdjoinRoot.mk Q5c POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 3 + r ^ 2 + r + 1 := root_Q5c
  have h2 : (2 : AdjoinRoot Q5c) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h5
  have h7 : r ^ 7 = r ^ 4 + r + 1 := by linear_combination r * h6 + h5 + (r ^ 3 + r ^ 2) * h2
  have h8 : r ^ 8 = r ^ 3 + 1 := by linear_combination r * h7 + h5 + (r ^ 2 + r) * h2
  have h9 : r ^ 9 = r ^ 4 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 3 + r + 1 := by linear_combination r * h9 + h5 + (r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 4 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r + 1 := by linear_combination r * h11 + h5 + (r ^ 3 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 3 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 4 + r ^ 3 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h15 + h5
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 2 + r + 1 = AdjoinRoot.mk Q5c (X ^ 4 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5c_degree]
    have hd : (X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible quintic #4: `X ^ 5 + X ^ 4 + X ^ 2 + X + 1`. -/
noncomputable def Q5d : (ZMod 2)[X] := X ^ 5 + X ^ 4 + X ^ 2 + X + 1
theorem Q5d_monic : Q5d.Monic := by unfold Q5d; monicity!
theorem Q5d_degree : Q5d.degree = 5 := by unfold Q5d; compute_degree!
theorem Q5d_natDegree : Q5d.natDegree = 5 := by
  have := Q5d_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5d; exact Q5d_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5d) :=
  AdjoinRoot.nontrivial Q5d (by rw [Q5d_degree]; decide)
instance : CharP (AdjoinRoot Q5d) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5d)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 4 + X ^ 2 + X + 1)`: `r⁵ = r ^ 4 + r ^ 2 + r + 1`. -/
theorem root_Q5d : (AdjoinRoot.root Q5d) ^ 5 = AdjoinRoot.root Q5d ^ 4 + AdjoinRoot.root Q5d ^ 2 + AdjoinRoot.root Q5d + 1 := by
  have h0 : (AdjoinRoot.mk Q5d) Q5d = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5d) Q5d = (AdjoinRoot.root Q5d) ^ 5 + (AdjoinRoot.root Q5d) ^ 4 + (AdjoinRoot.root Q5d) ^ 2 + AdjoinRoot.root Q5d + 1 := by
    unfold Q5d; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5d) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5d ^ 4 + AdjoinRoot.root Q5d ^ 2 + AdjoinRoot.root Q5d + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 4 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_quintic_factor_d : ¬ Q5d ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5d with hr
  have hmkP : AdjoinRoot.mk Q5d POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 4 + r ^ 2 + r + 1 := root_Q5d
  have h2 : (2 : AdjoinRoot Q5d) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 4 + r ^ 3 + 1 := by linear_combination r * h5 + h5 + (r ^ 2 + r) * h2
  have h7 : r ^ 7 = r ^ 2 + 1 := by linear_combination r * h6 + h5 + (r ^ 4 + r) * h2
  have h8 : r ^ 8 = r ^ 3 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 4 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h9 + h5
  have h11 : r ^ 11 = r ^ 3 + 1 := by linear_combination r * h10 + h5 + (r ^ 4 + r ^ 2 + r) * h2
  have h12 : r ^ 12 = r ^ 4 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r + 1 := by linear_combination r * h12 + h5 + (r ^ 2) * h2
  have h14 : r ^ 14 = r ^ 4 + 1 := by linear_combination r * h13 + h5 + (r ^ 2 + r) * h2
  have h15 : r ^ 15 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h14 + h5 + (r) * h2
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h5 + (r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 2 = AdjoinRoot.mk Q5d (X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 2 : (ZMod 2)[X]).degree = 2 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5d_degree]
    have hd : (X ^ 2 : (ZMod 2)[X]).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible quintic #5: `X ^ 5 + X ^ 4 + X ^ 3 + X + 1`. -/
noncomputable def Q5e : (ZMod 2)[X] := X ^ 5 + X ^ 4 + X ^ 3 + X + 1
theorem Q5e_monic : Q5e.Monic := by unfold Q5e; monicity!
theorem Q5e_degree : Q5e.degree = 5 := by unfold Q5e; compute_degree!
theorem Q5e_natDegree : Q5e.natDegree = 5 := by
  have := Q5e_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5e; exact Q5e_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5e) :=
  AdjoinRoot.nontrivial Q5e (by rw [Q5e_degree]; decide)
instance : CharP (AdjoinRoot Q5e) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5e)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 4 + X ^ 3 + X + 1)`: `r⁵ = r ^ 4 + r ^ 3 + r + 1`. -/
theorem root_Q5e : (AdjoinRoot.root Q5e) ^ 5 = AdjoinRoot.root Q5e ^ 4 + AdjoinRoot.root Q5e ^ 3 + AdjoinRoot.root Q5e + 1 := by
  have h0 : (AdjoinRoot.mk Q5e) Q5e = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5e) Q5e = (AdjoinRoot.root Q5e) ^ 5 + (AdjoinRoot.root Q5e) ^ 4 + (AdjoinRoot.root Q5e) ^ 3 + AdjoinRoot.root Q5e + 1 := by
    unfold Q5e; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5e) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5e ^ 4 + AdjoinRoot.root Q5e ^ 3 + AdjoinRoot.root Q5e + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 4 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_quintic_factor_e : ¬ Q5e ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5e with hr
  have hmkP : AdjoinRoot.mk Q5e POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 4 + r ^ 3 + r + 1 := root_Q5e
  have h2 : (2 : AdjoinRoot Q5e) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h5 + h5 + (r ^ 4 + r) * h2
  have h7 : r ^ 7 = r ^ 4 + r ^ 3 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h7 + h5 + (r ^ 4) * h2
  have h9 : r ^ 9 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 2 + r + 1 := by linear_combination r * h9 + h5 + (r ^ 4 + r ^ 3) * h2
  have h11 : r ^ 11 = r ^ 3 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r + 1 := by linear_combination r * h12 + h5 + (r ^ 4 + r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 3 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3) * h2
  rw [hval]
  have hrw : r ^ 3 + r ^ 2 + r + 1 = AdjoinRoot.mk Q5e (X ^ 3 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 3 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5e_degree]
    have hd : (X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 3 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible quintic #6: `X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q5f : (ZMod 2)[X] := X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q5f_monic : Q5f.Monic := by unfold Q5f; monicity!
theorem Q5f_degree : Q5f.degree = 5 := by unfold Q5f; compute_degree!
theorem Q5f_natDegree : Q5f.natDegree = 5 := by
  have := Q5f_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q5f; exact Q5f_monic.ne_zero)] at this
  exact_mod_cast this

instance : Nontrivial (AdjoinRoot Q5f) :=
  AdjoinRoot.nontrivial Q5f (by rw [Q5f_degree]; decide)
instance : CharP (AdjoinRoot Q5f) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q5f)).injective) 2

/-- Root relation in `GF(32) = (ZMod 2)[X] ⧸ (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1)`: `r⁵ = r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q5f : (AdjoinRoot.root Q5f) ^ 5 = AdjoinRoot.root Q5f ^ 4 + AdjoinRoot.root Q5f ^ 3 + AdjoinRoot.root Q5f ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q5f) Q5f = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q5f) Q5f = (AdjoinRoot.root Q5f) ^ 5 + (AdjoinRoot.root Q5f) ^ 4 + (AdjoinRoot.root Q5f) ^ 3 + (AdjoinRoot.root Q5f) ^ 2 + 1 := by
    unfold Q5f; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q5f) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q5f ^ 4 + AdjoinRoot.root Q5f ^ 3 + AdjoinRoot.root Q5f ^ 2 + 1) * h2

/-- **`POLY_poly` has no quintic factor `X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_quintic_factor_f : ¬ Q5f ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q5f with hr
  have hmkP : AdjoinRoot.mk Q5f POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h5 : r ^ 5 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q5f
  have h2 : (2 : AdjoinRoot Q5f) = 0 := CharTwo.two_eq_zero
  have h6 : r ^ 6 = r ^ 2 + r + 1 := by linear_combination r * h5 + h5 + (r ^ 4 + r ^ 3) * h2
  have h7 : r ^ 7 = r ^ 3 + r ^ 2 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 2 + 1 := by linear_combination r * h8 + h5 + (r ^ 4 + r ^ 3) * h2
  have h10 : r ^ 10 = r ^ 3 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 4 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h11 + h5 + (r ^ 3) * h2
  have h13 : r ^ 13 = r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h12 + h5 + (r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 4 + r + 1 := by linear_combination r * h13 + h5 + (r ^ 3 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h14 + h5 + (r ^ 2) * h2
  have h16 : r ^ 16 = r ^ 3 + r + 1 := by linear_combination r * h15 + h5 + (r ^ 4 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 2 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 2 + 1 = AdjoinRoot.mk Q5f (X ^ 4 + X ^ 2 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q5f_degree]
    have hd : (X ^ 4 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)


/-! ### Degree-6 stratum: no degree-6 factor

There are exactly 9 monic irreducible degree-6 polynomials over `ZMod 2`.
Each generates `GF(2^6)`; we evaluate `POLY_poly` at the root, climb `rⁿ = r·rⁿ⁻¹`
reducing the single `r^6` per step through the root relation (char-2 doublings corrected
by `2 = 0`), and certify the resulting degree-`<6` residue nonzero via
`mk_ne_zero_of_degree_lt`. No `decide` over `(ZMod 2)[X]`, no axiom. Closes the degree-6
stratum of the factor-exclusion criterion. -/

/-- Monic irreducible degree-6 #1: `X ^ 6 + X + 1`. -/
noncomputable def Q6a : (ZMod 2)[X] := X ^ 6 + X + 1
theorem Q6a_monic : Q6a.Monic := by unfold Q6a; monicity!
theorem Q6a_degree : Q6a.degree = 6 := by unfold Q6a; compute_degree!
theorem Q6a_natDegree : Q6a.natDegree = 6 := by
  have := Q6a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6a; exact Q6a_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6a) :=
  AdjoinRoot.nontrivial Q6a (by rw [Q6a_degree]; decide)
instance : CharP (AdjoinRoot Q6a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6a)).injective) 2
/-- Root relation: `r^6 = r + 1`. -/
theorem root_Q6a : (AdjoinRoot.root Q6a) ^ 6 = AdjoinRoot.root Q6a + 1 := by
  have h0 : (AdjoinRoot.mk Q6a) Q6a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6a) Q6a = (AdjoinRoot.root Q6a) ^ 6 + AdjoinRoot.root Q6a + 1 := by
    unfold Q6a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6a) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6a + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X + 1`.** -/
theorem POLY_poly_no_deg6_factor_a : ¬ Q6a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6a with hr
  have hmkP : AdjoinRoot.mk Q6a POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r + 1 := root_Q6a
  have h2 : (2 : AdjoinRoot Q6a) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 2 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 3 + r ^ 2 := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 4 + r ^ 3 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r + 1 := by linear_combination r * h10 + h6
  have h12 : r ^ 12 = r ^ 2 + 1 := by linear_combination r * h11 + h6 + (r) * h2
  have h13 : r ^ 13 = r ^ 3 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 4 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 3 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r + 1 := by linear_combination r * h15 + h6
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by
    rw [h16, h12]; linear_combination (r + 1) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 + r ^ 2 + 1 = AdjoinRoot.mk Q6a (X ^ 4 + X ^ 3 + X ^ 2 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6a_degree]
    have hd : (X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #2: `X ^ 6 + X ^ 3 + 1`. -/
noncomputable def Q6b : (ZMod 2)[X] := X ^ 6 + X ^ 3 + 1
theorem Q6b_monic : Q6b.Monic := by unfold Q6b; monicity!
theorem Q6b_degree : Q6b.degree = 6 := by unfold Q6b; compute_degree!
theorem Q6b_natDegree : Q6b.natDegree = 6 := by
  have := Q6b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6b; exact Q6b_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6b) :=
  AdjoinRoot.nontrivial Q6b (by rw [Q6b_degree]; decide)
instance : CharP (AdjoinRoot Q6b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6b)).injective) 2
/-- Root relation: `r^6 = r ^ 3 + 1`. -/
theorem root_Q6b : (AdjoinRoot.root Q6b) ^ 6 = AdjoinRoot.root Q6b ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q6b) Q6b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6b) Q6b = (AdjoinRoot.root Q6b) ^ 6 + (AdjoinRoot.root Q6b) ^ 3 + 1 := by
    unfold Q6b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6b) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6b ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg6_factor_b : ¬ Q6b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6b with hr
  have hmkP : AdjoinRoot.mk Q6b POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 3 + 1 := root_Q6b
  have h2 : (2 : AdjoinRoot Q6b) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 4 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 5 + r ^ 2 := by linear_combination r * h7
  have h9 : r ^ 9 = 1 := by linear_combination r * h8 + h6 + (r ^ 3) * h2
  have h10 : r ^ 10 = r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 3 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 5 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 3 + 1 := by linear_combination r * h14 + h6
  have h16 : r ^ 16 = r ^ 4 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 4 + 1 = AdjoinRoot.mk Q6b (X ^ 4 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6b_degree]
    have hd : (X ^ 4 + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #3: `X ^ 6 + X ^ 4 + X ^ 2 + X + 1`. -/
noncomputable def Q6c : (ZMod 2)[X] := X ^ 6 + X ^ 4 + X ^ 2 + X + 1
theorem Q6c_monic : Q6c.Monic := by unfold Q6c; monicity!
theorem Q6c_degree : Q6c.degree = 6 := by unfold Q6c; compute_degree!
theorem Q6c_natDegree : Q6c.natDegree = 6 := by
  have := Q6c_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6c; exact Q6c_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6c) :=
  AdjoinRoot.nontrivial Q6c (by rw [Q6c_degree]; decide)
instance : CharP (AdjoinRoot Q6c) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6c)).injective) 2
/-- Root relation: `r^6 = r ^ 4 + r ^ 2 + r + 1`. -/
theorem root_Q6c : (AdjoinRoot.root Q6c) ^ 6 = AdjoinRoot.root Q6c ^ 4 + AdjoinRoot.root Q6c ^ 2 + AdjoinRoot.root Q6c + 1 := by
  have h0 : (AdjoinRoot.mk Q6c) Q6c = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6c) Q6c = (AdjoinRoot.root Q6c) ^ 6 + (AdjoinRoot.root Q6c) ^ 4 + (AdjoinRoot.root Q6c) ^ 2 + AdjoinRoot.root Q6c + 1 := by
    unfold Q6c; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6c) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6c ^ 4 + AdjoinRoot.root Q6c ^ 2 + AdjoinRoot.root Q6c + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 4 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg6_factor_c : ¬ Q6c ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6c with hr
  have hmkP : AdjoinRoot.mk Q6c POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 4 + r ^ 2 + r + 1 := root_Q6c
  have h2 : (2 : AdjoinRoot Q6c) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 3 + r + 1 := by linear_combination r * h7 + h6 + (r ^ 4 + r ^ 2) * h2
  have h9 : r ^ 9 = r ^ 4 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h6 + (r ^ 4) * h2
  have h12 : r ^ 12 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h13 + h6 + (r ^ 4) * h2
  have h15 : r ^ 15 = r ^ 3 + 1 := by linear_combination r * h14 + h6 + (r ^ 4 + r ^ 2 + r) * h2
  have h16 : r ^ 16 = r ^ 4 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 2 + r + 1 = AdjoinRoot.mk Q6c (X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 2 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6c_degree]
    have hd : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #4: `X ^ 6 + X ^ 4 + X ^ 3 + X + 1`. -/
noncomputable def Q6d : (ZMod 2)[X] := X ^ 6 + X ^ 4 + X ^ 3 + X + 1
theorem Q6d_monic : Q6d.Monic := by unfold Q6d; monicity!
theorem Q6d_degree : Q6d.degree = 6 := by unfold Q6d; compute_degree!
theorem Q6d_natDegree : Q6d.natDegree = 6 := by
  have := Q6d_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6d; exact Q6d_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6d) :=
  AdjoinRoot.nontrivial Q6d (by rw [Q6d_degree]; decide)
instance : CharP (AdjoinRoot Q6d) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6d)).injective) 2
/-- Root relation: `r^6 = r ^ 4 + r ^ 3 + r + 1`. -/
theorem root_Q6d : (AdjoinRoot.root Q6d) ^ 6 = AdjoinRoot.root Q6d ^ 4 + AdjoinRoot.root Q6d ^ 3 + AdjoinRoot.root Q6d + 1 := by
  have h0 : (AdjoinRoot.mk Q6d) Q6d = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6d) Q6d = (AdjoinRoot.root Q6d) ^ 6 + (AdjoinRoot.root Q6d) ^ 4 + (AdjoinRoot.root Q6d) ^ 3 + AdjoinRoot.root Q6d + 1 := by
    unfold Q6d; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6d) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6d ^ 4 + AdjoinRoot.root Q6d ^ 3 + AdjoinRoot.root Q6d + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 4 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg6_factor_d : ¬ Q6d ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6d with hr
  have hmkP : AdjoinRoot.mk Q6d POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 4 + r ^ 3 + r + 1 := root_Q6d
  have h2 : (2 : AdjoinRoot Q6d) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h6
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h7 + h6 + (r ^ 3) * h2
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h8 + h6 + (r ^ 3 + r) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + 1 := by linear_combination r * h9 + h6 + (r ^ 3 + r) * h2
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h10 + h6 + (r) * h2
  have h12 : r ^ 12 = r ^ 5 + r ^ 3 + 1 := by linear_combination r * h11 + h6 + (r ^ 4 + r) * h2
  have h13 : r ^ 13 = r ^ 3 + 1 := by linear_combination r * h12 + h6 + (r ^ 4 + r) * h2
  have h14 : r ^ 14 = r ^ 4 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r + 1 := by linear_combination r * h15 + h6 + (r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + 1 = AdjoinRoot.mk Q6d (X ^ 5 + X ^ 4 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6d_degree]
    have hd : (X ^ 5 + X ^ 4 + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #5: `X ^ 6 + X ^ 5 + 1`. -/
noncomputable def Q6e : (ZMod 2)[X] := X ^ 6 + X ^ 5 + 1
theorem Q6e_monic : Q6e.Monic := by unfold Q6e; monicity!
theorem Q6e_degree : Q6e.degree = 6 := by unfold Q6e; compute_degree!
theorem Q6e_natDegree : Q6e.natDegree = 6 := by
  have := Q6e_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6e; exact Q6e_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6e) :=
  AdjoinRoot.nontrivial Q6e (by rw [Q6e_degree]; decide)
instance : CharP (AdjoinRoot Q6e) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6e)).injective) 2
/-- Root relation: `r^6 = r ^ 5 + 1`. -/
theorem root_Q6e : (AdjoinRoot.root Q6e) ^ 6 = AdjoinRoot.root Q6e ^ 5 + 1 := by
  have h0 : (AdjoinRoot.mk Q6e) Q6e = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6e) Q6e = (AdjoinRoot.root Q6e) ^ 6 + (AdjoinRoot.root Q6e) ^ 5 + 1 := by
    unfold Q6e; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6e) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6e ^ 5 + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 5 + 1`.** -/
theorem POLY_poly_no_deg6_factor_e : ¬ Q6e ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6e with hr
  have hmkP : AdjoinRoot.mk Q6e POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 5 + 1 := root_Q6e
  have h2 : (2 : AdjoinRoot Q6e) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 5 + r + 1 := by linear_combination r * h6 + h6
  have h8 : r ^ 8 = r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h7 + h6
  have h9 : r ^ 9 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h8 + h6
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h9 + h6
  have h11 : r ^ 11 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h6 + (r ^ 5) * h2
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h6 + (r ^ 5) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h14 + h6 + (r ^ 5) * h2
  have h16 : r ^ 16 = r ^ 5 + r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 5 + r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = AdjoinRoot.mk Q6e (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6e_degree]
    have hd : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #6: `X ^ 6 + X ^ 5 + X ^ 2 + X + 1`. -/
noncomputable def Q6f : (ZMod 2)[X] := X ^ 6 + X ^ 5 + X ^ 2 + X + 1
theorem Q6f_monic : Q6f.Monic := by unfold Q6f; monicity!
theorem Q6f_degree : Q6f.degree = 6 := by unfold Q6f; compute_degree!
theorem Q6f_natDegree : Q6f.natDegree = 6 := by
  have := Q6f_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6f; exact Q6f_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6f) :=
  AdjoinRoot.nontrivial Q6f (by rw [Q6f_degree]; decide)
instance : CharP (AdjoinRoot Q6f) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6f)).injective) 2
/-- Root relation: `r^6 = r ^ 5 + r ^ 2 + r + 1`. -/
theorem root_Q6f : (AdjoinRoot.root Q6f) ^ 6 = AdjoinRoot.root Q6f ^ 5 + AdjoinRoot.root Q6f ^ 2 + AdjoinRoot.root Q6f + 1 := by
  have h0 : (AdjoinRoot.mk Q6f) Q6f = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6f) Q6f = (AdjoinRoot.root Q6f) ^ 6 + (AdjoinRoot.root Q6f) ^ 5 + (AdjoinRoot.root Q6f) ^ 2 + AdjoinRoot.root Q6f + 1 := by
    unfold Q6f; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6f) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6f ^ 5 + AdjoinRoot.root Q6f ^ 2 + AdjoinRoot.root Q6f + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 5 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg6_factor_f : ¬ Q6f ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6f with hr
  have hmkP : AdjoinRoot.mk Q6f POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 5 + r ^ 2 + r + 1 := root_Q6f
  have h2 : (2 : AdjoinRoot Q6f) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 5 + r ^ 3 + 1 := by linear_combination r * h6 + h6 + (r ^ 2 + r) * h2
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h7 + h6 + (r) * h2
  have h9 : r ^ 9 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h8 + h6 + (r ^ 5 + r) * h2
  have h10 : r ^ 10 = r ^ 4 + r ^ 3 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h6 + (r ^ 5) * h2
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h14 + h6 + (r ^ 5) * h2
  have h16 : r ^ 16 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r ^ 2 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r = AdjoinRoot.mk Q6f (X ^ 5 + X ^ 4 + X ^ 3 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6f_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #7: `X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q6g : (ZMod 2)[X] := X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + 1
theorem Q6g_monic : Q6g.Monic := by unfold Q6g; monicity!
theorem Q6g_degree : Q6g.degree = 6 := by unfold Q6g; compute_degree!
theorem Q6g_natDegree : Q6g.natDegree = 6 := by
  have := Q6g_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6g; exact Q6g_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6g) :=
  AdjoinRoot.nontrivial Q6g (by rw [Q6g_degree]; decide)
instance : CharP (AdjoinRoot Q6g) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6g)).injective) 2
/-- Root relation: `r^6 = r ^ 5 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q6g : (AdjoinRoot.root Q6g) ^ 6 = AdjoinRoot.root Q6g ^ 5 + AdjoinRoot.root Q6g ^ 3 + AdjoinRoot.root Q6g ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q6g) Q6g = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6g) Q6g = (AdjoinRoot.root Q6g) ^ 6 + (AdjoinRoot.root Q6g) ^ 5 + (AdjoinRoot.root Q6g) ^ 3 + (AdjoinRoot.root Q6g) ^ 2 + 1 := by
    unfold Q6g; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6g) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6g ^ 5 + AdjoinRoot.root Q6g ^ 3 + AdjoinRoot.root Q6g ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg6_factor_g : ¬ Q6g ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6g with hr
  have hmkP : AdjoinRoot.mk Q6g POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 5 + r ^ 3 + r ^ 2 + 1 := root_Q6g
  have h2 : (2 : AdjoinRoot Q6g) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h6 + h6 + (r ^ 3) * h2
  have h8 : r ^ 8 = r + 1 := by linear_combination r * h7 + h6 + (r ^ 5 + r ^ 3 + r ^ 2) * h2
  have h9 : r ^ 9 = r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 4 + r ^ 3 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h6 + (r ^ 5) * h2
  have h14 : r ^ 14 = r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 2 + 1 := by linear_combination r * h15 + h6 + (r ^ 5 + r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q6g (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6g_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #8: `X ^ 6 + X ^ 5 + X ^ 4 + X + 1`. -/
noncomputable def Q6h : (ZMod 2)[X] := X ^ 6 + X ^ 5 + X ^ 4 + X + 1
theorem Q6h_monic : Q6h.Monic := by unfold Q6h; monicity!
theorem Q6h_degree : Q6h.degree = 6 := by unfold Q6h; compute_degree!
theorem Q6h_natDegree : Q6h.natDegree = 6 := by
  have := Q6h_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6h; exact Q6h_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6h) :=
  AdjoinRoot.nontrivial Q6h (by rw [Q6h_degree]; decide)
instance : CharP (AdjoinRoot Q6h) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6h)).injective) 2
/-- Root relation: `r^6 = r ^ 5 + r ^ 4 + r + 1`. -/
theorem root_Q6h : (AdjoinRoot.root Q6h) ^ 6 = AdjoinRoot.root Q6h ^ 5 + AdjoinRoot.root Q6h ^ 4 + AdjoinRoot.root Q6h + 1 := by
  have h0 : (AdjoinRoot.mk Q6h) Q6h = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6h) Q6h = (AdjoinRoot.root Q6h) ^ 6 + (AdjoinRoot.root Q6h) ^ 5 + (AdjoinRoot.root Q6h) ^ 4 + AdjoinRoot.root Q6h + 1 := by
    unfold Q6h; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6h) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6h ^ 5 + AdjoinRoot.root Q6h ^ 4 + AdjoinRoot.root Q6h + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 5 + X ^ 4 + X + 1`.** -/
theorem POLY_poly_no_deg6_factor_h : ¬ Q6h ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6h with hr
  have hmkP : AdjoinRoot.mk Q6h POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 5 + r ^ 4 + r + 1 := root_Q6h
  have h2 : (2 : AdjoinRoot Q6h) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h6 + h6 + (r ^ 5 + r) * h2
  have h8 : r ^ 8 = r ^ 5 + r ^ 3 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h8 + h6 + (r ^ 4) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h9 + h6 + (r) * h2
  have h11 : r ^ 11 = r ^ 3 + 1 := by linear_combination r * h10 + h6 + (r ^ 5 + r ^ 4 + r) * h2
  have h12 : r ^ 12 = r ^ 4 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 5 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h13 + h6
  have h15 : r ^ 15 = r ^ 2 + 1 := by linear_combination r * h14 + h6 + (r ^ 5 + r ^ 4 + r) * h2
  have h16 : r ^ 16 = r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 4 + r + 1 = AdjoinRoot.mk Q6h (X ^ 4 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6h_degree]
    have hd : (X ^ 4 + X + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-6 #9: `X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1`. -/
noncomputable def Q6i : (ZMod 2)[X] := X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1
theorem Q6i_monic : Q6i.Monic := by unfold Q6i; monicity!
theorem Q6i_degree : Q6i.degree = 6 := by unfold Q6i; compute_degree!
theorem Q6i_natDegree : Q6i.natDegree = 6 := by
  have := Q6i_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q6i; exact Q6i_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q6i) :=
  AdjoinRoot.nontrivial Q6i (by rw [Q6i_degree]; decide)
instance : CharP (AdjoinRoot Q6i) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q6i)).injective) 2
/-- Root relation: `r^6 = r ^ 5 + r ^ 4 + r ^ 2 + 1`. -/
theorem root_Q6i : (AdjoinRoot.root Q6i) ^ 6 = AdjoinRoot.root Q6i ^ 5 + AdjoinRoot.root Q6i ^ 4 + AdjoinRoot.root Q6i ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q6i) Q6i = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q6i) Q6i = (AdjoinRoot.root Q6i) ^ 6 + (AdjoinRoot.root Q6i) ^ 5 + (AdjoinRoot.root Q6i) ^ 4 + (AdjoinRoot.root Q6i) ^ 2 + 1 := by
    unfold Q6i; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q6i) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q6i ^ 5 + AdjoinRoot.root Q6i ^ 4 + AdjoinRoot.root Q6i ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-6 factor `X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg6_factor_i : ¬ Q6i ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q6i with hr
  have hmkP : AdjoinRoot.mk Q6i POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h6 : r ^ 6 = r ^ 5 + r ^ 4 + r ^ 2 + 1 := root_Q6i
  have h2 : (2 : AdjoinRoot Q6i) = 0 := CharTwo.two_eq_zero
  have h7 : r ^ 7 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h6 + h6 + (r ^ 5) * h2
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 3 + 1 := by linear_combination r * h8 + h6 + (r ^ 5 + r ^ 4 + r ^ 2) * h2
  have h10 : r ^ 10 = r ^ 4 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h11 + h6
  have h13 : r ^ 13 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h6 + (r ^ 5 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h6 + (r ^ 5 + r ^ 4) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r ^ 2 + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r + 1 = AdjoinRoot.mk Q6i (X ^ 5 + X ^ 4 + X ^ 3 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q6i_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)
/-! ### Degree-7 stratum: no degree-7 factor

There are exactly 18 monic irreducible degree-7 polynomials over `ZMod 2`.
Each generates `GF(2^7)`; we evaluate `POLY_poly` at the root, climb `rⁿ = r·rⁿ⁻¹`
reducing the single `r^7` per step through the root relation (char-2 doublings corrected
by `2 = 0`), and certify the resulting degree-`<7` residue nonzero via
`mk_ne_zero_of_degree_lt`. No `decide` over `(ZMod 2)[X]`, no axiom. Closes the degree-7
stratum of the factor-exclusion criterion. -/

/-- Monic irreducible degree-7 #1: `X ^ 7 + X + 1`. -/
noncomputable def Q7a : (ZMod 2)[X] := X ^ 7 + X + 1
theorem Q7a_monic : Q7a.Monic := by unfold Q7a; monicity!
theorem Q7a_degree : Q7a.degree = 7 := by unfold Q7a; compute_degree!
theorem Q7a_natDegree : Q7a.natDegree = 7 := by
  have := Q7a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7a; exact Q7a_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7a) :=
  AdjoinRoot.nontrivial Q7a (by rw [Q7a_degree]; decide)
instance : CharP (AdjoinRoot Q7a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7a)).injective) 2
/-- Root relation: `r^7 = r + 1`. -/
theorem root_Q7a : (AdjoinRoot.root Q7a) ^ 7 = AdjoinRoot.root Q7a + 1 := by
  have h0 : (AdjoinRoot.mk Q7a) Q7a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7a) Q7a = (AdjoinRoot.root Q7a) ^ 7 + AdjoinRoot.root Q7a + 1 := by
    unfold Q7a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7a) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7a + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_a : ¬ Q7a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7a with hr
  have hmkP : AdjoinRoot.mk Q7a POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r + 1 := root_Q7a
  have h2 : (2 : AdjoinRoot Q7a) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 3 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 4 + r ^ 3 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r + 1 := by linear_combination r * h12 + h7
  have h14 : r ^ 14 = r ^ 2 + 1 := by linear_combination r * h13 + h7 + (r) * h2
  have h15 : r ^ 15 = r ^ 3 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 2 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
    rw [h16, h12]; ring
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = AdjoinRoot.mk Q7a (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7a_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #2: `X ^ 7 + X ^ 3 + 1`. -/
noncomputable def Q7b : (ZMod 2)[X] := X ^ 7 + X ^ 3 + 1
theorem Q7b_monic : Q7b.Monic := by unfold Q7b; monicity!
theorem Q7b_degree : Q7b.degree = 7 := by unfold Q7b; compute_degree!
theorem Q7b_natDegree : Q7b.natDegree = 7 := by
  have := Q7b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7b; exact Q7b_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7b) :=
  AdjoinRoot.nontrivial Q7b (by rw [Q7b_degree]; decide)
instance : CharP (AdjoinRoot Q7b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7b)).injective) 2
/-- Root relation: `r^7 = r ^ 3 + 1`. -/
theorem root_Q7b : (AdjoinRoot.root Q7b) ^ 7 = AdjoinRoot.root Q7b ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q7b) Q7b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7b) Q7b = (AdjoinRoot.root Q7b) ^ 7 + (AdjoinRoot.root Q7b) ^ 3 + 1 := by
    unfold Q7b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7b) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7b ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg7_factor_b : ¬ Q7b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7b with hr
  have hmkP : AdjoinRoot.mk Q7b POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 3 + 1 := root_Q7b
  have h2 : (2 : AdjoinRoot Q7b) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 4 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 5 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 3 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 4 + r ^ 3 + 1 := by linear_combination r * h10 + h7
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + 1 := by linear_combination r * h13 + h7 + (r ^ 3) * h2
  have h15 : r ^ 15 = r ^ 3 + r + 1 := by linear_combination r * h14 + h7
  have h16 : r ^ 16 = r ^ 4 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 3 + r ^ 2 + r + 1 = AdjoinRoot.mk Q7b (X ^ 5 + X ^ 3 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7b_degree]
    have hd : (X ^ 5 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #3: `X ^ 7 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q7c : (ZMod 2)[X] := X ^ 7 + X ^ 3 + X ^ 2 + X + 1
theorem Q7c_monic : Q7c.Monic := by unfold Q7c; monicity!
theorem Q7c_degree : Q7c.degree = 7 := by unfold Q7c; compute_degree!
theorem Q7c_natDegree : Q7c.natDegree = 7 := by
  have := Q7c_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7c; exact Q7c_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7c) :=
  AdjoinRoot.nontrivial Q7c (by rw [Q7c_degree]; decide)
instance : CharP (AdjoinRoot Q7c) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7c)).injective) 2
/-- Root relation: `r^7 = r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q7c : (AdjoinRoot.root Q7c) ^ 7 = AdjoinRoot.root Q7c ^ 3 + AdjoinRoot.root Q7c ^ 2 + AdjoinRoot.root Q7c + 1 := by
  have h0 : (AdjoinRoot.mk Q7c) Q7c = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7c) Q7c = (AdjoinRoot.root Q7c) ^ 7 + (AdjoinRoot.root Q7c) ^ 3 + (AdjoinRoot.root Q7c) ^ 2 + AdjoinRoot.root Q7c + 1 := by
    unfold Q7c; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7c) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7c ^ 3 + AdjoinRoot.root Q7c ^ 2 + AdjoinRoot.root Q7c + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_c : ¬ Q7c ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7c with hr
  have hmkP : AdjoinRoot.mk Q7c POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 3 + r ^ 2 + r + 1 := root_Q7c
  have h2 : (2 : AdjoinRoot Q7c) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h11 + h7 + (r ^ 3 + r ^ 2 + r) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h7 + (r) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h13 + h7 + (r ^ 3 + r) * h2
  have h15 : r ^ 15 = r ^ 5 + r ^ 2 + 1 := by linear_combination r * h14 + h7 + (r ^ 3 + r) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 = AdjoinRoot.mk Q7c (X ^ 5 + X ^ 4) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7c_degree]
    have hd : (X ^ 5 + X ^ 4 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #4: `X ^ 7 + X ^ 4 + 1`. -/
noncomputable def Q7d : (ZMod 2)[X] := X ^ 7 + X ^ 4 + 1
theorem Q7d_monic : Q7d.Monic := by unfold Q7d; monicity!
theorem Q7d_degree : Q7d.degree = 7 := by unfold Q7d; compute_degree!
theorem Q7d_natDegree : Q7d.natDegree = 7 := by
  have := Q7d_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7d; exact Q7d_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7d) :=
  AdjoinRoot.nontrivial Q7d (by rw [Q7d_degree]; decide)
instance : CharP (AdjoinRoot Q7d) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7d)).injective) 2
/-- Root relation: `r^7 = r ^ 4 + 1`. -/
theorem root_Q7d : (AdjoinRoot.root Q7d) ^ 7 = AdjoinRoot.root Q7d ^ 4 + 1 := by
  have h0 : (AdjoinRoot.mk Q7d) Q7d = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7d) Q7d = (AdjoinRoot.root Q7d) ^ 7 + (AdjoinRoot.root Q7d) ^ 4 + 1 := by
    unfold Q7d; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7d) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7d ^ 4 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 4 + 1`.** -/
theorem POLY_poly_no_deg7_factor_d : ¬ Q7d ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7d with hr
  have hmkP : AdjoinRoot.mk Q7d POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 4 + 1 := root_Q7d
  have h2 : (2 : AdjoinRoot Q7d) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 5 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 6 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 4 + r ^ 3 + 1 := by linear_combination r * h9 + h7
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h12 + h7
  have h14 : r ^ 14 = r ^ 5 + r + 1 := by linear_combination r * h13 + h7 + (r ^ 4) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h7
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r ^ 2 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r = AdjoinRoot.mk Q7d (X ^ 6 + X ^ 5 + X ^ 4 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7d_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #5: `X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q7e : (ZMod 2)[X] := X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q7e_monic : Q7e.Monic := by unfold Q7e; monicity!
theorem Q7e_degree : Q7e.degree = 7 := by unfold Q7e; compute_degree!
theorem Q7e_natDegree : Q7e.natDegree = 7 := by
  have := Q7e_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7e; exact Q7e_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7e) :=
  AdjoinRoot.nontrivial Q7e (by rw [Q7e_degree]; decide)
instance : CharP (AdjoinRoot Q7e) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7e)).injective) 2
/-- Root relation: `r^7 = r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q7e : (AdjoinRoot.root Q7e) ^ 7 = AdjoinRoot.root Q7e ^ 4 + AdjoinRoot.root Q7e ^ 3 + AdjoinRoot.root Q7e ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q7e) Q7e = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7e) Q7e = (AdjoinRoot.root Q7e) ^ 7 + (AdjoinRoot.root Q7e) ^ 4 + (AdjoinRoot.root Q7e) ^ 3 + (AdjoinRoot.root Q7e) ^ 2 + 1 := by
    unfold Q7e; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7e) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7e ^ 4 + AdjoinRoot.root Q7e ^ 3 + AdjoinRoot.root Q7e ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg7_factor_e : ¬ Q7e ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7e with hr
  have hmkP : AdjoinRoot.mk Q7e POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q7e
  have h2 : (2 : AdjoinRoot Q7e) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h9 + h7 + (r ^ 3) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7 + (r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 3 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h12 + h7 + (r ^ 2) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h13 + h7 + (r ^ 4 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h14 + h7 + (r ^ 4 + r ^ 2) * h2
  have h16 : r ^ 16 = r ^ 3 + r + 1 := by linear_combination r * h15 + h7 + (r ^ 4 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r + 1 = AdjoinRoot.mk Q7e (X ^ 6 + X ^ 5 + X ^ 4 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7e_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #6: `X ^ 7 + X ^ 5 + X ^ 2 + X + 1`. -/
noncomputable def Q7f : (ZMod 2)[X] := X ^ 7 + X ^ 5 + X ^ 2 + X + 1
theorem Q7f_monic : Q7f.Monic := by unfold Q7f; monicity!
theorem Q7f_degree : Q7f.degree = 7 := by unfold Q7f; compute_degree!
theorem Q7f_natDegree : Q7f.natDegree = 7 := by
  have := Q7f_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7f; exact Q7f_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7f) :=
  AdjoinRoot.nontrivial Q7f (by rw [Q7f_degree]; decide)
instance : CharP (AdjoinRoot Q7f) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7f)).injective) 2
/-- Root relation: `r^7 = r ^ 5 + r ^ 2 + r + 1`. -/
theorem root_Q7f : (AdjoinRoot.root Q7f) ^ 7 = AdjoinRoot.root Q7f ^ 5 + AdjoinRoot.root Q7f ^ 2 + AdjoinRoot.root Q7f + 1 := by
  have h0 : (AdjoinRoot.mk Q7f) Q7f = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7f) Q7f = (AdjoinRoot.root Q7f) ^ 7 + (AdjoinRoot.root Q7f) ^ 5 + (AdjoinRoot.root Q7f) ^ 2 + AdjoinRoot.root Q7f + 1 := by
    unfold Q7f; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7f) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7f ^ 5 + AdjoinRoot.root Q7f ^ 2 + AdjoinRoot.root Q7f + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 5 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_f : ¬ Q7f ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7f with hr
  have hmkP : AdjoinRoot.mk Q7f POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 5 + r ^ 2 + r + 1 := root_Q7f
  have h2 : (2 : AdjoinRoot Q7f) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 3 + r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h8 + h7 + (r ^ 2) * h2
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h10 + h7 + (r ^ 5 + r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + 1 := by linear_combination r * h11 + h7 + (r ^ 2 + r) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r + 1 := by linear_combination r * h13 + h7 + (r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 5 + 1 := by linear_combination r * h14 + h7 + (r ^ 2 + r) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 2 + 1 := by linear_combination r * h15 + h7 + (r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 5 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = AdjoinRoot.mk Q7f (X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7f_degree]
    have hd : (X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #7: `X ^ 7 + X ^ 5 + X ^ 3 + X + 1`. -/
noncomputable def Q7g : (ZMod 2)[X] := X ^ 7 + X ^ 5 + X ^ 3 + X + 1
theorem Q7g_monic : Q7g.Monic := by unfold Q7g; monicity!
theorem Q7g_degree : Q7g.degree = 7 := by unfold Q7g; compute_degree!
theorem Q7g_natDegree : Q7g.natDegree = 7 := by
  have := Q7g_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7g; exact Q7g_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7g) :=
  AdjoinRoot.nontrivial Q7g (by rw [Q7g_degree]; decide)
instance : CharP (AdjoinRoot Q7g) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7g)).injective) 2
/-- Root relation: `r^7 = r ^ 5 + r ^ 3 + r + 1`. -/
theorem root_Q7g : (AdjoinRoot.root Q7g) ^ 7 = AdjoinRoot.root Q7g ^ 5 + AdjoinRoot.root Q7g ^ 3 + AdjoinRoot.root Q7g + 1 := by
  have h0 : (AdjoinRoot.mk Q7g) Q7g = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7g) Q7g = (AdjoinRoot.root Q7g) ^ 7 + (AdjoinRoot.root Q7g) ^ 5 + (AdjoinRoot.root Q7g) ^ 3 + AdjoinRoot.root Q7g + 1 := by
    unfold Q7g; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7g) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7g ^ 5 + AdjoinRoot.root Q7g ^ 3 + AdjoinRoot.root Q7g + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 5 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_g : ¬ Q7g ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7g with hr
  have hmkP : AdjoinRoot.mk Q7g POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 5 + r ^ 3 + r + 1 := root_Q7g
  have h2 : (2 : AdjoinRoot Q7g) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 4 + r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 2 + r + 1 := by linear_combination r * h8 + h7 + (r ^ 5 + r ^ 3) * h2
  have h10 : r ^ 10 = r ^ 3 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 4 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h13 + h7 + (r ^ 5) * h2
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h14 + h7 + (r) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 3 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 5 + r ^ 4 + r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 3 + 1 = AdjoinRoot.mk Q7g (X ^ 6 + X ^ 3 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 3 + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7g_degree]
    have hd : (X ^ 6 + X ^ 3 + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #8: `X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1`. -/
noncomputable def Q7h : (ZMod 2)[X] := X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1
theorem Q7h_monic : Q7h.Monic := by unfold Q7h; monicity!
theorem Q7h_degree : Q7h.degree = 7 := by unfold Q7h; compute_degree!
theorem Q7h_natDegree : Q7h.natDegree = 7 := by
  have := Q7h_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7h; exact Q7h_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7h) :=
  AdjoinRoot.nontrivial Q7h (by rw [Q7h_degree]; decide)
instance : CharP (AdjoinRoot Q7h) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7h)).injective) 2
/-- Root relation: `r^7 = r ^ 5 + r ^ 4 + r ^ 3 + 1`. -/
theorem root_Q7h : (AdjoinRoot.root Q7h) ^ 7 = AdjoinRoot.root Q7h ^ 5 + AdjoinRoot.root Q7h ^ 4 + AdjoinRoot.root Q7h ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q7h) Q7h = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7h) Q7h = (AdjoinRoot.root Q7h) ^ 7 + (AdjoinRoot.root Q7h) ^ 5 + (AdjoinRoot.root Q7h) ^ 4 + (AdjoinRoot.root Q7h) ^ 3 + 1 := by
    unfold Q7h; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7h) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7h ^ 5 + AdjoinRoot.root Q7h ^ 4 + AdjoinRoot.root Q7h ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg7_factor_h : ¬ Q7h ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7h with hr
  have hmkP : AdjoinRoot.mk Q7h POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := root_Q7h
  have h2 : (2 : AdjoinRoot Q7h) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h8 + h7 + (r ^ 5) * h2
  have h10 : r ^ 10 = r + 1 := by linear_combination r * h9 + h7 + (r ^ 5 + r ^ 4 + r ^ 3) * h2
  have h11 : r ^ 11 = r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 3 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r ^ 5 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h15 + h7
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q7h (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7h_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #9: `X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q7i : (ZMod 2)[X] := X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
theorem Q7i_monic : Q7i.Monic := by unfold Q7i; monicity!
theorem Q7i_degree : Q7i.degree = 7 := by unfold Q7i; compute_degree!
theorem Q7i_natDegree : Q7i.natDegree = 7 := by
  have := Q7i_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7i; exact Q7i_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7i) :=
  AdjoinRoot.nontrivial Q7i (by rw [Q7i_degree]; decide)
instance : CharP (AdjoinRoot Q7i) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7i)).injective) 2
/-- Root relation: `r^7 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q7i : (AdjoinRoot.root Q7i) ^ 7 = AdjoinRoot.root Q7i ^ 5 + AdjoinRoot.root Q7i ^ 4 + AdjoinRoot.root Q7i ^ 3 + AdjoinRoot.root Q7i ^ 2 + AdjoinRoot.root Q7i + 1 := by
  have h0 : (AdjoinRoot.mk Q7i) Q7i = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7i) Q7i = (AdjoinRoot.root Q7i) ^ 7 + (AdjoinRoot.root Q7i) ^ 5 + (AdjoinRoot.root Q7i) ^ 4 + (AdjoinRoot.root Q7i) ^ 3 + (AdjoinRoot.root Q7i) ^ 2 + AdjoinRoot.root Q7i + 1 := by
    unfold Q7i; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7i) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7i ^ 5 + AdjoinRoot.root Q7i ^ 4 + AdjoinRoot.root Q7i ^ 3 + AdjoinRoot.root Q7i ^ 2 + AdjoinRoot.root Q7i + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_i : ¬ Q7i ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7i with hr
  have hmkP : AdjoinRoot.mk Q7i POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := root_Q7i
  have h2 : (2 : AdjoinRoot Q7i) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h7
  have h9 : r ^ 9 = r ^ 6 + r + 1 := by linear_combination r * h8 + h7 + (r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h9 + h7 + (r ^ 2 + r) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 5 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 3 + 1 := by linear_combination r * h12 + h7 + (r ^ 5 + r ^ 4 + r ^ 2 + r) * h2
  have h14 : r ^ 14 = r ^ 4 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 = AdjoinRoot.mk Q7i (X ^ 4 + X ^ 3) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7i_degree]
    have hd : (X ^ 4 + X ^ 3 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #10: `X ^ 7 + X ^ 6 + 1`. -/
noncomputable def Q7j : (ZMod 2)[X] := X ^ 7 + X ^ 6 + 1
theorem Q7j_monic : Q7j.Monic := by unfold Q7j; monicity!
theorem Q7j_degree : Q7j.degree = 7 := by unfold Q7j; compute_degree!
theorem Q7j_natDegree : Q7j.natDegree = 7 := by
  have := Q7j_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7j; exact Q7j_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7j) :=
  AdjoinRoot.nontrivial Q7j (by rw [Q7j_degree]; decide)
instance : CharP (AdjoinRoot Q7j) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7j)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + 1`. -/
theorem root_Q7j : (AdjoinRoot.root Q7j) ^ 7 = AdjoinRoot.root Q7j ^ 6 + 1 := by
  have h0 : (AdjoinRoot.mk Q7j) Q7j = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7j) Q7j = (AdjoinRoot.root Q7j) ^ 7 + (AdjoinRoot.root Q7j) ^ 6 + 1 := by
    unfold Q7j; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7j) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7j ^ 6 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + 1`.** -/
theorem POLY_poly_no_deg7_factor_j : ¬ Q7j ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7j with hr
  have hmkP : AdjoinRoot.mk Q7j POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + 1 := root_Q7j
  have h2 : (2 : AdjoinRoot Q7j) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r + 1 := by linear_combination r * h7 + h7
  have h9 : r ^ 9 = r ^ 6 + r ^ 2 + r + 1 := by linear_combination r * h8 + h7
  have h10 : r ^ 10 = r ^ 6 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h9 + h7
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h7
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h7 + (r ^ 6) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h14 + h7 + (r ^ 6) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q7j (X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 3 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7j_degree]
    have hd : (X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 3 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #11: `X ^ 7 + X ^ 6 + X ^ 3 + X + 1`. -/
noncomputable def Q7k : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 3 + X + 1
theorem Q7k_monic : Q7k.Monic := by unfold Q7k; monicity!
theorem Q7k_degree : Q7k.degree = 7 := by unfold Q7k; compute_degree!
theorem Q7k_natDegree : Q7k.natDegree = 7 := by
  have := Q7k_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7k; exact Q7k_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7k) :=
  AdjoinRoot.nontrivial Q7k (by rw [Q7k_degree]; decide)
instance : CharP (AdjoinRoot Q7k) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7k)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 3 + r + 1`. -/
theorem root_Q7k : (AdjoinRoot.root Q7k) ^ 7 = AdjoinRoot.root Q7k ^ 6 + AdjoinRoot.root Q7k ^ 3 + AdjoinRoot.root Q7k + 1 := by
  have h0 : (AdjoinRoot.mk Q7k) Q7k = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7k) Q7k = (AdjoinRoot.root Q7k) ^ 7 + (AdjoinRoot.root Q7k) ^ 6 + (AdjoinRoot.root Q7k) ^ 3 + AdjoinRoot.root Q7k + 1 := by
    unfold Q7k; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7k) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7k ^ 6 + AdjoinRoot.root Q7k ^ 3 + AdjoinRoot.root Q7k + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_k : ¬ Q7k ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7k with hr
  have hmkP : AdjoinRoot.mk Q7k POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 3 + r + 1 := root_Q7k
  have h2 : (2 : AdjoinRoot Q7k) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h7 + h7 + (r) * h2
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h8 + h7 + (r ^ 3 + r) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 3 + 1 := by linear_combination r * h9 + h7 + (r ^ 6 + r) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h7
  have h13 : r ^ 13 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h12 + h7 + (r ^ 6 + r ^ 3 + r) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r + 1 := by linear_combination r * h15 + h7 + (r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 5 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 2 + r + 1 = AdjoinRoot.mk Q7k (X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 2 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7k_degree]
    have hd : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #12: `X ^ 7 + X ^ 6 + X ^ 4 + X + 1`. -/
noncomputable def Q7l : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 4 + X + 1
theorem Q7l_monic : Q7l.Monic := by unfold Q7l; monicity!
theorem Q7l_degree : Q7l.degree = 7 := by unfold Q7l; compute_degree!
theorem Q7l_natDegree : Q7l.natDegree = 7 := by
  have := Q7l_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7l; exact Q7l_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7l) :=
  AdjoinRoot.nontrivial Q7l (by rw [Q7l_degree]; decide)
instance : CharP (AdjoinRoot Q7l) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7l)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 4 + r + 1`. -/
theorem root_Q7l : (AdjoinRoot.root Q7l) ^ 7 = AdjoinRoot.root Q7l ^ 6 + AdjoinRoot.root Q7l ^ 4 + AdjoinRoot.root Q7l + 1 := by
  have h0 : (AdjoinRoot.mk Q7l) Q7l = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7l) Q7l = (AdjoinRoot.root Q7l) ^ 7 + (AdjoinRoot.root Q7l) ^ 6 + (AdjoinRoot.root Q7l) ^ 4 + AdjoinRoot.root Q7l + 1 := by
    unfold Q7l; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7l) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7l ^ 6 + AdjoinRoot.root Q7l ^ 4 + AdjoinRoot.root Q7l + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 4 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_l : ¬ Q7l ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7l with hr
  have hmkP : AdjoinRoot.mk Q7l POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 4 + r + 1 := root_Q7l
  have h2 : (2 : AdjoinRoot Q7l) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h7 + h7 + (r) * h2
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h8 + h7 + (r ^ 6 + r) * h2
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7 + (r ^ 6) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h7 + (r ^ 6 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 5 + r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 4 + r ^ 3 + r ^ 2 + 1 = AdjoinRoot.mk Q7l (X ^ 4 + X ^ 3 + X ^ 2 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 4 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7l_degree]
    have hd : (X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 4 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #13: `X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + 1`. -/
noncomputable def Q7m : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + 1
theorem Q7m_monic : Q7m.Monic := by unfold Q7m; monicity!
theorem Q7m_degree : Q7m.degree = 7 := by unfold Q7m; compute_degree!
theorem Q7m_natDegree : Q7m.natDegree = 7 := by
  have := Q7m_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7m; exact Q7m_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7m) :=
  AdjoinRoot.nontrivial Q7m (by rw [Q7m_degree]; decide)
instance : CharP (AdjoinRoot Q7m) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7m)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 4 + r ^ 2 + 1`. -/
theorem root_Q7m : (AdjoinRoot.root Q7m) ^ 7 = AdjoinRoot.root Q7m ^ 6 + AdjoinRoot.root Q7m ^ 4 + AdjoinRoot.root Q7m ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q7m) Q7m = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7m) Q7m = (AdjoinRoot.root Q7m) ^ 7 + (AdjoinRoot.root Q7m) ^ 6 + (AdjoinRoot.root Q7m) ^ 4 + (AdjoinRoot.root Q7m) ^ 2 + 1 := by
    unfold Q7m; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7m) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7m ^ 6 + AdjoinRoot.root Q7m ^ 4 + AdjoinRoot.root Q7m ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg7_factor_m : ¬ Q7m ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7m with hr
  have hmkP : AdjoinRoot.mk Q7m POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 4 + r ^ 2 + 1 := root_Q7m
  have h2 : (2 : AdjoinRoot Q7m) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h7 + h7
  have h9 : r ^ 9 = r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h8 + h7 + (r ^ 6 + r ^ 4 + r ^ 2) * h2
  have h10 : r ^ 10 = r ^ 6 + r ^ 4 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h10 + h7 + (r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 6 + r ^ 4) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 3 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 3 + 1 := by linear_combination r * h13 + h7 + (r ^ 4 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 2 + r + 1 := by linear_combination r * h14 + h7 + (r ^ 4) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h15 + h7 + (r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 = AdjoinRoot.mk Q7m (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7m_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #14: `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + 1`. -/
noncomputable def Q7n : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + 1
theorem Q7n_monic : Q7n.Monic := by unfold Q7n; monicity!
theorem Q7n_degree : Q7n.degree = 7 := by unfold Q7n; compute_degree!
theorem Q7n_natDegree : Q7n.natDegree = 7 := by
  have := Q7n_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7n; exact Q7n_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7n) :=
  AdjoinRoot.nontrivial Q7n (by rw [Q7n_degree]; decide)
instance : CharP (AdjoinRoot Q7n) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7n)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 5 + r ^ 2 + 1`. -/
theorem root_Q7n : (AdjoinRoot.root Q7n) ^ 7 = AdjoinRoot.root Q7n ^ 6 + AdjoinRoot.root Q7n ^ 5 + AdjoinRoot.root Q7n ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q7n) Q7n = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7n) Q7n = (AdjoinRoot.root Q7n) ^ 7 + (AdjoinRoot.root Q7n) ^ 6 + (AdjoinRoot.root Q7n) ^ 5 + (AdjoinRoot.root Q7n) ^ 2 + 1 := by
    unfold Q7n; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7n) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7n ^ 6 + AdjoinRoot.root Q7n ^ 5 + AdjoinRoot.root Q7n ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg7_factor_n : ¬ Q7n ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7n with hr
  have hmkP : AdjoinRoot.mk Q7n POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 5 + r ^ 2 + 1 := root_Q7n
  have h2 : (2 : AdjoinRoot Q7n) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h7 + h7 + (r ^ 6) * h2
  have h9 : r ^ 9 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h9 + h7 + (r ^ 5 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7 + (r ^ 5) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 5 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h12 + h7 + (r ^ 2) * h2
  have h14 : r ^ 14 = r + 1 := by linear_combination r * h13 + h7 + (r ^ 6 + r ^ 5 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 3 + r ^ 2 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q7n (X ^ 6 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7n_degree]
    have hd : (X ^ 6 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #15: `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q7o : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X + 1
theorem Q7o_monic : Q7o.Monic := by unfold Q7o; monicity!
theorem Q7o_degree : Q7o.degree = 7 := by unfold Q7o; compute_degree!
theorem Q7o_natDegree : Q7o.natDegree = 7 := by
  have := Q7o_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7o; exact Q7o_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7o) :=
  AdjoinRoot.nontrivial Q7o (by rw [Q7o_degree]; decide)
instance : CharP (AdjoinRoot Q7o) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7o)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q7o : (AdjoinRoot.root Q7o) ^ 7 = AdjoinRoot.root Q7o ^ 6 + AdjoinRoot.root Q7o ^ 5 + AdjoinRoot.root Q7o ^ 3 + AdjoinRoot.root Q7o ^ 2 + AdjoinRoot.root Q7o + 1 := by
  have h0 : (AdjoinRoot.mk Q7o) Q7o = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7o) Q7o = (AdjoinRoot.root Q7o) ^ 7 + (AdjoinRoot.root Q7o) ^ 6 + (AdjoinRoot.root Q7o) ^ 5 + (AdjoinRoot.root Q7o) ^ 3 + (AdjoinRoot.root Q7o) ^ 2 + AdjoinRoot.root Q7o + 1 := by
    unfold Q7o; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7o) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7o ^ 6 + AdjoinRoot.root Q7o ^ 5 + AdjoinRoot.root Q7o ^ 3 + AdjoinRoot.root Q7o ^ 2 + AdjoinRoot.root Q7o + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_o : ¬ Q7o ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7o with hr
  have hmkP : AdjoinRoot.mk Q7o POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := root_Q7o
  have h2 : (2 : AdjoinRoot Q7o) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + 1 := by linear_combination r * h7 + h7 + (r ^ 6 + r ^ 3 + r ^ 2 + r) * h2
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h9 + h7 + (r ^ 6 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 5 + r ^ 3 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h12 + h7 + (r ^ 2 + r) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h13 + h7 + (r ^ 6 + r) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h15 + h7 + (r ^ 6 + r ^ 5 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 4 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 4 + r + 1 = AdjoinRoot.mk Q7o (X ^ 6 + X ^ 4 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 4 + X + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7o_degree]
    have hd : (X ^ 6 + X ^ 4 + X + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #16: `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + 1`. -/
noncomputable def Q7p : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + 1
theorem Q7p_monic : Q7p.Monic := by unfold Q7p; monicity!
theorem Q7p_degree : Q7p.degree = 7 := by unfold Q7p; compute_degree!
theorem Q7p_natDegree : Q7p.natDegree = 7 := by
  have := Q7p_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7p; exact Q7p_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7p) :=
  AdjoinRoot.nontrivial Q7p (by rw [Q7p_degree]; decide)
instance : CharP (AdjoinRoot Q7p) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7p)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 5 + r ^ 4 + 1`. -/
theorem root_Q7p : (AdjoinRoot.root Q7p) ^ 7 = AdjoinRoot.root Q7p ^ 6 + AdjoinRoot.root Q7p ^ 5 + AdjoinRoot.root Q7p ^ 4 + 1 := by
  have h0 : (AdjoinRoot.mk Q7p) Q7p = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7p) Q7p = (AdjoinRoot.root Q7p) ^ 7 + (AdjoinRoot.root Q7p) ^ 6 + (AdjoinRoot.root Q7p) ^ 5 + (AdjoinRoot.root Q7p) ^ 4 + 1 := by
    unfold Q7p; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7p) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7p ^ 6 + AdjoinRoot.root Q7p ^ 5 + AdjoinRoot.root Q7p ^ 4 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + 1`.** -/
theorem POLY_poly_no_deg7_factor_p : ¬ Q7p ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7p with hr
  have hmkP : AdjoinRoot.mk Q7p POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 5 + r ^ 4 + 1 := root_Q7p
  have h2 : (2 : AdjoinRoot Q7p) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 4 + r + 1 := by linear_combination r * h7 + h7 + (r ^ 6 + r ^ 5) * h2
  have h9 : r ^ 9 = r ^ 5 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h10 + h7 + (r ^ 4) * h2
  have h12 : r ^ 12 = r ^ 5 + r + 1 := by linear_combination r * h11 + h7 + (r ^ 6 + r ^ 4) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h13 + h7
  have h15 : r ^ 15 = r ^ 3 + r + 1 := by linear_combination r * h14 + h7 + (r ^ 6 + r ^ 5 + r ^ 4) * h2
  have h16 : r ^ 16 = r ^ 4 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q7p (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7p_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #17: `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1`. -/
noncomputable def Q7q : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1
theorem Q7q_monic : Q7q.Monic := by unfold Q7q; monicity!
theorem Q7q_degree : Q7q.degree = 7 := by unfold Q7q; compute_degree!
theorem Q7q_natDegree : Q7q.natDegree = 7 := by
  have := Q7q_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7q; exact Q7q_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7q) :=
  AdjoinRoot.nontrivial Q7q (by rw [Q7q_degree]; decide)
instance : CharP (AdjoinRoot Q7q) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7q)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1`. -/
theorem root_Q7q : (AdjoinRoot.root Q7q) ^ 7 = AdjoinRoot.root Q7q ^ 6 + AdjoinRoot.root Q7q ^ 5 + AdjoinRoot.root Q7q ^ 4 + AdjoinRoot.root Q7q ^ 2 + AdjoinRoot.root Q7q + 1 := by
  have h0 : (AdjoinRoot.mk Q7q) Q7q = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7q) Q7q = (AdjoinRoot.root Q7q) ^ 7 + (AdjoinRoot.root Q7q) ^ 6 + (AdjoinRoot.root Q7q) ^ 5 + (AdjoinRoot.root Q7q) ^ 4 + (AdjoinRoot.root Q7q) ^ 2 + AdjoinRoot.root Q7q + 1 := by
    unfold Q7q; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7q) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7q ^ 6 + AdjoinRoot.root Q7q ^ 5 + AdjoinRoot.root Q7q ^ 4 + AdjoinRoot.root Q7q ^ 2 + AdjoinRoot.root Q7q + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg7_factor_q : ¬ Q7q ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7q with hr
  have hmkP : AdjoinRoot.mk Q7q POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := root_Q7q
  have h2 : (2 : AdjoinRoot Q7q) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + 1 := by linear_combination r * h7 + h7 + (r ^ 6 + r ^ 5 + r ^ 2 + r) * h2
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h10 + h7 + (r ^ 6) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 3 + r + 1 := by linear_combination r * h12 + h7 + (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2) * h2
  have h14 : r ^ 14 = r ^ 4 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 4 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 3 + r ^ 2 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 4 + r ^ 3 + r) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 3 + r ^ 2 + 1 = AdjoinRoot.mk Q7q (X ^ 5 + X ^ 3 + X ^ 2 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7q_degree]
    have hd : (X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-7 #18: `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q7r : (ZMod 2)[X] := X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q7r_monic : Q7r.Monic := by unfold Q7r; monicity!
theorem Q7r_degree : Q7r.degree = 7 := by unfold Q7r; compute_degree!
theorem Q7r_natDegree : Q7r.natDegree = 7 := by
  have := Q7r_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q7r; exact Q7r_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q7r) :=
  AdjoinRoot.nontrivial Q7r (by rw [Q7r_degree]; decide)
instance : CharP (AdjoinRoot Q7r) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q7r)).injective) 2
/-- Root relation: `r^7 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q7r : (AdjoinRoot.root Q7r) ^ 7 = AdjoinRoot.root Q7r ^ 6 + AdjoinRoot.root Q7r ^ 5 + AdjoinRoot.root Q7r ^ 4 + AdjoinRoot.root Q7r ^ 3 + AdjoinRoot.root Q7r ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q7r) Q7r = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q7r) Q7r = (AdjoinRoot.root Q7r) ^ 7 + (AdjoinRoot.root Q7r) ^ 6 + (AdjoinRoot.root Q7r) ^ 5 + (AdjoinRoot.root Q7r) ^ 4 + (AdjoinRoot.root Q7r) ^ 3 + (AdjoinRoot.root Q7r) ^ 2 + 1 := by
    unfold Q7r; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q7r) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q7r ^ 6 + AdjoinRoot.root Q7r ^ 5 + AdjoinRoot.root Q7r ^ 4 + AdjoinRoot.root Q7r ^ 3 + AdjoinRoot.root Q7r ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-7 factor `X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg7_factor_r : ¬ Q7r ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q7r with hr
  have hmkP : AdjoinRoot.mk Q7r POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h7 : r ^ 7 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q7r
  have h2 : (2 : AdjoinRoot Q7r) = 0 := CharTwo.two_eq_zero
  have h8 : r ^ 8 = r ^ 2 + r + 1 := by linear_combination r * h7 + h7 + (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3) * h2
  have h9 : r ^ 9 = r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 4 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h7 + (r ^ 6 + r ^ 5) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h15 + h7 + (r ^ 6 + r ^ 5 + r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 4 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q7r (X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q7r_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)
/-! ### Degree-8 stratum: no degree-8 factor

There are exactly 30 monic irreducible degree-8 polynomials over `ZMod 2`.
Each generates `GF(2^8)`; we evaluate `POLY_poly` at the root, climb `rⁿ = r·rⁿ⁻¹`
reducing the single `r^8` per step through the root relation (char-2 doublings corrected
by `2 = 0`), and certify the resulting degree-`<8` residue nonzero via
`mk_ne_zero_of_degree_lt`. No `decide` over `(ZMod 2)[X]`, no axiom. Closes the degree-8
stratum of the factor-exclusion criterion. -/

/-- Monic irreducible degree-8 #1: `X ^ 8 + X ^ 4 + X ^ 3 + X + 1`. -/
noncomputable def Q8a : (ZMod 2)[X] := X ^ 8 + X ^ 4 + X ^ 3 + X + 1
theorem Q8a_monic : Q8a.Monic := by unfold Q8a; monicity!
theorem Q8a_degree : Q8a.degree = 8 := by unfold Q8a; compute_degree!
theorem Q8a_natDegree : Q8a.natDegree = 8 := by
  have := Q8a_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8a; exact Q8a_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8a) :=
  AdjoinRoot.nontrivial Q8a (by rw [Q8a_degree]; decide)
instance : CharP (AdjoinRoot Q8a) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8a)).injective) 2
/-- Root relation: `r^8 = r ^ 4 + r ^ 3 + r + 1`. -/
theorem root_Q8a : (AdjoinRoot.root Q8a) ^ 8 = AdjoinRoot.root Q8a ^ 4 + AdjoinRoot.root Q8a ^ 3 + AdjoinRoot.root Q8a + 1 := by
  have h0 : (AdjoinRoot.mk Q8a) Q8a = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8a) Q8a = (AdjoinRoot.root Q8a) ^ 8 + (AdjoinRoot.root Q8a) ^ 4 + (AdjoinRoot.root Q8a) ^ 3 + AdjoinRoot.root Q8a + 1 := by
    unfold Q8a; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8a) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8a ^ 4 + AdjoinRoot.root Q8a ^ 3 + AdjoinRoot.root Q8a + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 4 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_a : ¬ Q8a ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8a with hr
  have hmkP : AdjoinRoot.mk Q8a POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + r + 1 := root_Q8a
  have h2 : (2 : AdjoinRoot Q8a) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 4) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 4 + r) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 4) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q8a (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8a_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #2: `X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8b : (ZMod 2)[X] := X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q8b_monic : Q8b.Monic := by unfold Q8b; monicity!
theorem Q8b_degree : Q8b.degree = 8 := by unfold Q8b; compute_degree!
theorem Q8b_natDegree : Q8b.natDegree = 8 := by
  have := Q8b_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8b; exact Q8b_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8b) :=
  AdjoinRoot.nontrivial Q8b (by rw [Q8b_degree]; decide)
instance : CharP (AdjoinRoot Q8b) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8b)).injective) 2
/-- Root relation: `r^8 = r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8b : (AdjoinRoot.root Q8b) ^ 8 = AdjoinRoot.root Q8b ^ 4 + AdjoinRoot.root Q8b ^ 3 + AdjoinRoot.root Q8b ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8b) Q8b = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8b) Q8b = (AdjoinRoot.root Q8b) ^ 8 + (AdjoinRoot.root Q8b) ^ 4 + (AdjoinRoot.root Q8b) ^ 3 + (AdjoinRoot.root Q8b) ^ 2 + 1 := by
    unfold Q8b; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8b) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8b ^ 4 + AdjoinRoot.root Q8b ^ 3 + AdjoinRoot.root Q8b ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_b : ¬ Q8b ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8b with hr
  have hmkP : AdjoinRoot.mk Q8b POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q8b
  have h2 : (2 : AdjoinRoot Q8b) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h11 + h8 + (r ^ 4) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 4 + r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 4 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 3 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 5 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 3 + r ^ 2 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 3 + r := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r ^ 2 + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 3 + r = AdjoinRoot.mk Q8b (X ^ 7 + X ^ 3 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 3 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8b_degree]
    have hd : (X ^ 7 + X ^ 3 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #3: `X ^ 8 + X ^ 5 + X ^ 3 + X + 1`. -/
noncomputable def Q8c : (ZMod 2)[X] := X ^ 8 + X ^ 5 + X ^ 3 + X + 1
theorem Q8c_monic : Q8c.Monic := by unfold Q8c; monicity!
theorem Q8c_degree : Q8c.degree = 8 := by unfold Q8c; compute_degree!
theorem Q8c_natDegree : Q8c.natDegree = 8 := by
  have := Q8c_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8c; exact Q8c_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8c) :=
  AdjoinRoot.nontrivial Q8c (by rw [Q8c_degree]; decide)
instance : CharP (AdjoinRoot Q8c) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8c)).injective) 2
/-- Root relation: `r^8 = r ^ 5 + r ^ 3 + r + 1`. -/
theorem root_Q8c : (AdjoinRoot.root Q8c) ^ 8 = AdjoinRoot.root Q8c ^ 5 + AdjoinRoot.root Q8c ^ 3 + AdjoinRoot.root Q8c + 1 := by
  have h0 : (AdjoinRoot.mk Q8c) Q8c = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8c) Q8c = (AdjoinRoot.root Q8c) ^ 8 + (AdjoinRoot.root Q8c) ^ 5 + (AdjoinRoot.root Q8c) ^ 3 + AdjoinRoot.root Q8c + 1 := by
    unfold Q8c; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8c) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8c ^ 5 + AdjoinRoot.root Q8c ^ 3 + AdjoinRoot.root Q8c + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 5 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_c : ¬ Q8c ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8c with hr
  have hmkP : AdjoinRoot.mk Q8c POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 5 + r ^ 3 + r + 1 := root_Q8c
  have h2 : (2 : AdjoinRoot Q8c) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 4 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + 1 := by linear_combination r * h13 + h8 + (r ^ 3 + r) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + 1 := by linear_combination r * h14 + h8 + (r ^ 3 + r) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h15 + h8 + (r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 2 = AdjoinRoot.mk Q8c (X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 2 : (ZMod 2)[X]).degree = 2 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8c_degree]
    have hd : (X ^ 2 : (ZMod 2)[X]).degree ≤ 2 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #4: `X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8d : (ZMod 2)[X] := X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1
theorem Q8d_monic : Q8d.Monic := by unfold Q8d; monicity!
theorem Q8d_degree : Q8d.degree = 8 := by unfold Q8d; compute_degree!
theorem Q8d_natDegree : Q8d.natDegree = 8 := by
  have := Q8d_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8d; exact Q8d_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8d) :=
  AdjoinRoot.nontrivial Q8d (by rw [Q8d_degree]; decide)
instance : CharP (AdjoinRoot Q8d) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8d)).injective) 2
/-- Root relation: `r^8 = r ^ 5 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8d : (AdjoinRoot.root Q8d) ^ 8 = AdjoinRoot.root Q8d ^ 5 + AdjoinRoot.root Q8d ^ 3 + AdjoinRoot.root Q8d ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8d) Q8d = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8d) Q8d = (AdjoinRoot.root Q8d) ^ 8 + (AdjoinRoot.root Q8d) ^ 5 + (AdjoinRoot.root Q8d) ^ 3 + (AdjoinRoot.root Q8d) ^ 2 + 1 := by
    unfold Q8d; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8d) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8d ^ 5 + AdjoinRoot.root Q8d ^ 3 + AdjoinRoot.root Q8d ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_d : ¬ Q8d ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8d with hr
  have hmkP : AdjoinRoot.mk Q8d POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 5 + r ^ 3 + r ^ 2 + 1 := root_Q8d
  have h2 : (2 : AdjoinRoot Q8d) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 4 + r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 2 + 1 := by linear_combination r * h10 + h8 + (r ^ 5 + r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 3 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h12 + h8 + (r ^ 2) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + 1 := by linear_combination r * h15 + h8 + (r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 2 = AdjoinRoot.mk Q8d (X ^ 6 + X ^ 5 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 2 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8d_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 2 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #5: `X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1`. -/
noncomputable def Q8e : (ZMod 2)[X] := X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1
theorem Q8e_monic : Q8e.Monic := by unfold Q8e; monicity!
theorem Q8e_degree : Q8e.degree = 8 := by unfold Q8e; compute_degree!
theorem Q8e_natDegree : Q8e.natDegree = 8 := by
  have := Q8e_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8e; exact Q8e_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8e) :=
  AdjoinRoot.nontrivial Q8e (by rw [Q8e_degree]; decide)
instance : CharP (AdjoinRoot Q8e) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8e)).injective) 2
/-- Root relation: `r^8 = r ^ 5 + r ^ 4 + r ^ 3 + 1`. -/
theorem root_Q8e : (AdjoinRoot.root Q8e) ^ 8 = AdjoinRoot.root Q8e ^ 5 + AdjoinRoot.root Q8e ^ 4 + AdjoinRoot.root Q8e ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q8e) Q8e = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8e) Q8e = (AdjoinRoot.root Q8e) ^ 8 + (AdjoinRoot.root Q8e) ^ 5 + (AdjoinRoot.root Q8e) ^ 4 + (AdjoinRoot.root Q8e) ^ 3 + 1 := by
    unfold Q8e; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8e) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8e ^ 5 + AdjoinRoot.root Q8e ^ 4 + AdjoinRoot.root Q8e ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg8_factor_e : ¬ Q8e ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8e with hr
  have hmkP : AdjoinRoot.mk Q8e POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 3 + 1 := root_Q8e
  have h2 : (2 : AdjoinRoot Q8e) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h10 + h8 + (r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 5) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 5 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 4 + r ^ 3) * h2
  have h15 : r ^ 15 = r ^ 6 + r ^ 3 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q8e (X ^ 6 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8e_degree]
    have hd : (X ^ 6 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #6: `X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q8f : (ZMod 2)[X] := X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
theorem Q8f_monic : Q8f.Monic := by unfold Q8f; monicity!
theorem Q8f_degree : Q8f.degree = 8 := by unfold Q8f; compute_degree!
theorem Q8f_natDegree : Q8f.natDegree = 8 := by
  have := Q8f_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8f; exact Q8f_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8f) :=
  AdjoinRoot.nontrivial Q8f (by rw [Q8f_degree]; decide)
instance : CharP (AdjoinRoot Q8f) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8f)).injective) 2
/-- Root relation: `r^8 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q8f : (AdjoinRoot.root Q8f) ^ 8 = AdjoinRoot.root Q8f ^ 5 + AdjoinRoot.root Q8f ^ 4 + AdjoinRoot.root Q8f ^ 3 + AdjoinRoot.root Q8f ^ 2 + AdjoinRoot.root Q8f + 1 := by
  have h0 : (AdjoinRoot.mk Q8f) Q8f = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8f) Q8f = (AdjoinRoot.root Q8f) ^ 8 + (AdjoinRoot.root Q8f) ^ 5 + (AdjoinRoot.root Q8f) ^ 4 + (AdjoinRoot.root Q8f) ^ 3 + (AdjoinRoot.root Q8f) ^ 2 + AdjoinRoot.root Q8f + 1 := by
    unfold Q8f; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8f) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8f ^ 5 + AdjoinRoot.root Q8f ^ 4 + AdjoinRoot.root Q8f ^ 3 + AdjoinRoot.root Q8f ^ 2 + AdjoinRoot.root Q8f + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_f : ¬ Q8f ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8f with hr
  have hmkP : AdjoinRoot.mk Q8f POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := root_Q8f
  have h2 : (2 : AdjoinRoot Q8f) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 2 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 5 + r ^ 4 + r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h11 + h8 + (r ^ 3 + r ^ 2 + r) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 5 + r) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 5 + r ^ 4 + r ^ 2) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 4 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 4 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q8f (X ^ 5 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8f_degree]
    have hd : (X ^ 5 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #7: `X ^ 8 + X ^ 6 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8g : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 3 + X ^ 2 + 1
theorem Q8g_monic : Q8g.Monic := by unfold Q8g; monicity!
theorem Q8g_degree : Q8g.degree = 8 := by unfold Q8g; compute_degree!
theorem Q8g_natDegree : Q8g.natDegree = 8 := by
  have := Q8g_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8g; exact Q8g_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8g) :=
  AdjoinRoot.nontrivial Q8g (by rw [Q8g_degree]; decide)
instance : CharP (AdjoinRoot Q8g) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8g)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8g : (AdjoinRoot.root Q8g) ^ 8 = AdjoinRoot.root Q8g ^ 6 + AdjoinRoot.root Q8g ^ 3 + AdjoinRoot.root Q8g ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8g) Q8g = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8g) Q8g = (AdjoinRoot.root Q8g) ^ 8 + (AdjoinRoot.root Q8g) ^ 6 + (AdjoinRoot.root Q8g) ^ 3 + (AdjoinRoot.root Q8g) ^ 2 + 1 := by
    unfold Q8g; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8g) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8g ^ 6 + AdjoinRoot.root Q8g ^ 3 + AdjoinRoot.root Q8g ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_g : ¬ Q8g ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8g with hr
  have hmkP : AdjoinRoot.mk Q8g POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 3 + r ^ 2 + 1 := root_Q8g
  have h2 : (2 : AdjoinRoot Q8g) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 4 + r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h9 + h8 + (r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h11 + h8 + (r ^ 6 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 6) * h2
  have h14 : r ^ 14 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 4 + r ^ 3 + r := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 5 + r ^ 3 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 4 + r ^ 3 + r = AdjoinRoot.mk Q8g (X ^ 6 + X ^ 4 + X ^ 3 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 4 + X ^ 3 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8g_degree]
    have hd : (X ^ 6 + X ^ 4 + X ^ 3 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #8: `X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q8h : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
theorem Q8h_monic : Q8h.Monic := by unfold Q8h; monicity!
theorem Q8h_degree : Q8h.degree = 8 := by unfold Q8h; compute_degree!
theorem Q8h_natDegree : Q8h.natDegree = 8 := by
  have := Q8h_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8h; exact Q8h_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8h) :=
  AdjoinRoot.nontrivial Q8h (by rw [Q8h_degree]; decide)
instance : CharP (AdjoinRoot Q8h) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8h)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q8h : (AdjoinRoot.root Q8h) ^ 8 = AdjoinRoot.root Q8h ^ 6 + AdjoinRoot.root Q8h ^ 4 + AdjoinRoot.root Q8h ^ 3 + AdjoinRoot.root Q8h ^ 2 + AdjoinRoot.root Q8h + 1 := by
  have h0 : (AdjoinRoot.mk Q8h) Q8h = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8h) Q8h = (AdjoinRoot.root Q8h) ^ 8 + (AdjoinRoot.root Q8h) ^ 6 + (AdjoinRoot.root Q8h) ^ 4 + (AdjoinRoot.root Q8h) ^ 3 + (AdjoinRoot.root Q8h) ^ 2 + AdjoinRoot.root Q8h + 1 := by
    unfold Q8h; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8h) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8h ^ 6 + AdjoinRoot.root Q8h ^ 4 + AdjoinRoot.root Q8h ^ 3 + AdjoinRoot.root Q8h ^ 2 + AdjoinRoot.root Q8h + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_h : ¬ Q8h ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8h with hr
  have hmkP : AdjoinRoot.mk Q8h POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := root_Q8h
  have h2 : (2 : AdjoinRoot Q8h) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 5 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 3 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 4 + r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 6 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 4 + r ^ 3 + r ^ 2) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = 1 := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 3 + r ^ 2 + r) * h2
  rw [hval]
  -- residue is the constant `1`, nonzero in the nontrivial ring `AdjoinRoot Q8h`.
  exact one_ne_zero

/-- Monic irreducible degree-8 #9: `X ^ 8 + X ^ 6 + X ^ 5 + X + 1`. -/
noncomputable def Q8i : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X + 1
theorem Q8i_monic : Q8i.Monic := by unfold Q8i; monicity!
theorem Q8i_degree : Q8i.degree = 8 := by unfold Q8i; compute_degree!
theorem Q8i_natDegree : Q8i.natDegree = 8 := by
  have := Q8i_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8i; exact Q8i_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8i) :=
  AdjoinRoot.nontrivial Q8i (by rw [Q8i_degree]; decide)
instance : CharP (AdjoinRoot Q8i) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8i)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r + 1`. -/
theorem root_Q8i : (AdjoinRoot.root Q8i) ^ 8 = AdjoinRoot.root Q8i ^ 6 + AdjoinRoot.root Q8i ^ 5 + AdjoinRoot.root Q8i + 1 := by
  have h0 : (AdjoinRoot.mk Q8i) Q8i = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8i) Q8i = (AdjoinRoot.root Q8i) ^ 8 + (AdjoinRoot.root Q8i) ^ 6 + (AdjoinRoot.root Q8i) ^ 5 + AdjoinRoot.root Q8i + 1 := by
    unfold Q8i; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8i) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8i ^ 6 + AdjoinRoot.root Q8i ^ 5 + AdjoinRoot.root Q8i + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_i : ¬ Q8i ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8i with hr
  have hmkP : AdjoinRoot.mk Q8i POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r + 1 := root_Q8i
  have h2 : (2 : AdjoinRoot Q8i) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h9 + h8
  have h11 : r ^ 11 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h10 + h8 + (r ^ 6 + r) * h2
  have h12 : r ^ 12 = r ^ 4 + r ^ 3 + 1 := by linear_combination r * h11 + h8 + (r ^ 6 + r ^ 5 + r) * h2
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 3 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h15 + h8
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 5 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 5 + 1 = AdjoinRoot.mk Q8i (X ^ 7 + X ^ 6 + X ^ 5 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 5 + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8i_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 5 + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #10: `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 2 + 1`. -/
noncomputable def Q8j : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X ^ 2 + 1
theorem Q8j_monic : Q8j.Monic := by unfold Q8j; monicity!
theorem Q8j_degree : Q8j.degree = 8 := by unfold Q8j; compute_degree!
theorem Q8j_natDegree : Q8j.natDegree = 8 := by
  have := Q8j_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8j; exact Q8j_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8j) :=
  AdjoinRoot.nontrivial Q8j (by rw [Q8j_degree]; decide)
instance : CharP (AdjoinRoot Q8j) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8j)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r ^ 2 + 1`. -/
theorem root_Q8j : (AdjoinRoot.root Q8j) ^ 8 = AdjoinRoot.root Q8j ^ 6 + AdjoinRoot.root Q8j ^ 5 + AdjoinRoot.root Q8j ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8j) Q8j = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8j) Q8j = (AdjoinRoot.root Q8j) ^ 8 + (AdjoinRoot.root Q8j) ^ 6 + (AdjoinRoot.root Q8j) ^ 5 + (AdjoinRoot.root Q8j) ^ 2 + 1 := by
    unfold Q8j; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8j) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8j ^ 6 + AdjoinRoot.root Q8j ^ 5 + AdjoinRoot.root Q8j ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_j : ¬ Q8j ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8j with hr
  have hmkP : AdjoinRoot.mk Q8j POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 2 + 1 := root_Q8j
  have h2 : (2 : AdjoinRoot Q8j) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 3 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h9 + h8 + (r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 2 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 6 + r ^ 5) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 3 + 1 := by linear_combination r * h13 + h8 + (r ^ 5 + r ^ 2) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h14 + h8
  have h16 : r ^ 16 = r ^ 7 + r ^ 3 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 6 + r ^ 5 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r + 1 = AdjoinRoot.mk Q8j (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8j_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #11: `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 3 + 1`. -/
noncomputable def Q8k : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X ^ 3 + 1
theorem Q8k_monic : Q8k.Monic := by unfold Q8k; monicity!
theorem Q8k_degree : Q8k.degree = 8 := by unfold Q8k; compute_degree!
theorem Q8k_natDegree : Q8k.natDegree = 8 := by
  have := Q8k_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8k; exact Q8k_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8k) :=
  AdjoinRoot.nontrivial Q8k (by rw [Q8k_degree]; decide)
instance : CharP (AdjoinRoot Q8k) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8k)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r ^ 3 + 1`. -/
theorem root_Q8k : (AdjoinRoot.root Q8k) ^ 8 = AdjoinRoot.root Q8k ^ 6 + AdjoinRoot.root Q8k ^ 5 + AdjoinRoot.root Q8k ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q8k) Q8k = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8k) Q8k = (AdjoinRoot.root Q8k) ^ 8 + (AdjoinRoot.root Q8k) ^ 6 + (AdjoinRoot.root Q8k) ^ 5 + (AdjoinRoot.root Q8k) ^ 3 + 1 := by
    unfold Q8k; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8k) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8k ^ 6 + AdjoinRoot.root Q8k ^ 5 + AdjoinRoot.root Q8k ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg8_factor_k : ¬ Q8k ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8k with hr
  have hmkP : AdjoinRoot.mk Q8k POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 3 + 1 := root_Q8k
  have h2 : (2 : AdjoinRoot Q8k) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 4 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h9 + h8 + (r ^ 5) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 3) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 6 + r ^ 5) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h14 + h8 + (r ^ 6 + r ^ 3) * h2
  have h16 : r ^ 16 = r + 1 := by linear_combination r * h15 + h8 + (r ^ 6 + r ^ 5 + r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 2 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 2 + r + 1 = AdjoinRoot.mk Q8k (X ^ 7 + X ^ 2 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8k_degree]
    have hd : (X ^ 7 + X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #12: `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + 1`. -/
noncomputable def Q8l : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + 1
theorem Q8l_monic : Q8l.Monic := by unfold Q8l; monicity!
theorem Q8l_degree : Q8l.degree = 8 := by unfold Q8l; compute_degree!
theorem Q8l_natDegree : Q8l.natDegree = 8 := by
  have := Q8l_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8l; exact Q8l_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8l) :=
  AdjoinRoot.nontrivial Q8l (by rw [Q8l_degree]; decide)
instance : CharP (AdjoinRoot Q8l) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8l)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r ^ 4 + 1`. -/
theorem root_Q8l : (AdjoinRoot.root Q8l) ^ 8 = AdjoinRoot.root Q8l ^ 6 + AdjoinRoot.root Q8l ^ 5 + AdjoinRoot.root Q8l ^ 4 + 1 := by
  have h0 : (AdjoinRoot.mk Q8l) Q8l = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8l) Q8l = (AdjoinRoot.root Q8l) ^ 8 + (AdjoinRoot.root Q8l) ^ 6 + (AdjoinRoot.root Q8l) ^ 5 + (AdjoinRoot.root Q8l) ^ 4 + 1 := by
    unfold Q8l; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8l) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8l ^ 6 + AdjoinRoot.root Q8l ^ 5 + AdjoinRoot.root Q8l ^ 4 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + 1`.** -/
theorem POLY_poly_no_deg8_factor_l : ¬ Q8l ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8l with hr
  have hmkP : AdjoinRoot.mk Q8l POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + 1 := root_Q8l
  have h2 : (2 : AdjoinRoot Q8l) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 5 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h9 + h8 + (r ^ 6) * h2
  have h11 : r ^ 11 = r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 6 + r ^ 5) * h2
  have h12 : r ^ 12 = r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + 1 := by linear_combination r * h14 + h8 + (r ^ 5 + r ^ 4) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h15 + h8
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 5 + r ^ 4 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + r = AdjoinRoot.mk Q8l (X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8l_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #13: `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1`. -/
noncomputable def Q8m : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1
theorem Q8m_monic : Q8m.Monic := by unfold Q8m; monicity!
theorem Q8m_degree : Q8m.degree = 8 := by unfold Q8m; compute_degree!
theorem Q8m_natDegree : Q8m.natDegree = 8 := by
  have := Q8m_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8m; exact Q8m_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8m) :=
  AdjoinRoot.nontrivial Q8m (by rw [Q8m_degree]; decide)
instance : CharP (AdjoinRoot Q8m) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8m)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1`. -/
theorem root_Q8m : (AdjoinRoot.root Q8m) ^ 8 = AdjoinRoot.root Q8m ^ 6 + AdjoinRoot.root Q8m ^ 5 + AdjoinRoot.root Q8m ^ 4 + AdjoinRoot.root Q8m ^ 2 + AdjoinRoot.root Q8m + 1 := by
  have h0 : (AdjoinRoot.mk Q8m) Q8m = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8m) Q8m = (AdjoinRoot.root Q8m) ^ 8 + (AdjoinRoot.root Q8m) ^ 6 + (AdjoinRoot.root Q8m) ^ 5 + (AdjoinRoot.root Q8m) ^ 4 + (AdjoinRoot.root Q8m) ^ 2 + AdjoinRoot.root Q8m + 1 := by
    unfold Q8m; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8m) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8m ^ 6 + AdjoinRoot.root Q8m ^ 5 + AdjoinRoot.root Q8m ^ 4 + AdjoinRoot.root Q8m ^ 2 + AdjoinRoot.root Q8m + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_m : ¬ Q8m ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8m with hr
  have hmkP : AdjoinRoot.mk Q8m POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := root_Q8m
  have h2 : (2 : AdjoinRoot Q8m) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 6 + r ^ 4 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 5 + 1 := by linear_combination r * h10 + h8 + (r ^ 6 + r ^ 4 + r ^ 2 + r) * h2
  have h12 : r ^ 12 = r ^ 6 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 3 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r = AdjoinRoot.mk Q8m (X ^ 7 + X ^ 6 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8m_degree]
    have hd : (X ^ 7 + X ^ 6 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #14: `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1`. -/
noncomputable def Q8n : (ZMod 2)[X] := X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1
theorem Q8n_monic : Q8n.Monic := by unfold Q8n; monicity!
theorem Q8n_degree : Q8n.degree = 8 := by unfold Q8n; compute_degree!
theorem Q8n_natDegree : Q8n.natDegree = 8 := by
  have := Q8n_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8n; exact Q8n_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8n) :=
  AdjoinRoot.nontrivial Q8n (by rw [Q8n_degree]; decide)
instance : CharP (AdjoinRoot Q8n) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8n)).injective) 2
/-- Root relation: `r^8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r + 1`. -/
theorem root_Q8n : (AdjoinRoot.root Q8n) ^ 8 = AdjoinRoot.root Q8n ^ 6 + AdjoinRoot.root Q8n ^ 5 + AdjoinRoot.root Q8n ^ 4 + AdjoinRoot.root Q8n ^ 3 + AdjoinRoot.root Q8n + 1 := by
  have h0 : (AdjoinRoot.mk Q8n) Q8n = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8n) Q8n = (AdjoinRoot.root Q8n) ^ 8 + (AdjoinRoot.root Q8n) ^ 6 + (AdjoinRoot.root Q8n) ^ 5 + (AdjoinRoot.root Q8n) ^ 4 + (AdjoinRoot.root Q8n) ^ 3 + AdjoinRoot.root Q8n + 1 := by
    unfold Q8n; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8n) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8n ^ 6 + AdjoinRoot.root Q8n ^ 5 + AdjoinRoot.root Q8n ^ 4 + AdjoinRoot.root Q8n ^ 3 + AdjoinRoot.root Q8n + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_n : ¬ Q8n ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8n with hr
  have hmkP : AdjoinRoot.mk Q8n POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := root_Q8n
  have h2 : (2 : AdjoinRoot Q8n) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h8
  have h10 : r ^ 10 = r ^ 7 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 6 + r ^ 5 + r ^ 3) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h10 + h8 + (r ^ 5 + r ^ 3 + r) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 3 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 6 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r + 1 := by linear_combination r * h15 + h8 + (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 5 + r := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 5 + r = AdjoinRoot.mk Q8n (X ^ 7 + X ^ 5 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 5 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8n_degree]
    have hd : (X ^ 7 + X ^ 5 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #15: `X ^ 8 + X ^ 7 + X ^ 2 + X + 1`. -/
noncomputable def Q8o : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 2 + X + 1
theorem Q8o_monic : Q8o.Monic := by unfold Q8o; monicity!
theorem Q8o_degree : Q8o.degree = 8 := by unfold Q8o; compute_degree!
theorem Q8o_natDegree : Q8o.natDegree = 8 := by
  have := Q8o_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8o; exact Q8o_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8o) :=
  AdjoinRoot.nontrivial Q8o (by rw [Q8o_degree]; decide)
instance : CharP (AdjoinRoot Q8o) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8o)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 2 + r + 1`. -/
theorem root_Q8o : (AdjoinRoot.root Q8o) ^ 8 = AdjoinRoot.root Q8o ^ 7 + AdjoinRoot.root Q8o ^ 2 + AdjoinRoot.root Q8o + 1 := by
  have h0 : (AdjoinRoot.mk Q8o) Q8o = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8o) Q8o = (AdjoinRoot.root Q8o) ^ 8 + (AdjoinRoot.root Q8o) ^ 7 + (AdjoinRoot.root Q8o) ^ 2 + AdjoinRoot.root Q8o + 1 := by
    unfold Q8o; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8o) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8o ^ 7 + AdjoinRoot.root Q8o ^ 2 + AdjoinRoot.root Q8o + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_o : ¬ Q8o ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8o with hr
  have hmkP : AdjoinRoot.mk Q8o POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 2 + r + 1 := root_Q8o
  have h2 : (2 : AdjoinRoot Q8o) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 3 + 1 := by linear_combination r * h8 + h8 + (r ^ 2 + r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h9 + h8 + (r) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 5 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h10 + h8 + (r) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h11 + h8 + (r) * h2
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 7 + r) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 7) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r ^ 2 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + 1 = AdjoinRoot.mk Q8o (X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8o_degree]
    have hd : (X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #16: `X ^ 8 + X ^ 7 + X ^ 3 + X + 1`. -/
noncomputable def Q8p : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 3 + X + 1
theorem Q8p_monic : Q8p.Monic := by unfold Q8p; monicity!
theorem Q8p_degree : Q8p.degree = 8 := by unfold Q8p; compute_degree!
theorem Q8p_natDegree : Q8p.natDegree = 8 := by
  have := Q8p_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8p; exact Q8p_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8p) :=
  AdjoinRoot.nontrivial Q8p (by rw [Q8p_degree]; decide)
instance : CharP (AdjoinRoot Q8p) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8p)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 3 + r + 1`. -/
theorem root_Q8p : (AdjoinRoot.root Q8p) ^ 8 = AdjoinRoot.root Q8p ^ 7 + AdjoinRoot.root Q8p ^ 3 + AdjoinRoot.root Q8p + 1 := by
  have h0 : (AdjoinRoot.mk Q8p) Q8p = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8p) Q8p = (AdjoinRoot.root Q8p) ^ 8 + (AdjoinRoot.root Q8p) ^ 7 + (AdjoinRoot.root Q8p) ^ 3 + AdjoinRoot.root Q8p + 1 := by
    unfold Q8p; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8p) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8p ^ 7 + AdjoinRoot.root Q8p ^ 3 + AdjoinRoot.root Q8p + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 3 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_p : ¬ Q8p ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8p with hr
  have hmkP : AdjoinRoot.mk Q8p POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 3 + r + 1 := root_Q8p
  have h2 : (2 : AdjoinRoot Q8p) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h8 + h8 + (r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h9 + h8 + (r ^ 3 + r) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h10 + h8 + (r) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h11 + h8 + (r ^ 7 + r) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 5 + r ^ 4 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8
  have h15 : r ^ 15 = r ^ 6 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h14 + h8 + (r ^ 7 + r ^ 3 + r) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 5 + r ^ 3 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 = AdjoinRoot.mk Q8p (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8p_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #17: `X ^ 8 + X ^ 7 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8q : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 3 + X ^ 2 + 1
theorem Q8q_monic : Q8q.Monic := by unfold Q8q; monicity!
theorem Q8q_degree : Q8q.degree = 8 := by unfold Q8q; compute_degree!
theorem Q8q_natDegree : Q8q.natDegree = 8 := by
  have := Q8q_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8q; exact Q8q_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8q) :=
  AdjoinRoot.nontrivial Q8q (by rw [Q8q_degree]; decide)
instance : CharP (AdjoinRoot Q8q) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8q)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8q : (AdjoinRoot.root Q8q) ^ 8 = AdjoinRoot.root Q8q ^ 7 + AdjoinRoot.root Q8q ^ 3 + AdjoinRoot.root Q8q ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8q) Q8q = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8q) Q8q = (AdjoinRoot.root Q8q) ^ 8 + (AdjoinRoot.root Q8q) ^ 7 + (AdjoinRoot.root Q8q) ^ 3 + (AdjoinRoot.root Q8q) ^ 2 + 1 := by
    unfold Q8q; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8q) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8q ^ 7 + AdjoinRoot.root Q8q ^ 3 + AdjoinRoot.root Q8q ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_q : ¬ Q8q ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8q with hr
  have hmkP : AdjoinRoot.mk Q8q POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 3 + r ^ 2 + 1 := root_Q8q
  have h2 : (2 : AdjoinRoot Q8q) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 3) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 3 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 7 + r ^ 2) * h2
  have h13 : r ^ 13 = r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h8 + (r ^ 7) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 3 + r ^ 2 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 3 + r ^ 2 + 1 = AdjoinRoot.mk Q8q (X ^ 5 + X ^ 3 + X ^ 2 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8q_degree]
    have hd : (X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #18: `X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q8r : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
theorem Q8r_monic : Q8r.Monic := by unfold Q8r; monicity!
theorem Q8r_degree : Q8r.degree = 8 := by unfold Q8r; compute_degree!
theorem Q8r_natDegree : Q8r.natDegree = 8 := by
  have := Q8r_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8r; exact Q8r_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8r) :=
  AdjoinRoot.nontrivial Q8r (by rw [Q8r_degree]; decide)
instance : CharP (AdjoinRoot Q8r) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8r)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q8r : (AdjoinRoot.root Q8r) ^ 8 = AdjoinRoot.root Q8r ^ 7 + AdjoinRoot.root Q8r ^ 4 + AdjoinRoot.root Q8r ^ 3 + AdjoinRoot.root Q8r ^ 2 + AdjoinRoot.root Q8r + 1 := by
  have h0 : (AdjoinRoot.mk Q8r) Q8r = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8r) Q8r = (AdjoinRoot.root Q8r) ^ 8 + (AdjoinRoot.root Q8r) ^ 7 + (AdjoinRoot.root Q8r) ^ 4 + (AdjoinRoot.root Q8r) ^ 3 + (AdjoinRoot.root Q8r) ^ 2 + AdjoinRoot.root Q8r + 1 := by
    unfold Q8r; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8r) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8r ^ 7 + AdjoinRoot.root Q8r ^ 4 + AdjoinRoot.root Q8r ^ 3 + AdjoinRoot.root Q8r ^ 2 + AdjoinRoot.root Q8r + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_r : ¬ Q8r ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8r with hr
  have hmkP : AdjoinRoot.mk Q8r POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := root_Q8r
  have h2 : (2 : AdjoinRoot Q8r) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 5 + 1 := by linear_combination r * h8 + h8 + (r ^ 4 + r ^ 3 + r ^ 2 + r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h9 + h8 + (r) * h2
  have h11 : r ^ 11 = r ^ 5 + r ^ 2 + 1 := by linear_combination r * h10 + h8 + (r ^ 7 + r ^ 4 + r ^ 3 + r) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 3 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 4 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 3) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + 1 := by linear_combination r * h14 + h8 + (r ^ 3 + r ^ 2 + r) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h8 + (r ^ 7 + r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q8r (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8r_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #19: `X ^ 8 + X ^ 7 + X ^ 5 + X + 1`. -/
noncomputable def Q8s : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 5 + X + 1
theorem Q8s_monic : Q8s.Monic := by unfold Q8s; monicity!
theorem Q8s_degree : Q8s.degree = 8 := by unfold Q8s; compute_degree!
theorem Q8s_natDegree : Q8s.natDegree = 8 := by
  have := Q8s_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8s; exact Q8s_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8s) :=
  AdjoinRoot.nontrivial Q8s (by rw [Q8s_degree]; decide)
instance : CharP (AdjoinRoot Q8s) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8s)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 5 + r + 1`. -/
theorem root_Q8s : (AdjoinRoot.root Q8s) ^ 8 = AdjoinRoot.root Q8s ^ 7 + AdjoinRoot.root Q8s ^ 5 + AdjoinRoot.root Q8s + 1 := by
  have h0 : (AdjoinRoot.mk Q8s) Q8s = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8s) Q8s = (AdjoinRoot.root Q8s) ^ 8 + (AdjoinRoot.root Q8s) ^ 7 + (AdjoinRoot.root Q8s) ^ 5 + AdjoinRoot.root Q8s + 1 := by
    unfold Q8s; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8s) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8s ^ 7 + AdjoinRoot.root Q8s ^ 5 + AdjoinRoot.root Q8s + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 5 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_s : ¬ Q8s ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8s with hr
  have hmkP : AdjoinRoot.mk Q8s POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 5 + r + 1 := root_Q8s
  have h2 : (2 : AdjoinRoot Q8s) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + 1 := by linear_combination r * h8 + h8 + (r) * h2
  have h10 : r ^ 10 = r ^ 6 + r ^ 5 + r ^ 3 + 1 := by linear_combination r * h9 + h8 + (r ^ 7 + r) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 4 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 2 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 7 + r ^ 5) * h2
  have h13 : r ^ 13 = r ^ 3 + r ^ 2 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q8s (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8s_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #20: `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 3 + 1`. -/
noncomputable def Q8t : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 5 + X ^ 3 + 1
theorem Q8t_monic : Q8t.Monic := by unfold Q8t; monicity!
theorem Q8t_degree : Q8t.degree = 8 := by unfold Q8t; compute_degree!
theorem Q8t_natDegree : Q8t.natDegree = 8 := by
  have := Q8t_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8t; exact Q8t_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8t) :=
  AdjoinRoot.nontrivial Q8t (by rw [Q8t_degree]; decide)
instance : CharP (AdjoinRoot Q8t) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8t)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 5 + r ^ 3 + 1`. -/
theorem root_Q8t : (AdjoinRoot.root Q8t) ^ 8 = AdjoinRoot.root Q8t ^ 7 + AdjoinRoot.root Q8t ^ 5 + AdjoinRoot.root Q8t ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q8t) Q8t = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8t) Q8t = (AdjoinRoot.root Q8t) ^ 8 + (AdjoinRoot.root Q8t) ^ 7 + (AdjoinRoot.root Q8t) ^ 5 + (AdjoinRoot.root Q8t) ^ 3 + 1 := by
    unfold Q8t; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8t) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8t ^ 7 + AdjoinRoot.root Q8t ^ 5 + AdjoinRoot.root Q8t ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg8_factor_t : ¬ Q8t ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8t with hr
  have hmkP : AdjoinRoot.mk Q8t POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 5 + r ^ 3 + 1 := root_Q8t
  have h2 : (2 : AdjoinRoot Q8t) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h8 + h8
  have h10 : r ^ 10 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 7 + r ^ 5) * h2
  have h11 : r ^ 11 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h11 + h8 + (r ^ 5 + r ^ 3) * h2
  have h13 : r ^ 13 = r + 1 := by linear_combination r * h12 + h8 + (r ^ 7 + r ^ 5 + r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 2 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 3 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 4 + r ^ 3 + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 2 + r = AdjoinRoot.mk Q8t (X ^ 7 + X ^ 6 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 2 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8t_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #21: `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + 1`. -/
noncomputable def Q8u : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + 1
theorem Q8u_monic : Q8u.Monic := by unfold Q8u; monicity!
theorem Q8u_degree : Q8u.degree = 8 := by unfold Q8u; compute_degree!
theorem Q8u_natDegree : Q8u.natDegree = 8 := by
  have := Q8u_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8u; exact Q8u_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8u) :=
  AdjoinRoot.nontrivial Q8u (by rw [Q8u_degree]; decide)
instance : CharP (AdjoinRoot Q8u) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8u)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 5 + r ^ 4 + 1`. -/
theorem root_Q8u : (AdjoinRoot.root Q8u) ^ 8 = AdjoinRoot.root Q8u ^ 7 + AdjoinRoot.root Q8u ^ 5 + AdjoinRoot.root Q8u ^ 4 + 1 := by
  have h0 : (AdjoinRoot.mk Q8u) Q8u = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8u) Q8u = (AdjoinRoot.root Q8u) ^ 8 + (AdjoinRoot.root Q8u) ^ 7 + (AdjoinRoot.root Q8u) ^ 5 + (AdjoinRoot.root Q8u) ^ 4 + 1 := by
    unfold Q8u; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8u) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8u ^ 7 + AdjoinRoot.root Q8u ^ 5 + AdjoinRoot.root Q8u ^ 4 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + 1`.** -/
theorem POLY_poly_no_deg8_factor_u : ¬ Q8u ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8u with hr
  have hmkP : AdjoinRoot.mk Q8u POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 5 + r ^ 4 + 1 := root_Q8u
  have h2 : (2 : AdjoinRoot Q8u) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 4 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 5) * h2
  have h10 : r ^ 10 = r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 7 + r ^ 5) * h2
  have h11 : r ^ 11 = r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + 1 := by linear_combination r * h13 + h8 + (r ^ 5 + r ^ 4) * h2
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 7) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r ^ 2 + r) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + 1 = AdjoinRoot.mk Q8u (X ^ 5 + X ^ 4 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + 1 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8u_degree]
    have hd : (X ^ 5 + X ^ 4 + 1 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #22: `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8v : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q8v_monic : Q8v.Monic := by unfold Q8v; monicity!
theorem Q8v_degree : Q8v.degree = 8 := by unfold Q8v; compute_degree!
theorem Q8v_natDegree : Q8v.natDegree = 8 := by
  have := Q8v_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8v; exact Q8v_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8v) :=
  AdjoinRoot.nontrivial Q8v (by rw [Q8v_degree]; decide)
instance : CharP (AdjoinRoot Q8v) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8v)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8v : (AdjoinRoot.root Q8v) ^ 8 = AdjoinRoot.root Q8v ^ 7 + AdjoinRoot.root Q8v ^ 5 + AdjoinRoot.root Q8v ^ 4 + AdjoinRoot.root Q8v ^ 3 + AdjoinRoot.root Q8v ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8v) Q8v = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8v) Q8v = (AdjoinRoot.root Q8v) ^ 8 + (AdjoinRoot.root Q8v) ^ 7 + (AdjoinRoot.root Q8v) ^ 5 + (AdjoinRoot.root Q8v) ^ 4 + (AdjoinRoot.root Q8v) ^ 3 + (AdjoinRoot.root Q8v) ^ 2 + 1 := by
    unfold Q8v; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8v) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8v ^ 7 + AdjoinRoot.root Q8v ^ 5 + AdjoinRoot.root Q8v ^ 4 + AdjoinRoot.root Q8v ^ 3 + AdjoinRoot.root Q8v ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_v : ¬ Q8v ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8v with hr
  have hmkP : AdjoinRoot.mk Q8v POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q8v
  have h2 : (2 : AdjoinRoot Q8v) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 7 + r ^ 6 + r ^ 2 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 5 + r ^ 4 + r ^ 3) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h9 + h8 + (r ^ 7 + r ^ 3 + r ^ 2) * h2
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 2 + r := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 5 + r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 7 + r ^ 4 + r ^ 3) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 7 + r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h15 + h8 + (r ^ 5 + r ^ 3) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 4 + r := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 3 + r ^ 2 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 4 + r = AdjoinRoot.mk Q8v (X ^ 6 + X ^ 4 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 4 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8v_degree]
    have hd : (X ^ 6 + X ^ 4 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #23: `X ^ 8 + X ^ 7 + X ^ 6 + X + 1`. -/
noncomputable def Q8w : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X + 1
theorem Q8w_monic : Q8w.Monic := by unfold Q8w; monicity!
theorem Q8w_degree : Q8w.degree = 8 := by unfold Q8w; compute_degree!
theorem Q8w_natDegree : Q8w.natDegree = 8 := by
  have := Q8w_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8w; exact Q8w_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8w) :=
  AdjoinRoot.nontrivial Q8w (by rw [Q8w_degree]; decide)
instance : CharP (AdjoinRoot Q8w) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8w)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r + 1`. -/
theorem root_Q8w : (AdjoinRoot.root Q8w) ^ 8 = AdjoinRoot.root Q8w ^ 7 + AdjoinRoot.root Q8w ^ 6 + AdjoinRoot.root Q8w + 1 := by
  have h0 : (AdjoinRoot.mk Q8w) Q8w = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8w) Q8w = (AdjoinRoot.root Q8w) ^ 8 + (AdjoinRoot.root Q8w) ^ 7 + (AdjoinRoot.root Q8w) ^ 6 + AdjoinRoot.root Q8w + 1 := by
    unfold Q8w; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8w) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8w ^ 7 + AdjoinRoot.root Q8w ^ 6 + AdjoinRoot.root Q8w + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_w : ¬ Q8w ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8w with hr
  have hmkP : AdjoinRoot.mk Q8w POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r + 1 := root_Q8w
  have h2 : (2 : AdjoinRoot Q8w) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 2 + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 3 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h10 + h8
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h11 + h8 + (r ^ 7 + r) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 7) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 7 + r ^ 6) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 3 + r ^ 2 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 = AdjoinRoot.mk Q8w (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8w_degree]
    have hd : (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #24: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X + 1`. -/
noncomputable def Q8x : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X + 1
theorem Q8x_monic : Q8x.Monic := by unfold Q8x; monicity!
theorem Q8x_degree : Q8x.degree = 8 := by unfold Q8x; compute_degree!
theorem Q8x_natDegree : Q8x.natDegree = 8 := by
  have := Q8x_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8x; exact Q8x_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8x) :=
  AdjoinRoot.nontrivial Q8x (by rw [Q8x_degree]; decide)
instance : CharP (AdjoinRoot Q8x) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8x)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + r + 1`. -/
theorem root_Q8x : (AdjoinRoot.root Q8x) ^ 8 = AdjoinRoot.root Q8x ^ 7 + AdjoinRoot.root Q8x ^ 6 + AdjoinRoot.root Q8x ^ 3 + AdjoinRoot.root Q8x ^ 2 + AdjoinRoot.root Q8x + 1 := by
  have h0 : (AdjoinRoot.mk Q8x) Q8x = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8x) Q8x = (AdjoinRoot.root Q8x) ^ 8 + (AdjoinRoot.root Q8x) ^ 7 + (AdjoinRoot.root Q8x) ^ 6 + (AdjoinRoot.root Q8x) ^ 3 + (AdjoinRoot.root Q8x) ^ 2 + AdjoinRoot.root Q8x + 1 := by
    unfold Q8x; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8x) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8x ^ 7 + AdjoinRoot.root Q8x ^ 6 + AdjoinRoot.root Q8x ^ 3 + AdjoinRoot.root Q8x ^ 2 + AdjoinRoot.root Q8x + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_x : ¬ Q8x ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8x with hr
  have hmkP : AdjoinRoot.mk Q8x POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + r + 1 := root_Q8x
  have h2 : (2 : AdjoinRoot Q8x) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 4 + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 3 + r ^ 2 + r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 5 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 3 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 6 + r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h11 + h8 + (r ^ 2 + r) * h2
  have h13 : r ^ 13 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 7 + r) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 5 + r ^ 4 + r ^ 3 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 7 + r ^ 6 + r ^ 2) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + r := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 5 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 4 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 5 + r ^ 2 = AdjoinRoot.mk Q8x (X ^ 7 + X ^ 5 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 5 + X ^ 2 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8x_degree]
    have hd : (X ^ 7 + X ^ 5 + X ^ 2 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #25: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1`. -/
noncomputable def Q8y : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1
theorem Q8y_monic : Q8y.Monic := by unfold Q8y; monicity!
theorem Q8y_degree : Q8y.degree = 8 := by unfold Q8y; compute_degree!
theorem Q8y_natDegree : Q8y.natDegree = 8 := by
  have := Q8y_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8y; exact Q8y_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8y) :=
  AdjoinRoot.nontrivial Q8y (by rw [Q8y_degree]; decide)
instance : CharP (AdjoinRoot Q8y) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8y)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 2 + r + 1`. -/
theorem root_Q8y : (AdjoinRoot.root Q8y) ^ 8 = AdjoinRoot.root Q8y ^ 7 + AdjoinRoot.root Q8y ^ 6 + AdjoinRoot.root Q8y ^ 4 + AdjoinRoot.root Q8y ^ 2 + AdjoinRoot.root Q8y + 1 := by
  have h0 : (AdjoinRoot.mk Q8y) Q8y = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8y) Q8y = (AdjoinRoot.root Q8y) ^ 8 + (AdjoinRoot.root Q8y) ^ 7 + (AdjoinRoot.root Q8y) ^ 6 + (AdjoinRoot.root Q8y) ^ 4 + (AdjoinRoot.root Q8y) ^ 2 + AdjoinRoot.root Q8y + 1 := by
    unfold Q8y; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8y) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8y ^ 7 + AdjoinRoot.root Q8y ^ 6 + AdjoinRoot.root Q8y ^ 4 + AdjoinRoot.root Q8y ^ 2 + AdjoinRoot.root Q8y + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_y : ¬ Q8y ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8y with hr
  have hmkP : AdjoinRoot.mk Q8y POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 2 + r + 1 := root_Q8y
  have h2 : (2 : AdjoinRoot Q8y) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 2 + r) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 4 + r + 1 := by linear_combination r * h10 + h8 + (r ^ 7 + r ^ 6 + r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 6 + r ^ 5 + r ^ 2 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 6 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 7 + r ^ 4) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 4 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 2 + r := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 5 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 2 + r = AdjoinRoot.mk Q8y (X ^ 7 + X ^ 2 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 2 + X : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8y_degree]
    have hd : (X ^ 7 + X ^ 2 + X : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #26: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + 1`. -/
noncomputable def Q8z : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + 1
theorem Q8z_monic : Q8z.Monic := by unfold Q8z; monicity!
theorem Q8z_degree : Q8z.degree = 8 := by unfold Q8z; compute_degree!
theorem Q8z_natDegree : Q8z.natDegree = 8 := by
  have := Q8z_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8z; exact Q8z_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8z) :=
  AdjoinRoot.nontrivial Q8z (by rw [Q8z_degree]; decide)
instance : CharP (AdjoinRoot Q8z) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8z)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1`. -/
theorem root_Q8z : (AdjoinRoot.root Q8z) ^ 8 = AdjoinRoot.root Q8z ^ 7 + AdjoinRoot.root Q8z ^ 6 + AdjoinRoot.root Q8z ^ 4 + AdjoinRoot.root Q8z ^ 3 + AdjoinRoot.root Q8z ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8z) Q8z = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8z) Q8z = (AdjoinRoot.root Q8z) ^ 8 + (AdjoinRoot.root Q8z) ^ 7 + (AdjoinRoot.root Q8z) ^ 6 + (AdjoinRoot.root Q8z) ^ 4 + (AdjoinRoot.root Q8z) ^ 3 + (AdjoinRoot.root Q8z) ^ 2 + 1 := by
    unfold Q8z; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8z) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8z ^ 7 + AdjoinRoot.root Q8z ^ 6 + AdjoinRoot.root Q8z ^ 4 + AdjoinRoot.root Q8z ^ 3 + AdjoinRoot.root Q8z ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_z : ¬ Q8z ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8z with hr
  have hmkP : AdjoinRoot.mk Q8z POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := root_Q8z
  have h2 : (2 : AdjoinRoot Q8z) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 6 + r ^ 5 + r ^ 2 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 4 + r ^ 3) * h2
  have h10 : r ^ 10 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + 1 := by linear_combination r * h10 + h8 + (r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2) * h2
  have h12 : r ^ 12 = r ^ 7 + r := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h12 + h8 + (r ^ 2) * h2
  have h14 : r ^ 14 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h13 + h8 + (r ^ 7 + r ^ 4) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + 1 := by linear_combination r * h15 + h8 + (r ^ 7 + r ^ 4 + r ^ 3 + r ^ 2) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 := by
    rw [h16, h12]; linear_combination (r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 5 + r ^ 3 = AdjoinRoot.mk Q8z (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8z_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #27: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X + 1`. -/
noncomputable def Q8aa : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X + 1
theorem Q8aa_monic : Q8aa.Monic := by unfold Q8aa; monicity!
theorem Q8aa_degree : Q8aa.degree = 8 := by unfold Q8aa; compute_degree!
theorem Q8aa_natDegree : Q8aa.natDegree = 8 := by
  have := Q8aa_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8aa; exact Q8aa_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8aa) :=
  AdjoinRoot.nontrivial Q8aa (by rw [Q8aa_degree]; decide)
instance : CharP (AdjoinRoot Q8aa) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8aa)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + r + 1`. -/
theorem root_Q8aa : (AdjoinRoot.root Q8aa) ^ 8 = AdjoinRoot.root Q8aa ^ 7 + AdjoinRoot.root Q8aa ^ 6 + AdjoinRoot.root Q8aa ^ 5 + AdjoinRoot.root Q8aa ^ 2 + AdjoinRoot.root Q8aa + 1 := by
  have h0 : (AdjoinRoot.mk Q8aa) Q8aa = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8aa) Q8aa = (AdjoinRoot.root Q8aa) ^ 8 + (AdjoinRoot.root Q8aa) ^ 7 + (AdjoinRoot.root Q8aa) ^ 6 + (AdjoinRoot.root Q8aa) ^ 5 + (AdjoinRoot.root Q8aa) ^ 2 + AdjoinRoot.root Q8aa + 1 := by
    unfold Q8aa; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8aa) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8aa ^ 7 + AdjoinRoot.root Q8aa ^ 6 + AdjoinRoot.root Q8aa ^ 5 + AdjoinRoot.root Q8aa ^ 2 + AdjoinRoot.root Q8aa + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_aa : ¬ Q8aa ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8aa with hr
  have hmkP : AdjoinRoot.mk Q8aa POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 2 + r + 1 := root_Q8aa
  have h2 : (2 : AdjoinRoot Q8aa) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 5 + r ^ 3 + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 6 + r ^ 2 + r) * h2
  have h10 : r ^ 10 = r ^ 6 + r ^ 4 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 7 + r ^ 5 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h11 + h8 + (r ^ 6) * h2
  have h13 : r ^ 13 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h12 + h8 + (r ^ 6 + r ^ 2 + r) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h13 + h8 + (r ^ 6 + r ^ 5 + r) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h14 + h8 + (r ^ 5 + r) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + 1 := by linear_combination r * h15 + h8 + (r ^ 7 + r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + 1 := by
    rw [h16, h12]; linear_combination (r ^ 5 + r ^ 3 + r ^ 2 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + 1 = AdjoinRoot.mk Q8aa (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8aa_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #28: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1`. -/
noncomputable def Q8ab : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1
theorem Q8ab_monic : Q8ab.Monic := by unfold Q8ab; monicity!
theorem Q8ab_degree : Q8ab.degree = 8 := by unfold Q8ab; compute_degree!
theorem Q8ab_natDegree : Q8ab.natDegree = 8 := by
  have := Q8ab_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8ab; exact Q8ab_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8ab) :=
  AdjoinRoot.nontrivial Q8ab (by rw [Q8ab_degree]; decide)
instance : CharP (AdjoinRoot Q8ab) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8ab)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r + 1`. -/
theorem root_Q8ab : (AdjoinRoot.root Q8ab) ^ 8 = AdjoinRoot.root Q8ab ^ 7 + AdjoinRoot.root Q8ab ^ 6 + AdjoinRoot.root Q8ab ^ 5 + AdjoinRoot.root Q8ab ^ 4 + AdjoinRoot.root Q8ab + 1 := by
  have h0 : (AdjoinRoot.mk Q8ab) Q8ab = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8ab) Q8ab = (AdjoinRoot.root Q8ab) ^ 8 + (AdjoinRoot.root Q8ab) ^ 7 + (AdjoinRoot.root Q8ab) ^ 6 + (AdjoinRoot.root Q8ab) ^ 5 + (AdjoinRoot.root Q8ab) ^ 4 + AdjoinRoot.root Q8ab + 1 := by
    unfold Q8ab; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8ab) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8ab ^ 7 + AdjoinRoot.root Q8ab ^ 6 + AdjoinRoot.root Q8ab ^ 5 + AdjoinRoot.root Q8ab ^ 4 + AdjoinRoot.root Q8ab + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1`.** -/
theorem POLY_poly_no_deg8_factor_ab : ¬ Q8ab ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8ab with hr
  have hmkP : AdjoinRoot.mk Q8ab POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r + 1 := root_Q8ab
  have h2 : (2 : AdjoinRoot Q8ab) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 4 + r ^ 2 + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 6 + r ^ 5 + r) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 3 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 4 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 5 + r ^ 3 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 5 + r + 1 := by linear_combination r * h12 + h8 + (r ^ 6 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 7 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := by linear_combination r * h13 + h8 + (r ^ 6 + r) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h14 + h8 + (r ^ 6 + r ^ 5 + r) * h2
  have h16 : r ^ 16 = r ^ 7 + r ^ 6 + 1 := by linear_combination r * h15 + h8 + (r ^ 5 + r ^ 4 + r) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 6 + r ^ 5 + r := by
    rw [h16, h12]; linear_combination (r ^ 7 + r ^ 3 + 1) * h2
  rw [hval]
  have hrw : r ^ 6 + r ^ 5 + r = AdjoinRoot.mk Q8ab (X ^ 6 + X ^ 5 + X) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 6 + X ^ 5 + X : (ZMod 2)[X]).degree = 6 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8ab_degree]
    have hd : (X ^ 6 + X ^ 5 + X : (ZMod 2)[X]).degree ≤ 6 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #29: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1`. -/
noncomputable def Q8ac : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1
theorem Q8ac_monic : Q8ac.Monic := by unfold Q8ac; monicity!
theorem Q8ac_degree : Q8ac.degree = 8 := by unfold Q8ac; compute_degree!
theorem Q8ac_natDegree : Q8ac.natDegree = 8 := by
  have := Q8ac_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8ac; exact Q8ac_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8ac) :=
  AdjoinRoot.nontrivial Q8ac (by rw [Q8ac_degree]; decide)
instance : CharP (AdjoinRoot Q8ac) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8ac)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + 1`. -/
theorem root_Q8ac : (AdjoinRoot.root Q8ac) ^ 8 = AdjoinRoot.root Q8ac ^ 7 + AdjoinRoot.root Q8ac ^ 6 + AdjoinRoot.root Q8ac ^ 5 + AdjoinRoot.root Q8ac ^ 4 + AdjoinRoot.root Q8ac ^ 2 + 1 := by
  have h0 : (AdjoinRoot.mk Q8ac) Q8ac = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8ac) Q8ac = (AdjoinRoot.root Q8ac) ^ 8 + (AdjoinRoot.root Q8ac) ^ 7 + (AdjoinRoot.root Q8ac) ^ 6 + (AdjoinRoot.root Q8ac) ^ 5 + (AdjoinRoot.root Q8ac) ^ 4 + (AdjoinRoot.root Q8ac) ^ 2 + 1 := by
    unfold Q8ac; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8ac) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8ac ^ 7 + AdjoinRoot.root Q8ac ^ 6 + AdjoinRoot.root Q8ac ^ 5 + AdjoinRoot.root Q8ac ^ 4 + AdjoinRoot.root Q8ac ^ 2 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1`.** -/
theorem POLY_poly_no_deg8_factor_ac : ¬ Q8ac ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8ac with hr
  have hmkP : AdjoinRoot.mk Q8ac POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 2 + 1 := root_Q8ac
  have h2 : (2 : AdjoinRoot Q8ac) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 6 + r ^ 5) * h2
  have h10 : r ^ 10 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 2 + 1 := by linear_combination r * h12 + h8 + (r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4) * h2
  have h14 : r ^ 14 = r ^ 3 + r := by linear_combination r * h13
  have h15 : r ^ 15 = r ^ 4 + r ^ 2 := by linear_combination r * h14
  have h16 : r ^ 16 = r ^ 5 + r ^ 3 := by linear_combination r * h15
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r + 1 := by
    rw [h16, h12]; linear_combination (r ^ 5 + r ^ 3) * h2
  rw [hval]
  have hrw : r ^ 7 + r ^ 6 + r ^ 4 + r ^ 3 + r + 1 = AdjoinRoot.mk Q8ac (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X + 1) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree = 7 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8ac_degree]
    have hd : (X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]).degree ≤ 7 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

/-- Monic irreducible degree-8 #30: `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1`. -/
noncomputable def Q8ad : (ZMod 2)[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1
theorem Q8ad_monic : Q8ad.Monic := by unfold Q8ad; monicity!
theorem Q8ad_degree : Q8ad.degree = 8 := by unfold Q8ad; compute_degree!
theorem Q8ad_natDegree : Q8ad.natDegree = 8 := by
  have := Q8ad_degree
  rw [Polynomial.degree_eq_natDegree (by unfold Q8ad; exact Q8ad_monic.ne_zero)] at this
  exact_mod_cast this
instance : Nontrivial (AdjoinRoot Q8ad) :=
  AdjoinRoot.nontrivial Q8ad (by rw [Q8ad_degree]; decide)
instance : CharP (AdjoinRoot Q8ad) 2 :=
  charP_of_injective_algebraMap ((algebraMap (ZMod 2) (AdjoinRoot Q8ad)).injective) 2
/-- Root relation: `r^8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1`. -/
theorem root_Q8ad : (AdjoinRoot.root Q8ad) ^ 8 = AdjoinRoot.root Q8ad ^ 7 + AdjoinRoot.root Q8ad ^ 6 + AdjoinRoot.root Q8ad ^ 5 + AdjoinRoot.root Q8ad ^ 4 + AdjoinRoot.root Q8ad ^ 3 + 1 := by
  have h0 : (AdjoinRoot.mk Q8ad) Q8ad = 0 := AdjoinRoot.mk_self
  have he : (AdjoinRoot.mk Q8ad) Q8ad = (AdjoinRoot.root Q8ad) ^ 8 + (AdjoinRoot.root Q8ad) ^ 7 + (AdjoinRoot.root Q8ad) ^ 6 + (AdjoinRoot.root Q8ad) ^ 5 + (AdjoinRoot.root Q8ad) ^ 4 + (AdjoinRoot.root Q8ad) ^ 3 + 1 := by
    unfold Q8ad; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  have h2 : (2 : AdjoinRoot Q8ad) = 0 := CharTwo.two_eq_zero
  rw [he] at h0
  linear_combination h0 - (AdjoinRoot.root Q8ad ^ 7 + AdjoinRoot.root Q8ad ^ 6 + AdjoinRoot.root Q8ad ^ 5 + AdjoinRoot.root Q8ad ^ 4 + AdjoinRoot.root Q8ad ^ 3 + 1) * h2
/-- **`POLY_poly` has no degree-8 factor `X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1`.** -/
theorem POLY_poly_no_deg8_factor_ad : ¬ Q8ad ∣ POLY_poly := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root Q8ad with hr
  have hmkP : AdjoinRoot.mk Q8ad POLY_poly = r ^ 16 + r ^ 12 + r ^ 3 + r + 1 := by
    unfold Spqr.Gf16Field.POLY_poly
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X, hr]
  rw [hmkP]
  have h8 : r ^ 8 = r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + 1 := root_Q8ad
  have h2 : (2 : AdjoinRoot Q8ad) = 0 := CharTwo.two_eq_zero
  have h9 : r ^ 9 = r ^ 3 + r + 1 := by linear_combination r * h8 + h8 + (r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4) * h2
  have h10 : r ^ 10 = r ^ 4 + r ^ 2 + r := by linear_combination r * h9
  have h11 : r ^ 11 = r ^ 5 + r ^ 3 + r ^ 2 := by linear_combination r * h10
  have h12 : r ^ 12 = r ^ 6 + r ^ 4 + r ^ 3 := by linear_combination r * h11
  have h13 : r ^ 13 = r ^ 7 + r ^ 5 + r ^ 4 := by linear_combination r * h12
  have h14 : r ^ 14 = r ^ 7 + r ^ 4 + r ^ 3 + 1 := by linear_combination r * h13 + h8 + (r ^ 6 + r ^ 5) * h2
  have h15 : r ^ 15 = r ^ 7 + r ^ 6 + r ^ 3 + r + 1 := by linear_combination r * h14 + h8 + (r ^ 5 + r ^ 4) * h2
  have h16 : r ^ 16 = r ^ 6 + r ^ 5 + r ^ 3 + r ^ 2 + r + 1 := by linear_combination r * h15 + h8 + (r ^ 7 + r ^ 4) * h2
  have hval : r ^ 16 + r ^ 12 + r ^ 3 + r + 1 = r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 := by
    rw [h16, h12]; linear_combination (r ^ 6 + r ^ 3 + r + 1) * h2
  rw [hval]
  have hrw : r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 = AdjoinRoot.mk Q8ad (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2) := by
    rw [hr]; simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
  rw [hrw]
  refine mk_ne_zero_of_degree_lt ?_ ?_
  · have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree = 5 := by compute_degree!
    intro h; rw [h] at hd; simp at hd
  · rw [Q8ad_degree]
    have hd : (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 : (ZMod 2)[X]).degree ≤ 5 := by compute_degree
    exact lt_of_le_of_lt hd (by decide)

end Spqr.Gf16Irreducible
