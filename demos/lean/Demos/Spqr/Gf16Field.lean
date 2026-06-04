/-
  SPQR Reed–Solomon codec — Layer B (PARTIAL): structural sub-results toward the
  GF(2¹⁶) field instance for the extracted field arithmetic.

  ## What this file establishes (genuine, in-boundary, field-law-FREE)

  The deep endpoint of `decode ∘ encode = id` needs the extracted
  `(U16, gfAddV = XOR, gfMulV = poly_reduce ∘ poly_mul)` to be a field isomorphic
  to GF(2¹⁶) = GF(2)[X]/(POLY), `POLY = x¹⁶+x¹²+x³+x+1`. This file banks the part
  of that obligation that closes STRUCTURALLY this round, with NO field-law cheat:

  1. **The additive group on `gfAddV`** (the value spec of the extracted `gf_add`):
     `gfAddV` is commutative, associative, has identity `0`, and is its own inverse
     (characteristic 2). These are proved structurally from `BitVec` XOR — they are
     genuinely about the extracted field-add (`gfAddV` ties to `gf.gf_add` via the
     banked `gf_add_eq`).

  2. **The bit↔coefficient embedding `toPoly : U16 → (ZMod 2)[X]`** and the proof
     that `gfAddV` is EXACTLY polynomial addition under it:
     `toPoly (gfAddV a b) = toPoly a + toPoly b`. This is the honest "XOR-as-poly-add"
     half of the ring-iso `U16 ≅ (ZMod 2)[X]/(POLY)`, proved from the bitwise
     definition of XOR (no field laws, no `decide` over the value space).

  3. **The reduction polynomial `POLY_poly : (ZMod 2)[X]`** named as `x¹⁶+x¹²+x³+x+1`
     with its cheap structural facts (`Monic`, `natDegree = 16`, `≠ 0`, `≠ 1`).

  ## The DOCUMENTED GAP (the genuine wall, NOT closed — and NOT faked)

  The multiplicative side of the field instance is NOT closed here, and is left as a
  precise, honest obligation rather than papered over with a cheat:

    (B-mul)  `gfMulV` is multiplication in `(ZMod 2)[X]/(POLY)`: i.e. `poly_mul` is the
             carryless coefficient convolution and `poly_reduce` is reduction mod POLY.
    (B-irr)  `Irreducible POLY_poly` over `ZMod 2`. `decide` is genuinely dead on
             `(ZMod 2)[X]` (a hard `Finsupp` non-reduction, verified at degree 0 — see
             section 4), there is no `Decidable (Irreducible …)` instance, and Mathlib has
             no Rabin-style test; the honest routes are a structural factor-exclusion
             (≈70 monic irreducibles of degree 2..8) or a computable mirror + transport,
             both multi-round. The degree-1 stratum IS closed here
             (`POLY_poly_no_linear_factor`); the rest is the documented gap (section 4).

  Given (B-mul) + (B-irr), `AdjoinRoot.instField` would supply `Field (AdjoinRoot POLY_poly)`,
  and the ring-iso (additive half banked here, multiplicative half = B-mul) would transport
  the field structure to `(U16, gfAddV, gfMulV)`. We do NOT introduce any axiom for
  irreducibility, do NOT `decide` over the value space, and do NOT transport a field
  through an unproven-multiplicative bijection (the circularity trap). The additive group
  laws and the XOR↔poly-add bridge are the part that is honestly provable now.

  NOTE: this file deliberately registers ONLY the additive-group / XOR-as-poly-add
  results as Audit.lean headlines (they are about `gfAddV`, the extracted field add).
  The multiplicative field instance stays an open, documented obligation.
-/
import Demos.Spqr.Gf
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.ComputeDegree

open Aeneas Std Result
open Spqr.Gf
open Polynomial

namespace Spqr.Gf16Field

/-! ### 1. The additive group structure on the extracted field add (`gfAddV` = XOR)

`gfAddV a b = a ^^^ b` is the value spec of the extracted `gf.gf_add` (banked as
`gf_add_eq`). In characteristic 2 the additive group is `(U16, XOR, 0)`. We prove the
abelian-group laws structurally from `BitVec` XOR — no field laws, no value-space `decide`. -/

/-- **`gfAddV` is commutative** (characteristic-2 field addition is symmetric). -/
theorem gfAddV_comm (a b : Std.U16) : gfAddV a b = gfAddV b a := by
  unfold gfAddV; ext1; simp only [UScalar.bv_xor]; exact BitVec.xor_comm _ _

/-- **`gfAddV` is associative.** -/
theorem gfAddV_assoc (a b c : Std.U16) :
    gfAddV (gfAddV a b) c = gfAddV a (gfAddV b c) := by
  unfold gfAddV; ext1; simp only [UScalar.bv_xor]; exact BitVec.xor_assoc _ _ _

/-- **`0` is a right identity for `gfAddV`.** -/
theorem gfAddV_zero (a : Std.U16) : gfAddV a 0#u16 = a := by
  unfold gfAddV; ext1; simp only [UScalar.bv_xor]; exact BitVec.xor_zero

/-- **`0` is a left identity for `gfAddV`.** -/
theorem gfAddV_zero_left (a : Std.U16) : gfAddV 0#u16 a = a := by
  unfold gfAddV; ext1; simp only [UScalar.bv_xor]; rw [BitVec.xor_comm]; exact BitVec.xor_zero

/-- **Every element is its own `gfAddV`-inverse** (characteristic 2). -/
theorem gfAddV_self (a : Std.U16) : gfAddV a a = 0#u16 := by
  unfold gfAddV; ext1; simp only [UScalar.bv_xor]; exact BitVec.xor_self

/-! ### 2. The bit↔coefficient embedding and `gfAddV` = polynomial addition

`toPoly a = Σ_{i<16} a.bv[i] · X^i` over `(ZMod 2)[X]`: the polynomial whose `i`-th
coefficient is bit `i` of `a` (as an element of `ZMod 2`). This is the additive half of
the ring-iso `U16 ≅ (ZMod 2)[X]/(POLY)` — and we prove `gfAddV` is EXACTLY polynomial
addition under it. The multiplicative half (`gfMulV` = `·` mod POLY) is the documented gap. -/

/-- Bit `i` (LSB-indexed) of a `U16`, as an element of `ZMod 2` (`0` or `1`), read off
the natural-number value (`a.val = a.bv.toNat`). -/
def bitZ (a : Std.U16) (i : Nat) : ZMod 2 := if a.val.testBit i then 1 else 0

/-- The bit↔coefficient embedding `U16 → (ZMod 2)[X]`: coefficient `i` is bit `i`. -/
noncomputable def toPoly (a : Std.U16) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 16, C (bitZ a i) * X ^ i

/-- In `ZMod 2`, the bit of an XOR is the sum of the bits: `bitZ (a^^^b) i = bitZ a i + bitZ b i`.
Proved from `UScalar.val_xor` (the XOR's value is the `Nat` XOR of the values) and
`Nat.testBit_xor`. -/
theorem bitZ_xor (a b : Std.U16) (i : Nat) :
    bitZ (gfAddV a b) i = bitZ a i + bitZ b i := by
  unfold bitZ gfAddV
  rw [UScalar.val_xor, Nat.testBit_xor]
  -- a Boolean-XOR ↦ ZMod 2 addition fact, by cases on the two bits
  cases a.val.testBit i <;> cases b.val.testBit i <;> decide

/-- **`gfAddV` is polynomial addition under `toPoly`** (the XOR-as-poly-add bridge).
This is the additive half of the ring-iso `U16 ≅ (ZMod 2)[X]/(POLY)`, proved from the
bitwise definition of XOR — no field laws, no value-space `decide`. -/
theorem toPoly_gfAddV (a b : Std.U16) :
    toPoly (gfAddV a b) = toPoly a + toPoly b := by
  unfold toPoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [bitZ_xor a b i, map_add, add_mul]

/-! ### 3. The reduction polynomial `POLY_poly = x¹⁶ + x¹² + x³ + x + 1` over `ZMod 2`

The extracted `gf.POLY = 69643#u32 = 0x1100b` is the bit pattern of `x¹⁶+x¹²+x³+x+1`.
Here we name that polynomial over `ZMod 2` and bank its cheap structural facts. The
bridge `gf.POLY ↔ POLY_poly` and the reduction-correctness (`B-mul`) are the open gap. -/

/-- The GF(2¹⁶) reduction polynomial `x¹⁶ + x¹² + x³ + x + 1` over `ZMod 2`. -/
noncomputable def POLY_poly : (ZMod 2)[X] :=
  X ^ 16 + X ^ 12 + X ^ 3 + X + 1

/-- `POLY_poly` is monic (leading coefficient `1`). -/
theorem POLY_poly_monic : POLY_poly.Monic := by
  unfold POLY_poly
  monicity!

/-- `POLY_poly` has degree exactly 16. -/
theorem POLY_poly_natDegree : POLY_poly.natDegree = 16 := by
  unfold POLY_poly
  compute_degree!

/-- `POLY_poly ≠ 0`. -/
theorem POLY_poly_ne_zero : POLY_poly ≠ 0 :=
  POLY_poly_monic.ne_zero

/-- `POLY_poly ≠ 1` (it has degree 16 > 0). -/
theorem POLY_poly_ne_one : POLY_poly ≠ 1 := by
  intro h
  have : POLY_poly.natDegree = 0 := by rw [h]; simp
  rw [POLY_poly_natDegree] at this
  exact absurd this (by decide)

/-! ### 4. Partial factor-exclusion toward irreducibility (B-irr): no linear factor

`Irreducible POLY_poly` is the multiplicative-side wall (the documented gap below). As a
genuine, structurally-proved step toward it we bank here the *degree-1 factor exclusion*:
`POLY_poly` has no root over `ZMod 2`, hence no monic linear factor `X - C a`. Over a field,
a degree-1 monic divisor is exactly `X - C a` for a root `a`, so this rules out the entire
`Finset.Ioc 0 8`-degree-1 stratum of the `Monic.irreducible_iff_lt_natDegree_lt` criterion.

This does NOT prove irreducibility (a reducible degree-16 polynomial can factor into two
degree-8 irreducibles with no root); it is an honest sub-result, proved structurally with no
`decide` over `(ZMod 2)[X]` and no axiom. The constant term is `1` (so `0` is not a root) and
at `x = 1` the five terms sum to `1 ≠ 0` in `ZMod 2`; the residual `decide` only touches
finite `ZMod 2` arithmetic on the evaluated value, never the non-reducing `Polynomial`. -/

/-- **`POLY_poly` has no root in `ZMod 2`.** (Excludes degree-1 factors; a building block,
not the irreducibility theorem.) -/
theorem POLY_poly_no_root : ∀ x : ZMod 2, POLY_poly.eval x ≠ 0 := by
  intro x
  fin_cases x <;> (unfold POLY_poly; simp) <;> decide

/-- **`POLY_poly` has no monic linear factor** `X - C a` over `ZMod 2`: it has no root, and
over a field `X - C a ∣ p ↔ p.IsRoot a`. (Building block toward `Irreducible POLY_poly`.) -/
theorem POLY_poly_no_linear_factor : ∀ a : ZMod 2, ¬ (X - C a : (ZMod 2)[X]) ∣ POLY_poly := by
  intro a hdvd
  rw [Polynomial.dvd_iff_isRoot] at hdvd
  exact POLY_poly_no_root a hdvd

/-! ### B-irr — the open obligation, with the precise remaining work (NOT faked)

`Irreducible (POLY_poly : (ZMod 2)[X])` is **NOT closed this round**, and is left as an HONEST
DOCUMENTED GAP — never an axiom, `sorry`, or `native_decide`. What was established and why it
does not yet close:

* **`decide` is genuinely dead on `(ZMod 2)[X]`**, verified empirically (not assumed) at the
  cheapest possible degree: even `(POLY_poly).coeff 0 = 1` fails `decide` — its `Decidable`
  instance unfolds through `Classical.propDecidable`/`ZMod.decidableEq` and reduction gets
  STUCK on the `Finsupp`/`AddMonoidAlgebra` representation of `Polynomial`, which the kernel
  cannot reduce. So NO fact about any `(ZMod 2)[X]` polynomial is `decide`-able in Mathlib's
  representation; this is a hard non-reduction, not a degree-16 timeout. (`simp` closes
  `coeff 0 = 1` fine — but `simp` is not a decision procedure for irreducibility.)
* **There is no `Decidable (Irreducible p)` instance** for `p : (ZMod 2)[X]` to hand to `decide`,
  and `Monic.irreducible_iff_lt_natDegree_lt` reduces it to `∀ q, q.Monic → q.natDegree ∈
  Finset.Ioc 0 8 → ¬ q ∣ p` — a quantifier over the INFINITE type `(ZMod 2)[X]`, still not
  Decidable, and each `¬ q ∣ p` is `p %ₘ q ≠ 0`, again over the non-reducing representation.
* **No Rabin-style irreducibility test exists in Mathlib** for this case (search found only
  Kummer-type `X_pow_sub_C_irreducible_iff…`, not applicable to `x¹⁶+x¹²+x³+x+1`).

**What remains** is therefore one of: (a) a full structural factor-exclusion — ruling out every
monic irreducible factor of degree 2..8 (≈70 irreducibles, each `¬ q ∣ POLY_poly` a hand
`%ₘ` computation over the non-reducing representation, no automation) — multi-round; or (b) a
SEPARATE computable mirror of `(ZMod 2)[X]` up to degree 16 (as `BitVec`/`Nat`/`List`) with a
custom carryless-`%`, `decide` irreducibility there over the ≈510 monic candidates of degree
≤ 8, then transport "no factor" back to `Polynomial` through a proven representation iso — whose
hard half (the mirror↔`Polynomial` factor correspondence) is itself most of the work.

The degree-1 stratum is closed above (`POLY_poly_no_linear_factor`). Until `Irreducible
POLY_poly` is proved, the field instance `Field (U16, gfAddV, gfMulV) ≅ GaloisField 2 16` and
the unconditional `decode ∘ encode = id` capstone must carry `Irreducible POLY_poly` (or
`Fact (Irreducible POLY_poly)`) as an explicit, satisfiable PREMISE — never an axiom. -/

end Spqr.Gf16Field
