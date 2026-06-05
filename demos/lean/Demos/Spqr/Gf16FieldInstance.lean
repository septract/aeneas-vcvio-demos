/-
  SPQR Reed–Solomon codec — Layer B, FIELD INSTANCE (the bridge prerequisite).

  ## What this file establishes

  Stage 2 (`Gf16ReduceTable`) discharged the multiplicative bridge `hmul`
  UNCONDITIONALLY, so the embedding

      φ = AdjoinRoot.mk POLY_poly ∘ toPoly : U16 → AdjoinRoot POLY_poly

  is now an UNCONDITIONAL ring homomorphism in the sense that it commutes with the
  extracted `gfAddV`/`gfMulV` and sends `0/1` to `0/1` (`phi_gfAddV`, `hmul_proved`,
  `phi_one`, `phi_zero`), and it is bijective (`phi_injective` + `phi_surjective`, both
  banked, UNCONDITIONAL). This file packages that into the genuine algebraic objects the
  interpolation bridge needs:

  * **`GF16`** — a type synonym for `Std.U16` carrying a `CommRing` whose `+` / `*` ARE the
    extracted `gfAddV` / `gfMulV` (UNCONDITIONAL). The ring laws come from `AdjoinRoot`'s
    genuine ring structure, transported back through the bijection `φ` — the NON-CIRCULAR
    route (no field structure is assumed on `U16`).

  * **`phiEquiv` / `phiRingEquiv`** — the bijection `φ`, bundled first as an `Equiv` and then
    (UNCONDITIONAL) as a `RingEquiv GF16 ≃+* AdjoinRoot POLY_poly`. This is the in-boundary
    statement that the extracted field arithmetic IS the GF(2¹⁶) quotient ring `(ZMod 2)[X]/(POLY)`.

  * **`instField` (CONDITIONAL on `[Fact (Irreducible POLY_poly)]`)** — when `POLY_poly` is
    irreducible (the documented WALL, strictly weaker than the prior `hmul + Irreducible`
    pair since `hmul` is now discharged), `AdjoinRoot POLY_poly` is a field, so `GF16`
    inherits a `Field` whose `+`/`*` are still the extracted `gfAddV`/`gfMulV`. The field
    structure is genuine (from `AdjoinRoot`), reflected through the bijection — never an
    axiom, never circular.

  ## Why this is the bridge prerequisite

  Mathlib's `Lagrange.interpolate` requires `[Field F]` in its signature. To state — let
  alone prove — that the extracted decoder computes `Lagrange.interpolate` over the genuine
  GF(2¹⁶) carrier, one needs a `Field` instance on the extracted arithmetic. This file
  supplies it (conditional only on irreducibility, with `hmul` already discharged) together
  with the ring iso to `AdjoinRoot POLY_poly`, so a future round can identify the
  `prepare`/`complete`/`divFold` recurrences with the Lagrange basis polynomials and discharge
  the `hbridge` premise of `RsCapstone.decode_value_at_roundtrip`.

  ## What is NOT done / faked

  - NO `axiom`, `sorry`, `native_decide`, or circular field instance. `Irreducible POLY_poly`
    is the only remaining open premise (carried as `[Fact …]`), and it is satisfiable.
  - The full identification of the decoder loops with `Lagrange.interpolate` (the `hbridge`
    premise) is NOT closed here — it is the natural next refinement now that the field
    instance exists.
-/
import Demos.Spqr.Gf16ReduceTable
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Field.TransferInstance

open Aeneas Std Result
open Spqr.Gf
open Spqr.Gf16Field (toPoly POLY_poly)
open Spqr.Gf16FieldAssembly (phi phi_gfAddV phi_one phi_injective phi_surjective)
open Spqr.Gf16ReduceTable (hmul_proved)
open Polynomial

namespace Spqr.Gf16FieldInstance

/-! ### 0. `φ` sends `0#u16` to `0`, and `φ` is a bijection. -/

/-- `φ 0#u16 = 0` (UNCONDITIONAL): `toPoly 0 = 0`, then `mk 0 = 0`. -/
theorem phi_zero : phi 0#u16 = 0 := by
  unfold phi
  have h0 : toPoly 0#u16 = 0 := by
    apply Polynomial.ext; intro n
    rw [Spqr.Gf16Mul.coeff_toPoly]; unfold Spqr.Gf16Field.bitZ
    rw [show (0#u16 : Std.U16).val = 0 from by decide]; simp
  rw [h0, map_zero]

/-- `φ` is bijective (UNCONDITIONAL, from the banked injectivity + surjectivity). -/
theorem phi_bijective : Function.Bijective phi := ⟨phi_injective, phi_surjective⟩

/-- The bijection `φ`, bundled as an `Equiv`. `φ` itself is `phiEquiv`'s forward map. -/
noncomputable def phiEquiv : Std.U16 ≃ AdjoinRoot POLY_poly :=
  Equiv.ofBijective phi phi_bijective

@[simp] theorem phiEquiv_apply (a : Std.U16) : phiEquiv a = phi a := rfl

@[simp] theorem phiEquiv_symm_phi (a : Std.U16) : phiEquiv.symm (phi a) = a := by
  have : phiEquiv.symm (phiEquiv a) = a := phiEquiv.symm_apply_apply a
  simpa using this

/-! ### 1. The `CommRing` on `GF16` (UNCONDITIONAL), with `+`/`*` = the extracted ops.

`GF16` is `Std.U16` carrying the ring structure transported from `AdjoinRoot POLY_poly`
through the bijection `φ` (`Equiv.commRing`). This is NON-CIRCULAR: the ring laws come from
`AdjoinRoot`'s genuine ring, not assumed on `U16`. We then prove the transported `+`/`*`/`0`/`1`
ARE the extracted `gfAddV`/`gfMulV`/`0#u16`/`1#u16`, so the structure is genuinely ABOUT the
extracted field arithmetic. -/

/-- The extracted GF(2¹⁶) carrier, as a type synonym for `Std.U16` to hold the ring/field
structure without polluting `Std.U16`'s native (modular) arithmetic. -/
def GF16 : Type := Std.U16

/-- `GF16` and `Std.U16` are the same type; this is the identity reinterpretation. -/
def GF16.ofU16 (a : Std.U16) : GF16 := a
/-- Read a `GF16` back as the underlying `Std.U16`. -/
def GF16.toU16 (a : GF16) : Std.U16 := a

@[simp] theorem GF16.toU16_ofU16 (a : Std.U16) : (GF16.ofU16 a).toU16 = a := rfl
@[simp] theorem GF16.ofU16_toU16 (a : GF16) : GF16.ofU16 a.toU16 = a := rfl

/-- The bijection `φ`, re-typed with domain `GF16` (definitionally `phi` on the underlying
`U16`). -/
noncomputable def gfEquiv : GF16 ≃ AdjoinRoot POLY_poly := phiEquiv

/-- The transported `CommRing` on `GF16` (UNCONDITIONAL). -/
noncomputable instance : CommRing GF16 := gfEquiv.commRing

/-- The bundled ring isomorphism `GF16 ≃+* AdjoinRoot POLY_poly` (UNCONDITIONAL). This is the
in-boundary statement that the extracted field arithmetic forms the GF(2¹⁶) quotient ring
`(ZMod 2)[X]/(POLY)`. -/
noncomputable def gfRingEquiv : GF16 ≃+* AdjoinRoot POLY_poly := gfEquiv.ringEquiv

@[simp] theorem gfRingEquiv_apply (a : GF16) : gfRingEquiv a = phi a.toU16 := rfl

/-- The forward ring iso is exactly `φ` on the underlying `U16`. -/
theorem gfRingEquiv_eq_phi (a : GF16) : gfRingEquiv a = phi (GF16.toU16 a) := rfl

@[simp] theorem gfRingEquiv_ofU16 (a : Std.U16) : gfRingEquiv (GF16.ofU16 a) = phi a := rfl

/-! ### 2. The transported `+`/`*`/`0`/`1` ARE the extracted `gfAddV`/`gfMulV`/`0`/`1`.

These are the in-boundary facts: the ring structure on `GF16` is genuinely the extracted field
arithmetic. Each is proved by reflecting through the injective ring iso `gfRingEquiv` (whose
`map_add`/`map_mul`/`map_one`/`map_zero` reduce the goal to the banked `φ`-compatibilities
`phi_gfAddV` / `hmul_proved` / `phi_one` / `phi_zero`). -/

/-- **`GF16` addition is the extracted `gfAddV`** (UNCONDITIONAL). -/
theorem add_eq_gfAddV (a b : Std.U16) :
    GF16.ofU16 a + GF16.ofU16 b = GF16.ofU16 (gfAddV a b) := by
  apply gfRingEquiv.injective
  rw [map_add, gfRingEquiv_ofU16, gfRingEquiv_ofU16, gfRingEquiv_ofU16, phi_gfAddV]

/-- **`GF16` multiplication is the extracted `gfMulV`** (UNCONDITIONAL — `hmul` discharged via
Stage 2). This is the in-boundary statement that the field multiply of the GF(2¹⁶) ring is the
extracted `gf.gf_mul`. -/
theorem mul_eq_gfMulV (a b : Std.U16) :
    GF16.ofU16 a * GF16.ofU16 b = GF16.ofU16 (gfMulV a b) := by
  apply gfRingEquiv.injective
  rw [map_mul, gfRingEquiv_ofU16, gfRingEquiv_ofU16, gfRingEquiv_ofU16, hmul_proved]

/-- **`GF16` zero is `0#u16`** (UNCONDITIONAL). -/
theorem zero_eq : (0 : GF16) = GF16.ofU16 0#u16 := by
  apply gfRingEquiv.injective
  rw [map_zero, gfRingEquiv_ofU16, phi_zero]

/-- **`GF16` one is `1#u16`** (UNCONDITIONAL). -/
theorem one_eq : (1 : GF16) = GF16.ofU16 1#u16 := by
  apply gfRingEquiv.injective
  rw [map_one, gfRingEquiv_ofU16, phi_one]

/-! ### 3. The `Field` structure on `GF16`, CONDITIONAL on `[Fact (Irreducible POLY_poly)]`.

`AdjoinRoot POLY_poly` is a field exactly when `POLY_poly` is irreducible (the documented WALL,
`AdjoinRoot.instField`). Under that single premise (strictly weaker than the prior `hmul +
Irreducible`, since `hmul` is now discharged unconditionally) the bijection `gfEquiv` transfers
the field structure to `GF16`. The transported `Field`'s `+`/`*` are STILL the extracted
`gfAddV`/`gfMulV` (the `Field` extends the same `CommRing`), so this is a genuine `Field` on the
extracted arithmetic — not an axiom, not circular (the field-ness comes from `AdjoinRoot`). -/

/-- **The GF(2¹⁶) field structure on `GF16`** (CONDITIONAL on `Irreducible POLY_poly`). The
extracted field arithmetic `(gfAddV, gfMulV)` is a field, isomorphic to the genuine quotient
field `(ZMod 2)[X]/(POLY)`. The only open premise is irreducibility (satisfiable), carried as a
`Fact` — never an axiom. -/
noncomputable def fieldOfIrreducible [Fact (Irreducible POLY_poly)] : Field GF16 :=
  gfEquiv.field

/-- The conditional field structure extends the SAME unconditional `CommRing` (its `+`/`*` are
the extracted `gfAddV`/`gfMulV`): the field iso `gfEquiv.field`'s `toCommRing` is defeq to the
banked `CommRing GF16`. Recorded so a future Lagrange bridge can use the field with the extracted
operations preserved. -/
theorem fieldOfIrreducible_toCommRing [Fact (Irreducible POLY_poly)] :
    (fieldOfIrreducible).toCommRing = (inferInstance : CommRing GF16) := rfl

end Spqr.Gf16FieldInstance
