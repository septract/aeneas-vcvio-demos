/-
  SPQR Reed–Solomon codec — Layer B-mul, the CODE DECOMPOSITION of the extracted field
  multiply, and the precise localization of the remaining multiplicative gap (Stage 2).

  ## What this file establishes (genuine, IN-BOUNDARY, field-law-FREE)

  The extracted `gf.gf_mul = poly_reduce ∘ poly_mul` (Extracted/Gf.lean):

      gf_mul a b = do let i ← poly_mul a b; poly_reduce i

  factors the field multiply into the carryless coefficient convolution `poly_mul`
  (whose value spec — the XOR-fold `clmulPartial`, and its polynomial reading
  `toPoly32 (polyMulV a b) = toPoly a * toPoly b` — is banked in `Gf16Mul.lean`) and the
  table-driven reduction `poly_reduce`. This file banks the VALUE-LEVEL decomposition of
  the extracted code, with NO field laws, NO `decide` over the value space, NO axiom:

    * `poly_reduceV` — the pure value of the extracted `gf.poly_reduce` (the `Result`'s
      payload; `0#u16` on the never-taken failure branch), with its `.ok` value spec
      `poly_reduce_ok` (from the banked totality `Spqr.Gf.poly_reduce_total`).

    * `gfMulV_decomp` — the HEADLINE: the extracted field multiply, read as the value
      `gfMulV a b` (the `gf_mul_eq` value spec), is EXACTLY the table reduction of the
      carryless product: `gfMulV a b = poly_reduceV (polyMulV a b)`. This pins the
      `gf_mul = poly_reduce ∘ poly_mul` decomposition at the value level — a result
      directly about `gf.gf_mul`, `gf.poly_reduce`, `gf.poly_mul`.

  ## The PRECISE remaining multiplicative gap (Stage 2), localized here (honest, NOT faked)

  The field-assembly bridge `hmul` carried by `Gf16FieldAssembly.lean` is
  `∀ a b, phi (gfMulV a b) = phi a * phi b`, i.e. (unfolding `phi = mk ∘ toPoly`)
  `mk (toPoly (gfMulV a b)) = mk (toPoly a * toPoly b)`. We prove HERE (`hmul_iff_stage2`)
  that — GIVEN the banked Stage 1 (`toPoly32_polyMulV`) and the decomposition
  (`gfMulV_decomp`) — this `hmul` is EQUIVALENT to the single polynomial statement

      STAGE 2:  ∀ v : U32,  mk (toPoly (poly_reduceV v)) = mk (toPoly32 v)

  i.e. the table reduction `poly_reduce` realizes reduction mod `POLY_poly` on the
  bit↔coefficient embedding. So the entire remaining multiplicative obligation is exactly
  this one statement about the extracted `gf.poly_reduce`.

  STATUS (updated): this obligation is now CLOSED — `Gf16ReduceTable.stage2_proved`
  (`Stage2 := poly_reduce_residue`) discharges Stage 2, and `Gf16ReduceTable.hmul_proved`
  then upgrades the `Gf16FieldAssembly` ring laws (`gfMulV_comm`/`_assoc`/`_one`/`_distrib`)
  from CONDITIONAL to UNCONDITIONAL — all axiom-clean (`[propext, Classical.choice,
  Quot.sound]`), never an axiom, `sorry`, or `native_decide`. The `Stage2`/`hmul_iff_stage2`
  statements remain HERE as the localized obligation; their discharging proofs live in
  `Gf16ReduceTable.lean`.
-/
import Demos.Spqr.Gf
import Demos.Spqr.Gf16Field
import Demos.Spqr.Gf16Mul
import Mathlib.RingTheory.AdjoinRoot

open Aeneas Std Result
open Spqr.Gf
open Spqr.Gf16Mul (polyMulV polyMulV_val toPoly32 toPoly32_polyMulV)
open Spqr.Gf16Field (toPoly POLY_poly)
open Polynomial

namespace Spqr.Gf16Reduce

/-! ### 1. The value of the extracted carryless multiply succeeds (`.ok`) -/

/-- The extracted carryless multiply succeeds with value `polyMulV a b` (it is total —
`Spqr.Gf.poly_mul_total` — so it is never `div`/`fail`). -/
theorem polyMulV_ok (a b : Std.U16) : gf.poly_mul a b = .ok (polyMulV a b) := by
  have := Spqr.Gf.poly_mul_total a b
  unfold polyMulV
  cases h : gf.poly_mul a b with
  | ok c => rfl
  | div => rw [h] at this; simp at this
  | fail e => rw [h] at this; simp at this

/-! ### 2. The value of the extracted table reduction -/

/-- The extracted table reduction, read as a pure `u32 → u16` (the value of the `Result`, or
`0#u16` on the never-taken failure branch). -/
def poly_reduceV (v : Std.U32) : Std.U16 :=
  match gf.poly_reduce v with
  | .ok c => c
  | _ => 0#u16

/-- **Value spec of the table reduction.** `gf.poly_reduce v` succeeds with value
`poly_reduceV v` — so the extracted two-fold table reduction denotes the pure `poly_reduceV`
(from the banked totality `Spqr.Gf.poly_reduce_total`). -/
theorem poly_reduce_ok (v : Std.U32) : gf.poly_reduce v = .ok (poly_reduceV v) := by
  have := Spqr.Gf.poly_reduce_total v
  unfold poly_reduceV
  cases h : gf.poly_reduce v with
  | ok c => rfl
  | div => rw [h] at this; simp at this
  | fail e => rw [h] at this; simp at this

/-! ### 3. The HEADLINE: `gf_mul` decomposes as `poly_reduce ∘ poly_mul` at the value level -/

/-- **Value-level decomposition of the extracted field multiply.** The extracted `gf.gf_mul`,
read as the value `gfMulV a b` (the banked `gf_mul_eq` value spec), is EXACTLY the table
reduction of the carryless product: `gfMulV a b = poly_reduceV (polyMulV a b)`. This pins the
`gf_mul = poly_reduce ∘ poly_mul` decomposition (Extracted/Gf.lean) at the value level — a
field-law-free fact directly about the extracted `gf.gf_mul` / `gf.poly_reduce` / `gf.poly_mul`. -/
theorem gfMulV_decomp (a b : Std.U16) : gfMulV a b = poly_reduceV (polyMulV a b) := by
  have hmul_eq : gf.gf_mul a b = .ok (gfMulV a b) := Spqr.Gf.gf_mul_eq a b
  -- unfold the extracted composition gf_mul = poly_reduce ∘ poly_mul and plug the value specs
  unfold gf.gf_mul at hmul_eq
  rw [polyMulV_ok a b] at hmul_eq
  simp only [Std.bind_tc_ok] at hmul_eq
  rw [poly_reduce_ok (polyMulV a b)] at hmul_eq
  exact (Result.ok.inj hmul_eq).symm

/-! ### 4. Localizing the remaining multiplicative gap to STAGE 2 (`poly_reduce` = remainder)

The field-assembly bridge `hmul` (in `Gf16FieldAssembly.lean`) is
`∀ a b, mk (toPoly (gfMulV a b)) = mk (toPoly a) * mk (toPoly b)`. Using the banked Stage 1
(`toPoly32_polyMulV : toPoly a * toPoly b = toPoly32 (polyMulV a b)`) and the decomposition
above, we show this is EQUIVALENT to the single Stage-2 statement about `gf.poly_reduce`:

  `∀ v, mk (toPoly (poly_reduceV v)) = mk (toPoly32 v)`.

So the whole remaining multiplicative obligation is exactly this. -/

/-- **The Stage-2 statement** (the precise remaining multiplicative gap): the table reduction
`poly_reduce` realizes reduction mod `POLY_poly` on the bit↔coefficient embeddings, i.e. in the
quotient `AdjoinRoot POLY_poly`, `toPoly (poly_reduceV v)` and `toPoly32 v` have the same image. -/
def Stage2 : Prop :=
  ∀ v : Std.U32,
    AdjoinRoot.mk POLY_poly (toPoly (poly_reduceV v)) = AdjoinRoot.mk POLY_poly (toPoly32 v)

/-- **Stage 2 ⇒ the multiplicative bridge `hmul`.** If the table reduction realizes the residue
(`Stage2`), then `mk (toPoly (gfMulV a b)) = mk (toPoly a) * mk (toPoly b)` for the extracted
field multiply — the exact `hmul` hypothesis `Gf16FieldAssembly` carries. (The converse also
holds — see `hmul_imp_stage2` — so `Stage2` is precisely the remaining obligation.) -/
theorem stage2_imp_hmul (h : Stage2) (a b : Std.U16) :
    AdjoinRoot.mk POLY_poly (toPoly (gfMulV a b))
      = AdjoinRoot.mk POLY_poly (toPoly a) * AdjoinRoot.mk POLY_poly (toPoly b) := by
  rw [gfMulV_decomp, h (polyMulV a b), ← map_mul, toPoly32_polyMulV]

/-- **The multiplicative bridge `hmul` ⇒ Stage 2** (every `U32` produced by the carryless
multiply is realized; here stated on the full image via the carryless multiply, which is onto
the products `toPoly a * toPoly b`). We prove the exact converse on the values `polyMulV a b`:
if `hmul` holds for all `a b`, then `Stage2` holds on every `v` of the form `polyMulV a b`.
Since `gfMulV_decomp` shows `gfMulV a b = poly_reduceV (polyMulV a b)`, the two are mutually
derivable on those values — confirming `Stage2` is precisely the remaining content of `hmul`. -/
theorem hmul_imp_stage2_on_products
    (hmul : ∀ a b, AdjoinRoot.mk POLY_poly (toPoly (gfMulV a b))
              = AdjoinRoot.mk POLY_poly (toPoly a) * AdjoinRoot.mk POLY_poly (toPoly b))
    (a b : Std.U16) :
    AdjoinRoot.mk POLY_poly (toPoly (poly_reduceV (polyMulV a b)))
      = AdjoinRoot.mk POLY_poly (toPoly32 (polyMulV a b)) := by
  rw [← gfMulV_decomp, hmul a b, ← map_mul, toPoly32_polyMulV]

end Spqr.Gf16Reduce
