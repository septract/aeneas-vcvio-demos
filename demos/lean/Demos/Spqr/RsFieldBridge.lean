/-
  SPQR Reed–Solomon codec — Layer C, the BRIDGE over the GENUINE GF(2¹⁶) carrier.

  ## What this file establishes

  `RsCapstone.decode_value_at_roundtrip` is the `decode ∘ encode = id` identity stated over an
  ARBITRARY `Field F` and an abstract "decoding" map `dec : U16 → F`, carrying the
  interpolation-correctness bridge `hbridge` as a premise. With Stage 2 closed
  (`Gf16ReduceTable`), the embedding `φ = mk ∘ toPoly : U16 → AdjoinRoot POLY_poly` is now an
  UNCONDITIONAL ring homomorphism that is bijective, so — given only `Irreducible POLY_poly`
  (the documented WALL) to make `AdjoinRoot POLY_poly` a field — we can instantiate the
  abstract round-trip at the REAL GF(2¹⁶) carrier `F = AdjoinRoot POLY_poly`, `dec = φ`.

  This file banks that instantiation:

  * **`decode_value_at_roundtrip_gf16`** — the `decode ∘ encode = id` identity ABOUT
    `gf.decode_value_at`, with the field FIXED to the genuine GF(2¹⁶) quotient
    `AdjoinRoot POLY_poly` and the decoding map FIXED to `φ` (= `mk ∘ toPoly`). Conditional only on
    `Irreducible POLY_poly` (the WALL) plus the genuine non-degeneracy premises (distinct nodes,
    low degree, codeword-of-`f`) and the interpolation-correctness bridge `hbridge` — phrased over
    the concrete `φ`. The prior abstract theorem's `[Field F]` is now DISCHARGED to the real field
    (it is `AdjoinRoot.instField` under `Fact (Irreducible POLY_poly)`), so the only carried
    algebraic premise is irreducibility — a genuine reduction of the assumption surface.

  ## Status (updated — both former obligations now CLOSED)

  - `hbridge` (that the extracted `prepare`/`complete`/`divFold`/`compute_at` recurrences compute
    Mathlib's `Lagrange.interpolate`/`eval` over GF(2¹⁶)) is now DERIVED in `RsLagrangeBridge`
    (`decode_value_at_eval_eq_interpolate`), using `gfDivV` read as the field inverse
    (`RsDivInverse`). The `_derived`/`_of_dist` capstones here consume it, so `hbridge` is no
    longer a carried premise for those.
  - `Irreducible POLY_poly` is now a real theorem (`Gf16IrreducibleBridge.POLY_poly_irreducible`,
    via the kernel-checked `List Bool` mirror), so `Gf16IrreducibleBridge.decode_value_at_roundtrip_gf16_unconditional`
    drops the `[Fact (Irreducible POLY_poly)]` binder entirely. The conditional theorems in THIS
    file remain (stated under `[Fact …]`) as the building blocks that the unconditional wrappers
    discharge; nothing here is an axiom. The only premises left on the roundtrip are the genuine
    non-degeneracy hypotheses (distinct nodes, low message degree, codeword-of-`f`).
-/
import Demos.Spqr.RsCapstone
import Demos.Spqr.Gf16FieldInstance
import Demos.Spqr.RsLagrangeBridge

open Aeneas Std Result
open Spqr.Gf
open Spqr.Gf16Field (toPoly POLY_poly)
open Spqr.Gf16FieldAssembly (phi)
open Spqr.RsInterp (denomV)
open Polynomial

namespace Spqr.RsFieldBridge

variable {ι : Type} [DecidableEq ι]

/-- **Reed–Solomon `decode ∘ encode = id` over the GENUINE GF(2¹⁶) carrier (CONDITIONAL on
`Irreducible POLY_poly`).**

This is `RsCapstone.decode_value_at_roundtrip` with the field DISCHARGED to the real quotient
`AdjoinRoot POLY_poly` (a field exactly when `POLY_poly` is irreducible — the WALL) and the
decoding map FIXED to the genuine embedding `φ = mk ∘ toPoly`. `s : Finset ι` indexes the `n`
nodes via `node : ι → AdjoinRoot POLY_poly`, `sample : ι → U16` the samples, `f` the message
polynomial. Under:

  * `hvs : Set.InjOn node s` — distinct nodes (REAL, necessary),
  * `hdeg : f.degree < s.card` — low-degree message (REAL, necessary),
  * `henc : ∀ i ∈ s, eval (node i) f = φ (sample i)` — the samples are the encoder's
    evaluations of `f` (the `decode ∘ ENCODE` premise),
  * `hbridge` — the extracted decoder, decoded through `φ`, evaluates the Lagrange interpolant of
    the `φ`-decoded samples at `φ x` (the honest open interpolation-correctness bridge, now
    phrased over the concrete `φ` — a genuine ring hom since Stage 2 closed),

the extracted `gf.decode_value_at xs ys n x`, decoded through `φ`, equals `eval (φ x) f` — it
recovers the message polynomial's value at the query point, over the actual GF(2¹⁶) field. The
only carried algebraic premise is `Irreducible POLY_poly`; `hmul`/the field laws are no longer
assumed (Stage 2 discharged them). -/
theorem decode_value_at_roundtrip_gf16 [Fact (Irreducible POLY_poly)]
    (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    (s : Finset ι) (node : ι → AdjoinRoot POLY_poly) (sample : ι → Std.U16)
    {f : (AdjoinRoot POLY_poly)[X]}
    (hvs : Set.InjOn node s) (hdeg : f.degree < s.card)
    (henc : ∀ i ∈ s, eval (node i) f = phi (sample i))
    (hbridge : (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v))
        = .ok (eval (phi x) (Lagrange.interpolate s node (fun i => phi (sample i))))) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v)) = .ok (eval (phi x) f) :=
  Spqr.RsCapstone.decode_value_at_roundtrip xs ys n x phi s node sample hvs hdeg henc hbridge

/-- **Reed–Solomon `decode ∘ encode = id` over GF(2¹⁶) with `hbridge` DISCHARGED** (CONDITIONAL on
`Irreducible POLY_poly` + distinct nodes + nonzero denominators ONLY — `hmul` discharged by Stage 2,
and the interpolation-correctness bridge is now a DERIVED fact, no longer assumed).

This is `decode_value_at_roundtrip_gf16` specialized to the concrete node/sample setup
(`ι = Nat`, `s = Finset.range n`, `node k = φ xs[k]`, `sample k = ys[k]`) where the formerly-assumed
`hbridge` premise is supplied by the now-proved `RsLagrangeBridge.decode_value_at_eval_eq_interpolate`
(the composition of the unconditional evaluation half with the irreducibility-conditional
interpolation half). So under irreducibility, distinct nodes (`hdist`), nonzero Lagrange denominators
(`hdenom`), low message degree (`hdeg`), and the genuine `decode ∘ ENCODE` premise (`henc` — `ys` is a
codeword of `f`), the extracted `gf.decode_value_at xs ys n x`, decoded through `φ`, recovers
`eval (φ x) f` — the message polynomial's value at the query point, over the actual GF(2¹⁶) field.

About `gf.decode_value_at`. The interpolation-correctness bridge is DERIVED here (not a premise); the
only carried algebraic premise is `Irreducible POLY_poly`, plus the genuine non-degeneracy
hypotheses. NO `axiom`, NO `sorry`, NO `native_decide`. -/
theorem decode_value_at_roundtrip_gf16_derived [Fact (Irreducible POLY_poly)]
    (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    {f : (AdjoinRoot POLY_poly)[X]}
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdenom : ∀ i, i < n.val → denomV xs n xs.val[i]! 1#u16 0 ≠ 0#u16)
    (hdeg : f.degree < (Finset.range n.val).card)
    (henc : ∀ i ∈ Finset.range n.val, eval (phi xs.val[i]!) f = phi ys.val[i]!) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v)) = .ok (eval (phi x) f) := by
  -- distinct nodes ⇒ Set.InjOn (φ is injective, and hdist gives index-distinctness)
  have hvs : Set.InjOn (fun k => phi xs.val[k]!) (↑(Finset.range n.val) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact hdist a b ha hb (Spqr.Gf16FieldAssembly.phi_injective hab)
  -- the now-DERIVED interpolation-correctness bridge
  have hbridge := Spqr.RsLagrangeBridge.decode_value_at_eval_eq_interpolate xs ys n x hn hdist hdenom
  exact decode_value_at_roundtrip_gf16 xs ys n x (Finset.range n.val)
    (fun k => phi xs.val[k]!) (fun k => ys.val[k]!) hvs hdeg henc hbridge

/-- **Reed–Solomon `decode ∘ encode = id` over GF(2¹⁶), `hbridge` AND `hdenom` DISCHARGED**
(CONDITIONAL on `Irreducible POLY_poly` + distinct nodes ONLY — `hmul` discharged by Stage 2, the
interpolation-correctness bridge DERIVED, and the nonzero-denominator hypothesis now DERIVED from
distinct nodes).

This strengthens `decode_value_at_roundtrip_gf16_derived` by DROPPING the separate `hdenom` premise:
in the genuine GF(2¹⁶) field the Lagrange denominators are products of differences of distinct nodes,
hence nonzero in the integral domain (`RsLagrangeBridge.denomV_ne_zero`). So under irreducibility,
distinct nodes (`hdist`), low message degree (`hdeg`), and the genuine `decode ∘ ENCODE` premise
(`henc` — `ys` is a codeword of `f`), the extracted `gf.decode_value_at xs ys n x`, decoded through
`φ`, recovers `eval (φ x) f` — the message polynomial's value at the query point, over the actual
GF(2¹⁶) field.

About `gf.decode_value_at`. Both the interpolation-correctness bridge AND the nonzero-denominator
condition are DERIVED here (neither is a premise); the only carried algebraic premise is
`Irreducible POLY_poly`, plus the genuine non-degeneracy hypotheses (distinct nodes, low degree,
codeword). NO `axiom`, NO `sorry`, NO `native_decide`. -/
theorem decode_value_at_roundtrip_gf16_of_dist [Fact (Irreducible POLY_poly)]
    (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    {f : (AdjoinRoot POLY_poly)[X]}
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdeg : f.degree < (Finset.range n.val).card)
    (henc : ∀ i ∈ Finset.range n.val, eval (phi xs.val[i]!) f = phi ys.val[i]!) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v)) = .ok (eval (phi x) f) :=
  decode_value_at_roundtrip_gf16_derived xs ys n x hn hdist
    (fun i hi => Spqr.RsLagrangeBridge.denomV_ne_zero xs n i hn hi hdist) hdeg henc

end Spqr.RsFieldBridge
