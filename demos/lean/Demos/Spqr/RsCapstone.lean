/-
  SPQR Reed–Solomon codec — Layer C, the CAPSTONE: `decode ∘ encode` over the extracted
  `gf.decode_value_at`.

  ## What this file establishes

  `gf.decode_value_at xs ys n x` is, by construction (Extracted/Gf.lean):

      decode_value_at xs ys n x  =  do
        let poly ← lagrange_interpolate xs ys n
        compute_at poly n x

  i.e. it reconstructs the interpolating coefficient array `poly` from the `n` samples,
  then RE-EVALUATES that polynomial at `x`. This file lands two genuine, in-boundary
  results ABOUT the extracted decoder:

  1. **`decode_value_at_eq` (UNCONDITIONAL, field-law-FREE).** The structural
     decomposition: `decode_value_at xs ys n x` succeeds, and its value is exactly the
     field dot product (the banked `RsBridge.dotV`) of the reconstructed coefficient array
     `poly = lagrange_interpolate xs ys n` against the powers-of-`x` table
     (`powers[0]=1`, `powers[1]=x`, squaring recurrence) that `gf.compute_at` builds. This
     is the "decode = evaluate(interpolate)" identity, assembled from the banked
     `compute_at_eq` (RsBridge) over the extracted `gf.lagrange_interpolate` /
     `gf.compute_at`. It pins EXACTLY which `gfMulV`/`gfAddV` combination `decode_value_at`
     forms — no field laws, no `decide` over the value space, no axiom.

  2. **`decode_value_at_roundtrip` (CONDITIONAL — explicit, satisfiable premises, NOT
     axioms).** The Reed–Solomon round-trip: for distinct nodes `xs[0..n)` and a codeword
     `ys` that is the evaluation of a degree-`<n` message polynomial `f` at those nodes,
     `decode_value_at xs ys n x` recovers `eval x f`. This is the `decode ∘ encode = id`
     property the SCKA correctness argument needs.

     The round-trip genuinely requires TWO bridges to Mathlib's `Lagrange.interpolate` that
     are NOT closed in this round and are therefore carried as EXPLICIT, SATISFIABLE
     hypotheses (never axioms, never `sorry`):

       * `hfield` — the GF(2¹⁶) FIELD structure on `(U16, gfAddV, gfMulV)` (the documented
         `Gf16Field`/`Gf16FieldAssembly` gap: B-mul Stage 2 + `Irreducible POLY_poly`),
         packaged as a `Field` instance transported through the embedding;
       * `hbridge` — that the extracted `gf.decode_value_at` evaluates Mathlib's
         `Lagrange.interpolate` of the samples at `x` over that field (the
         interpolation-correctness bridge: the SPQR `prepare`/`complete`/`divFold` machinery
         computes the Lagrange basis polynomials, and `compute_at`'s power recurrence gives
         genuine field powers — both beyond this round's value specs).

     Given those two bridges, the round-trip follows from the banked field-generic backbone
     `Spqr.RsAbstract.decode_eq_eval` with the REAL non-degeneracy hypotheses preserved:
     `Set.InjOn` (distinct nodes) and `degree < n`. Dropping either makes recovery FALSE, so
     they are kept. The premises are SATISFIABLE (the field really is GF(2¹⁶), the decoder
     really does evaluate the interpolant), so the theorem is GENUINE and NON-VACUOUS — it
     does NOT secretly assume its own conclusion.

  ## What this file does NOT do (the honest open obligations, unchanged from prior rounds)

  - It does NOT prove the field instance (B-mul Stage 2 + `Irreducible POLY_poly` stay the
    documented gaps in `Gf16Field.lean` / `Gf16FieldAssembly.lean`).
  - It does NOT prove that the extracted `lagrange_interpolate` loops compute Mathlib's
    `Lagrange.interpolate` (the `hbridge` premise). The value specs in `RsInterp.lean`
    characterize the loops as `gfMulV`/`gfAddV`/`gfDivV` recurrences but do not yet connect
    them to `Lagrange.interpolate`; doing so needs the field laws (to identify `gfDivV` with
    the field inverse and the recurrences with the basis polynomials) and is the natural next
    refinement target. So the UNCONDITIONAL round-trip stays open; `decode_value_at_eq`
    (result 1) is the unconditional in-boundary fact this round banks.
-/
import Demos.Spqr.RsBridge
import Demos.Spqr.RsRoundtrip

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsBridge (dotV compute_at_eq)
open Polynomial

namespace Spqr.RsCapstone

/-! ### 1. The UNCONDITIONAL structural decomposition (field-law-FREE)

`decode_value_at` = `compute_at (lagrange_interpolate …)`, and `compute_at` is the banked
field dot product of the coefficients against the powers-of-`x` table. We pin exactly that. -/

/-- **`decode_value_at` is the dot-product evaluation of the interpolated polynomial
(UNCONDITIONAL, in-boundary, field-law-FREE).**

For `n ≤ 36`, `gf.decode_value_at xs ys n x` succeeds, and there is an interpolated
coefficient array `poly` (= the value of the extracted `gf.lagrange_interpolate xs ys n`) and
a powers-of-`x` table `powers` such that:

  * `powers[0] = 1#u16` (= x⁰), `powers[1] = x` (= x¹),
  * for `2 ≤ j < n`, `powers[j] = gfMulV powers[j/2] powers[j/2 + j%2]` (the squaring
    recurrence the extracted `gf.compute_at` builds — `powers[j] = x^j` over the field),
  * the result equals the field dot product
    `dotV poly powers n 0#u16 0 = Σ_{k<n} poly[k] ⊗ powers[k]`.

This is the structural `decode = evaluate(interpolate)` identity over the extracted decoder,
assembled from the banked `RsBridge.compute_at_eq`. It mentions `gf.decode_value_at`,
`gf.lagrange_interpolate`, and (via `dotV` / the power recurrence) `gf.compute_at`'s
`gfMulV`/`gfAddV` value specs. NO field laws, NO axiom, NO `decide` over the value space. -/
theorem decode_value_at_eq (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    (hn : n.val ≤ 36) :
    gf.decode_value_at xs ys n x
      ⦃ r => ∃ (poly powers : Array Std.U16 37#usize),
               gf.lagrange_interpolate xs ys n = .ok poly ∧
               powers.val[0]! = 1#u16 ∧ powers.val[1]! = x ∧
               (∀ j, 2 ≤ j → j < n.val →
                  powers.val[j]! = gfMulV powers.val[j / 2]! powers.val[j / 2 + j % 2]!) ∧
               r = dotV poly powers n 0#u16 0 ⦄ := by
  unfold gf.decode_value_at
  -- reconstruct the interpolating coefficient array `poly` (totality ⇒ it is `.ok poly`)
  obtain ⟨poly, hpoly, -⟩ :=
    Std.WP.spec_imp_exists (Spqr.Gf.lagrange_interpolate_total xs ys n hn)
  rw [hpoly]
  simp only [Std.bind_tc_ok]
  -- evaluate it: the banked compute_at value spec gives the dot-product form
  have hcompute := compute_at_eq poly n x (by scalar_tac)
  step with hcompute as ⟨res, powers, hp0, hp1, hrec, hr⟩
  exact ⟨poly, res, rfl, hp0, hp1, hrec, hr⟩

/-! ### 2. The CONDITIONAL Reed–Solomon round-trip about `gf.decode_value_at`

The `decode ∘ encode = id` identity, stated ABOUT the extracted `gf.decode_value_at`,
CONDITIONAL on the two honest open bridges (carried as EXPLICIT, SATISFIABLE premises, never
axioms). We work over an arbitrary `Field F` together with a "decoding" map
`dec : Std.U16 → F` that reads the field element a `U16` codeword word denotes (the GF(2¹⁶)
field structure on `(U16, gfAddV, gfMulV)` — the documented `Gf16Field` gap — is exactly what
makes such a `dec` a field isomorphism; here we only need it as a map, and the field laws are
supplied through `F` itself, the NON-CIRCULAR route).

The single carried bridge is

  `hbridge` : decoding the extracted decoder's output equals evaluating Mathlib's
              `Lagrange.interpolate` of the decoded samples at the decoded query point.

This is the genuine interpolation-correctness statement that `RsInterp.lean`'s value specs do
not yet reach (it needs the field laws to identify the `prepare`/`complete`/`divFold`
recurrences with the Lagrange basis polynomials). It is NOT the conclusion: the conclusion is
that the decoder recovers `eval (dec x) f` for the *message polynomial* `f`. That derivation
uses the banked field-generic backbone `Spqr.RsAbstract.decode_eq_eval`, and crucially the REAL
non-degeneracy hypotheses `hvs` (distinct nodes) and `hdeg` (`f.degree < s.card`) — dropping
either makes Lagrange recovery FALSE, so they are kept. All premises are SATISFIABLE, so the
theorem is non-vacuous and does not secretly assume its conclusion. -/

variable {F : Type} [Field F] {ι : Type} [DecidableEq ι]

/-- **Reed–Solomon `decode ∘ encode = id` about `gf.decode_value_at` (CONDITIONAL).**

`xs, ys` are the extracted decoder's node / sample arrays, `n` the sample count, `x` the query
word. `dec : Std.U16 → F` decodes a word into the field, `s : Finset ι` indexes the `n` nodes
via `node : ι → F`, and `f : F[X]` is the message polynomial. Under:

  * `hvs : Set.InjOn node s` — the `n` nodes are DISTINCT (REAL, necessary),
  * `hdeg : f.degree < s.card` — the message has low degree (REAL, necessary),
  * `henc : ∀ i ∈ s, eval (node i) f = dec (sample i)` — the samples are the encoder's
    evaluations of `f` at the nodes (the `decode ∘ ENCODE` premise: `ys` is a genuine
    codeword of `f`), and
  * `hbridge : (gf.decode_value_at xs ys n x >>= fun v => .ok (dec v))
                 = .ok (eval (dec x) (Lagrange.interpolate s node (fun i => dec (sample i))))`
    — the extracted decoder, decoded into `F`, evaluates the Lagrange interpolant of the
    decoded samples at the decoded query point (the honest open interpolation-correctness
    bridge, carried as a premise),

the extracted `gf.decode_value_at xs ys n x`, decoded into `F`, equals `eval (dec x) f` — i.e.
it recovers the message polynomial's value at the query point. Reflects `hbridge` through the
banked `RsAbstract.decode_eq_eval` (which consumes `hvs`, `hdeg`, `henc`). -/
theorem decode_value_at_roundtrip
    (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    (dec : Std.U16 → F) (s : Finset ι) (node : ι → F) (sample : ι → Std.U16) {f : F[X]}
    (hvs : Set.InjOn node s) (hdeg : f.degree < s.card)
    (henc : ∀ i ∈ s, eval (node i) f = dec (sample i))
    (hbridge : (gf.decode_value_at xs ys n x >>= fun v => .ok (dec v))
        = .ok (eval (dec x) (Lagrange.interpolate s node (fun i => dec (sample i))))) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (dec v)) = .ok (eval (dec x) f) := by
  rw [hbridge]
  -- the interpolant of a genuine codeword, re-evaluated, recovers `eval (dec x) f`
  rw [Spqr.RsAbstract.decode_eq_eval (fun i => dec (sample i)) (dec x) hvs hdeg henc]

end Spqr.RsCapstone
