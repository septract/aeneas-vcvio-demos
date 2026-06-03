/-
  SPQR Reed–Solomon codec — Layer A: the abstract `decode ∘ encode = id` backbone.

  This file isolates the *field-generic* mathematical content of the Reed–Solomon
  round-trip identity that SPQR's decoder relies on, over an **arbitrary** `Field F`.
  It says nothing about the extracted `gf.*` code — it is a BUILDING BLOCK, not a
  headline about the codec, and is deliberately NOT registered in `Audit.lean`. Its
  job is to package Mathlib's `Lagrange.interpolate` round-trip in exactly the shape
  the concrete codec bridge will consume once the GF(2¹⁶) field instance lands.

  ## The statement

  Reed–Solomon encoding evaluates a message polynomial `P` (degree `< n`) at `n`
  distinct nodes `v i` (`i ∈ s`, `s.card = n`), producing the codeword `r i = eval (v i) P`.
  Decoding Lagrange-interpolates the polynomial back from those `n` points and
  re-evaluates it at any index `x`. The round-trip identity is that this recovers
  the original evaluation:

      eval x (interpolate s v r) = eval x P   for all x,

  given (i) the nodes are DISTINCT on `s` (`Set.InjOn v s`), (ii) `P` has low degree
  (`P.degree < s.card`), and (iii) `r` agrees with `P` at the nodes. Both non-degeneracy
  hypotheses are essential and are kept REAL here — dropping distinctness or the
  degree bound makes interpolation fail to recover `P`.

  The proof is a thin wrapper over Mathlib's
  `Lagrange.eq_interpolate_of_eval_eq` (which gives `P = interpolate s v r` under
  exactly these hypotheses).

  ## Why this is a building block, not a codec headline

  Per the task boundary, a HEADLINE must be ABOUT the extracted `gf.*` functions.
  The lemmas below quantify over an arbitrary `[Field F]` and mention no `gf.*`
  symbol, so they are explicitly building blocks. The concrete decode∘encode=id
  about `gf.decode_value_at` additionally needs (B) that the extracted
  `gfMulV`/`gfAddV` form a field isomorphic to GF(2¹⁶) — irreducibility of
  `POLY = x¹⁶+x¹²+x³+x+1` over `ZMod 2` plus the clmul/reduce characterization —
  and (C) that the decoder loops compute Mathlib's `interpolate`/`eval` over that
  field. (B) is the deep open obligation; this file closes (A) cleanly.
-/
import Mathlib.LinearAlgebra.Lagrange

open Polynomial

namespace Spqr.RsAbstract

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- **Abstract decoder recovers the message polynomial (building block).**
Under distinct nodes (`Set.InjOn v s`), a low-degree message polynomial `f`
(`f.degree < s.card`), and a codeword `r` matching `f` at the nodes
(`∀ i ∈ s, eval (v i) f = r i`), the Lagrange interpolant of `r` IS `f`.

This is the algebraic heart of `decode ∘ encode = id`. It is field-generic and
mentions no `gf.*`, so it is a BUILDING BLOCK — not a codec headline. -/
theorem interpolate_eq_message (r : ι → F) {f : F[X]}
    (hvs : Set.InjOn v s) (hdeg : f.degree < s.card)
    (heval : ∀ i ∈ s, eval (v i) f = r i) :
    Lagrange.interpolate s v r = f :=
  (Lagrange.eq_interpolate_of_eval_eq r hvs hdeg heval).symm

/-- **Abstract `decode ∘ encode = id` (building block).** Re-evaluating the decoded
(interpolated) polynomial at any index `x` recovers the original evaluation
`eval x f`. This is the field-generic round-trip identity, stated over an arbitrary
`Field F`; it mentions no `gf.*` and is therefore a BUILDING BLOCK, not a headline.

The two non-degeneracy hypotheses are REAL and necessary: `hvs` (distinct nodes)
and `hdeg` (degree `< s.card`). Dropping either breaks recovery. -/
theorem decode_eq_eval (r : ι → F) {f : F[X]} (x : F)
    (hvs : Set.InjOn v s) (hdeg : f.degree < s.card)
    (heval : ∀ i ∈ s, eval (v i) f = r i) :
    eval x (Lagrange.interpolate s v r) = eval x f := by
  rw [interpolate_eq_message r hvs hdeg heval]

/-- Specialization: if the codeword is literally the evaluation of `f` at every node
(the encoder's defining equation, no separate `r`), decoding then re-evaluating
returns the original evaluation. Still a building block (arbitrary `Field F`). -/
theorem decode_encode_eq (x : F) {f : F[X]}
    (hvs : Set.InjOn v s) (hdeg : f.degree < s.card) :
    eval x (Lagrange.interpolate s v (fun i => eval (v i) f)) = eval x f :=
  decode_eq_eval (fun i => eval (v i) f) x hvs hdeg (fun _ _ => rfl)

/-- The decoded polynomial also reproduces the codeword exactly at each node — the
"interpolation passes through the points" property, the other half of round-trip
correctness. Re-exported from `Lagrange.eval_interpolate_at_node`. Building block. -/
theorem decode_at_node (r : ι → F) {i : ι}
    (hvs : Set.InjOn v s) (hi : i ∈ s) :
    eval (v i) (Lagrange.interpolate s v r) = r i :=
  Lagrange.eval_interpolate_at_node r hvs hi

end Spqr.RsAbstract
