# A protocol key-indistinguishability game over extracted code: what it takes, and two lessons

This note records what it took to state a *protocol-shaped* security game — a multi-session
key-indistinguishability (KI) game with the full Send / Reveal / Corrupt / Test oracle interface and
a cleanness predicate — over **Aeneas-extracted Rust**, in a VCVio-style framework, and to connect
its advantage to a primitive (KEM) security game by a machine-checked reduction. It is written to be
reusable beyond any single protocol target. It is the natural sequel to
`2026-06-07_composing-component-reductions-plan.md` (the Tier F / Tier C / Tier P taxonomy): this is
a worked Tier-P artifact, and the two lessons below are about the *gap between* a Tier-P game and its
reduction — exactly where that note predicted the work would be.

Created 2026-06-08. All claims correspond to machine-checked, axiom-clean theorems
(`[propext, Classical.choice, Quot.sound]`) over extracted code.

## TL;DR

1. **The expressibility is real and not the hard part.** A multi-session KI game over extracted
   primitive ops — mutable session table, adaptive oracle interface, a non-constant freshness
   predicate, a real-or-random `Test` — elaborates and runs in the framework. So does a faithful
   AKE *cleanness-under-corruption* predicate (long-term-key `Corrupt` + partner-awareness),
   transcribed from a published definition.
2. **The hard part is connecting the running game to its reduction**, and it has two distinct
   sub-difficulties, each of which produced a concrete lesson here:
   - **(Lesson A — the running-game↔reduction seam.)** A hybrid bound that decomposes the running
     game into per-session hops, and a separate single-session reduction to the primitive, can both
     be sound while *nothing connects them* — the per-hop terms' primitive meaning is only asserted
     in prose. Closing that seam (even for a restricted distinguisher class) is pure in-boundary
     proof engineering and converts "asserted" into "machine-checked."
   - **(Lesson B — the freshness predicate's evaluation point.)** A cleanness predicate can be
     correct clause-by-clause and still be wired in at the wrong *time*. Evaluated at `Test` time
     (rather than over the whole transcript) it admits compromise-*after*-test attacks that win with
     no assumption at all — silently making the game unbounded. The bug is *when* the predicate is
     consulted, not *what* it says.

---

## 1. What "a protocol game over extracted code" concretely requires

Stating the game needs four things, all of which the framework supported:

- **A primitive instance over the extracted ops.** The extracted functions (`keygen`/`encaps`/
  `decaps`-style byte transforms) are wrapped as a primitive scheme; functional adequacy
  (totality, Result→pure, the decaps∘encaps correctness round-trip) and any structural fact the
  reduction needs (here: the session-key derivation is *injective*, so it is entropy-preserving) are
  proved as Tier-F lemmas first.
- **A mutable game state + an adaptive oracle handler.** A session table that `Send` appends to and
  `Reveal`/`Corrupt`/`Test` read and mutate, expressed as a stateful query handler over the
  framework's `StateT`-of-oracle-computation substrate.
- **A non-trivial freshness/cleanness predicate.** Proved non-trivial on *both* sides: some clean
  `Test` session can exist (anti-vacuity), *and* the trivial attacks (reveal-self, reveal-partner,
  corrupt-peer, double-test) are excluded. A predicate that is too strong (no session ever clean) is
  as useless as one too weak (a trivial win) — both must be ruled out by theorems, not by inspection.
- **An advantage object** (real-or-random `Test` bias) and a reduction relating it to a primitive
  game's advantage.

The reduction's cleanest form is an **equality with zero slack**: when the session key is an
injective/bijective image of the primitive's challenge value, the KI advantage *equals* the
primitive advantage of an explicit reduction adversary (which embeds the primitive challenge through
that bijection). Equality is worth aiming for — it is simpler to prove than an inequality and leaves
no slack to misattribute.

## 2. Lesson A: the running-game↔reduction seam, and how to close it

A common shape: the multi-session running game is bounded by a **hybrid** — a telescoping sum over
per-session `Test`-swap hops — and, *separately*, a single-session **structural** game is reduced to
the primitive. The trap is that these are two disconnected developments. The hybrid's per-hop term is
a distinguishing advantage between counted handlers; the structural reduction is about a two-phase
adversary; and the only thing asserting "each hop is the primitive advantage" is a docstring. The
soundness gate stays green because every individual theorem is true — but the game is not actually
reduced to the primitive.

**How to close it (the tractable fragment first).** The running-game adversary is typically a
*query-driven* program (it can only interact through the oracle interface, not sample its own coins).
So the canonical single-session distinguisher is concrete and short: `Send; Test; output D(challenge)`
for a decision function `D`. One can then prove, by *evaluating that program through the handler*
(unfolding the oracle-simulation fold over the two queries, then the stateful-run plumbing), that the
**running game on this distinguisher equals the structural single-session game** — hence, by the
existing structural reduction, equals the primitive advantage. This closes the seam for the canonical
distinguisher class with zero slack: the running protocol game is machine-checked to *be* the
primitive reduction, not merely bounded by a term whose meaning is asserted.

The fully adaptive, multi-`Test` "guess-the-session" reduction (a factor-Q hybrid that guesses which
session is tested and embeds the challenge there) is genuinely heavier and can be left as a documented
next step. The point of the canonical bridge is that it converts the *prose assertion* into a
*theorem* at the load-bearing place, cheaply.

**Mechanical tells and tactics.** The evaluation is fiddly but mechanical: lemmas that turn
`bind`-of-`pure` into a `<$>` map will *block* the simulation fold (the map hides the bind the fold
needs) — keep the computation in bind-form. Evaluate the handler with the simulate-bind /
simulate-query / stateful-run-bind / stateful-run-pure lemmas, reduce the freshness gate to `true`
on a just-opened session, and the two sides converge to the *same* `do`-block; a final `rfl` bridges
the residual notation difference between the two evaluation-semantics spellings.

## 3. Lesson B: the freshness predicate's evaluation point is load-bearing

The deepest finding came from *working the reduction by hand*. The cleanness predicate was correct —
its clauses excluded reveal-self, reveal-partner, corrupt-peer, double-test — but it was consulted
**at `Test` time only**. With dynamic `Corrupt`/`Reveal` oracles, that admits a trace that is clean
*at the moment of `Test`* and compromised *afterwards*:

```
Send          ↦ open a session to the peer (the ciphertext/sid is returned)
Test          ↦ clean right now ⇒ the real-or-random challenge is handed out
Corrupt peer  ↦ NOW corrupt the peer's long-term key
output (challenge == recompute-the-real-key-from-the-corrupted-secret)
```

By the primitive's *correctness* (decapsulation recovers the key), the recomputation succeeds, so the
distinguisher wins with advantage ≈ 1 **independent of any hardness assumption**. No bound of the form
`advantage ≤ f(primitive advantage)` is provable for such a game. The predicate's clauses were right;
the bug was *when* it was evaluated.

**The fix is the standard convention, and it is worth stating explicitly:** real AKE/secure-messaging
definitions evaluate freshness over the **whole transcript** — the test session must still be fresh
when the adversary halts (textbook AKE games require it; the published PQXDH/ratchet `clean` predicates
are conditions on the complete experiment). Concretely: score the guess only if the *final* state is
clean (every tested session still fresh), otherwise return a coin (zero bias). With that, the
compromise-after-test traces contribute nothing, and both-sided non-triviality is re-established at the
end-of-game evaluation point (the exclusion is generic; a tested-and-still-fresh trace still scores).

**Why this generalizes.** Any freshness/cleanness predicate has both a set of clauses *and* an
evaluation point, and the evaluation point is as load-bearing as the clauses. When transcribing a
published game, check *when* the source evaluates freshness (almost always end-of-game / whole-trace),
not only *what* the clauses are. A synthetic rehearsal is the cheapest place to discover this — far
cheaper than discovering it mid-proof on the real target.

## 4. Honest-scope discipline for synthetic rehearsals

A synthetic instance (deliberately weak primitive, uninstantiated hardness assumption) is the right
vehicle for derisking *expressibility and reduction structure* — but the writeup must say so loudly,
or it reads as a security claim it is not:

- The primitive assumption is **uninstantiated**; no concrete (e.g. byte-level) security is certified.
  The value is the *composition capability* and the *transcribed game structure*, machine-checked.
- Any structural shortcut in the synthetic instance (a secret that is a public function of the public
  key, say) must be surfaced as load-bearing and explained — including *why* it does not invalidate
  the reduction (e.g. the reduction never needs that secret) and *why* it nonetheless certifies no
  security.
- Scope limits that come from the synthetic model (no real time ⇒ a corruption *window* degenerates to
  "ever corrupted") are stated as scope limits, not silently elided: the static + perfect-forward-
  secrecy fragment is modeled; window/KCI variants are named as not-claimed.

## 5. The resulting checklist

When standing up a protocol game over extracted code:

1. Prove the Tier-F adequacy + the structural fact the reduction needs (often: the key-derivation is
   injective / a bijection). Without it, the reduction has no slack-free form — and a degenerate
   derivation can make the game *unbounded* (a different failure than Lesson B, but also fatal).
2. State the game; prove the freshness predicate non-trivial on **both** sides.
3. **Decide the freshness evaluation point deliberately** — whole-trace unless the source says
   otherwise — and prove the compromise-after-test class is excluded (Lesson B).
4. Reduce to the primitive with an **equality** where possible; for the running (adaptive) game,
   first close the **canonical single-session bridge** as a theorem (Lesson A), and document the
   adaptive guess-the-session reduction as the next step rather than asserting it.
5. State honest scope: uninstantiated assumption, any structural shortcut, any model-induced scope
   limit.

The recurring discipline, consistent with the companion planning note: **make the existing pieces
load-bearing for each other (close the seam) before adding new isolated work, and prefer discovering
the subtle failures — evaluation-point bugs, degenerate derivations — on a synthetic rehearsal where
they are cheap.**
