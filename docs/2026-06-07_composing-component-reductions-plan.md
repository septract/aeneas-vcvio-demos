# From component reductions to composed security results: a planning note

When a Lean/VCVio-style verification effort has accumulated a pile of *functional-correctness
lemmas* and *component-level reductions* (PRG, PRF/MAC, KEM/DEM, a hash-is-a-PRF cascade), the
natural next question is: **what does it take to turn that pile into a connected, protocol-level
security statement — and which of those moves are in-bounds vs. gated?** This note records a
structured answer, derived from a whole-corpus assessment (five parallel mapping passes + two
adversarial critiques). It is written to be reusable beyond any single protocol target.

Created 2026-06-07. All capability claims spot-checked against the in-tree VCV-io / FCF sources at
the cited `file:line`.

## TL;DR

The highest-leverage move is usually **not** building new infrastructure — it is **wiring the
towers you already built to each other**. A corpus can pass its soundness gate while quietly being
"a heap of lemmas that never compose": each reduction is real, but the *premise* of one is never
discharged by the *conclusion* of another. Finding and closing those un-wired seams is the cheapest
path to a composed result. Concretely, this assessment found:

1. **A disconnected seam is the top priority.** A keystream-PRG security tower carried its per-hop
   PRG premise as an *assumed hypothesis*, while a separate hash-is-a-PRF cascade proved exactly the
   bound that premise needs — and nothing connected them. Discharging that premise (the
   "floor→tower wire") is an ungated, in-boundary reduction that converts a *conditional* result
   into a *connected* one. Highest value, medium effort, real provability risk.
2. **Protocol-level games are a transcription-and-sign-off task, not a research program** — *if and
   only if* the game is taken verbatim from a published, peer-reviewed source. Improvising one is
   out of bounds (see "The precedent boundary").
3. **Audit your framework's surface before porting.** Several "missing" capabilities turned out to
   already ship (a constructive hybrid; worked KEM games), and several "available" ports turned out
   to be redundant or to sit behind a `sorry`. Grep the *right* subtree, and `grep -n sorry` the
   thing you're about to build on.

---

## 1. A taxonomy: where results sit on the path to "security"

It helps to classify every theorem in a corpus into one of three tiers, because only the third is
"security" and the gap between tiers is where the work is:

- **Tier F — functional correctness / value-adequacy.** "This extracted function computes the
  spec" (totality, byte-layout, codec round-trip, a comparator's accept/reject). No adversary, no
  probability. The bulk of an early corpus.
- **Tier C — component reductions.** A real security experiment (`prgAdvantage`, MAC UF-CMA,
  KEM IND-CPA) bounded by the advantage of an explicit reduction — but against a *primitive*, with
  the protocol's adversary/freshness/session structure absent. These *are* security statements, but
  local ones.
- **Tier P — protocol games.** A game whose secret-vs-random challenge is the *protocol's* session
  key or message key, scored under a cleanness/freshness predicate over an adversary with the full
  oracle interface (Send / Corrupt / Reveal / Test). This is the goal.

The trap: a corpus can be rich in Tier F + Tier C and have **zero** Tier P, while *looking* close
because the Tier-C reductions mention the right primitives. The distance F+C → P is the real work,
and it splits into (a) **wiring** Tier-C results to each other (ungated), and (b) **stating +
discharging** a Tier-P game (gated).

## 2. The "un-wired seam" pathology, and how to find it

The single most valuable finding of the assessment was a seam: a security tower

```
keystream pseudorandom  ⇐  Σ over hops of  (per-hop block is a PRG)   ← assumed premise `hbound`
```

sat directly above a separately-proved

```
hash-cascade is a PRF  ≤  q · (compression-PRF advantage)            ← a real reduction
```

and **nothing connected `hbound` to the cascade bound**. Both towers were sound; neither made the
other load-bearing. The wire — a reduction `per-hop block advantage ≤ cascade-PRF advantage` —
is pure in-boundary proof engineering (no new game), and it is the literal precondition for the
keystream result being a *connected* security statement rather than a conditional reduction.

**How to find these seams mechanically:** for each Tier-C theorem, look at its *hypotheses* (not
its conclusion). A hypothesis of the form "X is a secure {PRG,PRF,...}" is a candidate seam if some
*other* theorem in the corpus concludes a bound on exactly that `X`. A literal grep for the premise
symbol against the candidate-discharging module (here: the per-hop generator name against the
cascade module) returning **empty** is the tell: the wire is absent. We verified the seam this
way (empty grep), then verified the discharging bound exists.

**Caveat that recurs:** finding a seam is cheap; *closing* it can still be hard. Here the per-hop
generator is HKDF-over-a-counter and the cascade lemma is fixed-length cascade-PRF — the
input-shape match is *plausible but unproven* and may hit the same length/almost-universality issues
the cascade work already flagged. So the honest plan is: **probe the shape-match first**; if it
walls, land a *named-premise skeleton* (the wire as a lemma carrying the residual coupling
hypothesis) and say so. That is still a strictly better artifact than two disconnected towers.

## 3. The precedent boundary: transcribe, don't improvise

The decisive rule for Tier-P work: **a security game may be introduced only by verbatim
transcription of a published, peer-reviewed definition** (cite figure/definition/page), or with a
cryptographer's sign-off. Improvising a game — even a plausible-looking one — and then building
infrastructure on it is forbidden, because the whole value proposition is "machine-checked *that the
right thing holds*," and a self-invented game silently moves the goalposts.

This makes a clean **"land the type / prove the bound" split**:

- **Stating the game as a Lean type** (the oracle set, the `Test` challenge, the cleanness predicate
  as a checked `Prop`) is a *transcription* task. In-bounds for a published game; the gate is a
  review pass ("does this type match Figure N?"), not a research program — so it can run
  *concurrently* with other work rather than blocking behind it.
- **Proving the advantage bound** is the heavy, often partly-gated part, and may be blocked
  independently (e.g. by a missing hardness assumption — see §5).

A practical warning the assessment surfaced: even "just transcribe the type" has a **multi-trap
surface** — a cleanness predicate with an honest-key-generation conjunct that's easy to drop, an
order-sensitive acceptance flag, an off-by-one in an epoch index, classical-RO vs QROM. Sign-off is
"check the figure," but the figure has several places to get it subtly wrong. Budget for that.

## 4. Audit the framework surface before you build or port

Two concrete process lessons, each of which changed a ranking in the assessment:

- **"Missing" infrastructure often already ships.** A capability we were about to build (a
  *constructive* per-query hybrid) turned out to exist in the framework already
  (`AsymmEncAlg/INDCPA/GenericLift.lean:89-151`, the `firstn i ++ skipn i` switching oracle with
  worked counter-monotonicity proofs); only a *generic* (primitive-agnostic) version was missing.
  Always inventory before porting. (Conversely, the *generic* `OracleHybrid` analog genuinely *was*
  missing and was worth building — the point is to know which.)
- **"Available" ports / modules are often redundant or unsound to build on.** Before depending on a
  framework module, `grep -n sorry` it. In this assessment, the Fujisaki–Okamoto transforms carry
  live `sorry`s (`Composed.lean:146`, `TTransform.lean:347`, `UTransform.lean:551`) and the UC
  framework's central principle is an *assumed* typeclass (`Standard.lean:218`
  `class HasDummyAdversaryFactor`) — so neither is a sound foundation for a security claim today.
  And several cross-framework port candidates (ElGamal, generic encryption) merely duplicate what
  the target framework already ships.

**Cross-framework ports (e.g. from a Coq library the target framework is modeled on):** they
strengthen the *floor* (primitive-level reductions like hash-is-a-PRF), never the protocol layer —
a library with only a DDH assumption has no AKE/channel game to give you. Port a result only when
(i) the target framework lacks it, (ii) the goal needs it, and (iii) the construction maps to the
target's idioms (watch the impedance: `Comp`/`Pr[]`/`EqDec` ↔ `OracleComp`/`SPMF`/`DecidableEq`+
`Fintype` is real and unpriced; some helper combinators have no analogue). One such port (a generic
query hybrid) transferred cleanly here; most candidates did not clear all three bars.

## 5. Naming the ceiling honestly

A comprehensive-as-the-framework-allows plan must state what it *cannot* reach, so the corpus is
never read as claiming more than it proves:

- **A hardness assumption the framework doesn't define is a hard stop.** A classical bound needing
  Gap-DH is blocked because only DLog/CDH/DDH ship (`HardnessAssumptions/DiffieHellman.lean`); no
  GDH. Either add the assumption (and own it as a new floor) or drop that bound.
- **Model mismatches must not be mislabeled.** A classical-random-oracle proof must not be sold as a
  post-quantum (QROM) guarantee; honest scope stops at "the KEM-IND-CCA hop is discharged; QROM is a
  named open infra gap."
- **Composition results that no source proves are improvisation.** If neither published source
  proves the handshake→channel composition, it is gated; defer it until both component games exist.
- **An accepted external trust gap stays accepted.** Whatever cannot be brought into the verified
  boundary by the toolchain (here: certain code the extractor can't ingest) is documented as a
  fixed limitation and excluded from the roadmap, not silently glossed.

## 6. The resulting priority shape (generic form)

1. **Wire the existing towers (ungated, highest leverage).** Discharge a Tier-C result's assumed
   premise against another Tier-C result's conclusion. Probe the shape-match first; skeleton-fallback
   if it walls. *This is usually the cheapest path to a genuinely composed result.*
2. **Transcribe the published protocol game(s) as types (gated on sign-off, runs concurrently).**
   The coverage pivot — turns correctness + component reductions into discharged floors of an
   advantage object. The bound may be blocked independently; landing the *type* still has value.
3. **Deepen / port floor reductions** only where a wired tower will consume them (otherwise it's a
   disconnected lemma — the §2 pathology).
4. **Generalize framework infrastructure** (e.g. a generic hybrid) only when a concrete consumer
   needs the generic form; prefer reusing the framework's existing concrete pattern in place.

The recurring discipline across all four: **prefer the move that makes existing work load-bearing
over the move that adds new isolated work**, and **verify the framework surface (`sorry`-freedom,
what already ships) before depending on it.**

---

## Appendix — verification status of this note

Capability claims were spot-checked against source this pass (verbatim): the constructive IND-CPA
hybrid (`AsymmEncAlg/INDCPA/GenericLift.lean`), the FO `sorry`s and the UC assumed typeclass, the
absence of GDH (`HardnessAssumptions/DiffieHellman.lean`), and the un-wired seam (empty grep from the
per-hop generator to the cascade module, plus the discharging bound's existence). **Not** verified
this pass: the provability of the wire's underlying shape-match (confirmed absent, not confirmed
provable); verbatim faithfulness of the published game figures (a sign-off must check the PDFs
directly); end-to-end `sorry`-freedom of every cited framework module beyond the lines quoted.
