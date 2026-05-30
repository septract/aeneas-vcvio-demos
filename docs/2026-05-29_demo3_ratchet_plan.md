# Plan: Demo 3 — a symmetric KDF ratchet chain (protocol-flavored security)

Planning note for a third end-to-end demo. Demos 1–2 prove *node-level* properties
(one cryptographic operation, ε = 0 or a single reduction hop). Demo 3 should be the
first one with genuine **protocol shape**: state threaded across many steps, a
**multi-hop hybrid argument**, and the **Σε / poly-many-hops** soundness side condition
that the theory note keeps flagging as the thing that bites at protocol scale.

Created 2026-05-29.

> **Status (2026-05-29): implemented and `make verify`-green.** Built as planned:
> `demos/rust/ratchet.rs` (`ratchet_split`), `Demos/Ratchet/Step.lean` (loop-invariant value
> adequacy), `Demos/Ratchet/Chain.lean` (the PRG-hybrid chain). Headline theorems
> `RatchetSecurity.ratchet_advantage_le_sum` (telescoping `Σε` bound) and
> `ratchet_secure_asymptotic` (poly-length ⇒ negligible, via `negligible_polynomial_mul`), plus
> `ratchet.ratchet_split_spec`, all depend only on `[propext, Classical.choice, Quot.sound]`.
> Two deviations from the sketch below, both simplifications: (i) bijectivity of the split is
> proven via an explicit `concat` inverse + surjectivity rather than a cardinality argument
> (the `Std.Array`/`List.Vector`/`usize` defeq made `Fintype.card` blow the recursion stack);
> (ii) the hybrid is indexed by a length-recursive `redStream` builder so the assembled vector
> never needs a length cast, and the crux hop (`glue`) is proven at the `probOutput` level using
> `probOutput_bind_bijective_uniform_cross` (split-pushforward) + `probOutput_bind_bind_swap`
> (commute the independent draws), inducting on the length with the continuation generalized.

Companions: [rough theory](2026-05-29_rough_theory.md) (esp. §3, §5 "poly-many hops"),
[the missing remainder](2026-05-29_briefing_missing-remainder.md) (the three-part
decomposition this demo is built to illustrate), [Aeneas→VCVio](2026-05-29_briefing_aeneas-to-vcvio.md).

================================================================================

## 1. Why this construction

The goal stated by the user: prove something with **some of the same complexities as a
real protocol** (libsignal), **without the scale** — and it *must* use Aeneas / Lean / VCVio.

Signal's **symmetric-key ratchet** (the KDF chain inside the Double Ratchet) is the
smallest real protocol fragment that has the complexities we're missing:

```
        ck₀ ──step──▶ ck₁ ──step──▶ ck₂ ──step──▶ ck₃ ...
         │             │             │
         ▼             ▼             ▼
        mk₀           mk₁           mk₂          (message keys, the protocol output)
```

Each `step` takes a chain key and deterministically derives **(next chain key, message
key)**. Signal does this with HMAC/HKDF; abstractly the step is a **length-doubling PRG**
`G : Seed → Seed × Out`. Security property:

> The sequence of message keys `(mk₀, …, mk_{n-1})` produced from a uniformly random
> seed `ck₀` is **pseudorandom** — indistinguishable from `n` independent uniform keys.

This is exactly the property that makes a ratchet usable as a key schedule, and it is
proven by the **canonical hybrid argument**: walk `i = 0 … n`, replacing one PRG output
at a time with uniform; each hop is a single reduction to PRG security; the advantages
**telescope to `n · ε_PRG`**.

### What it exercises that demos 1–2 do not

| Complexity | Demo 1 (OTP) | Demo 2 (stream) | **Demo 3 (ratchet)** |
|---|---|---|---|
| Cryptographic node (Aeneas, ε=0) | ✓ xor | ✓ combine loop | ✓ ratchet split loop |
| A genuine reduction (ε>0) | — | ✓ (1 hop) | ✓ (**n hops**) |
| **State threaded across steps** (sequencing) | — | — | ✓ chain key |
| **Hybrid / multi-hop game-walk** | — | — | ✓ `H₀ … Hₙ` |
| **Σε advantage bound** | — | — | ✓ `≤ n · ε_PRG` |
| **poly-many-hops soundness side condition** | vacuous | vacuous | ✓ *the headline* |
| Forward secrecy (stretch) | — | — | ✓ (optional) |

The single most important new ingredient is the last row. rough_theory.md §3/§5 says a
security proof is a *path* whose theorem is `Σ εᵢ`, **sound iff the path is poly-long and
`Σ ε` is negligible** — and warns: *"If the chain length depends on a parameter (e.g. n
sessions / ratchet steps in Signal) you get n·ε — sound iff n = poly. A naive `==`-chain
conceals this; the graded relation forces you to discharge it."* Demo 3 makes that
discharge a literal, checked Lean step.

================================================================================

## 2. How it maps onto the three-part decomposition

The missing-remainder briefing splits a protocol proof into (1) primitive nodes, (2)
sequencing/orchestration, (3) network/trust/hardness. Demo 3 instantiates all three
*honestly and legibly* — and the Aeneas/VCVio split falls out of that decomposition:

- **(1) Node — lifted by Aeneas, ε = 0.** The deterministic per-step *glue*: split a PRG
  output block into `(next_chain_key, message_key)`. This is a fixed-size byte-array loop,
  squarely in Aeneas's subset (like `combine`). Value adequacy proven with a loop invariant.
- **(2) Sequencing — authored in the Lean model.** The chain recursion (thread `ck`,
  collect `mk`s over `n` steps) and the hybrid games. The briefing is explicit that
  sequencing is *pure-given-coins* and **not** liftable by Aeneas (pure-only); it is
  modeled and verified on the Lean side. Demo 3's chain loop living in Lean rather than in
  the extracted Rust is therefore the *correct, documented* trust boundary, not a shortcut.
- **(3) Hardness/trust — an explicit assumption.** "`G` is a secure PRG" and "the chain
  length `n` is polynomial in the security parameter." Both are named premises of the
  asymptotic theorem; neither is checkable against code (that's the point of §3).

So demo 3 is a worked, machine-checked illustration of the briefing's own taxonomy: the
certified part is (1)+(2)-on-the-model; (3) is a small, legible assumption budget.

================================================================================

## 3. The Rust to extract (`demos/rust/ratchet.rs`)

Keep the cryptographic hardness *out* of the extracted code (exactly as demo 2 keeps the
PRG abstract and only extracts the `combine` loop). The extracted Rust is **deterministic
plumbing**: split a 64-byte PRG output block into the next 32-byte chain key and a 32-byte
message key.

```rust
//! One symmetric-ratchet step's deterministic glue: split a 64-byte KDF/PRG output
//! block into the next 32-byte chain key and a 32-byte message key. The KDF/PRG itself
//! is modelled abstractly on the Lean side (its security is the hardness assumption);
//! this is the in-subset plumbing the proof treats as value-adequate. No unsafe/FFI/traits.

pub fn ratchet_split(block: [u8; 64]) -> ([u8; 32], [u8; 32]) {
    let mut ck = [0u8; 32];   // next chain key  = block[0..32]
    let mut mk = [0u8; 32];   // message key     = block[32..64]
    let mut i = 0;
    while i < 32 {
        ck[i] = block[i];
        mk[i] = block[32 + i];
        i += 1;
    }
    (ck, mk)
}
```

Why a loop and not a one-liner: it forces a genuine **loop-invariant value-adequacy proof**
(`Std.loop.spec_decr_nat`, as in `LoopCorrectness.lean`) — the extracted artifact is meaty,
not a `rfl`. The split is honest "just wiring": it is visibly *not* pretending to be the
KDF, so we are not smuggling the hardness assumption into extracted code.

**Value-adequacy lemma** (the ε=0 node link): `ratchet_split block = .ok (ck, mk)` with
`ck[j] = block[j]` and `mk[j] = block[32+j]` for `j < 32`, an equation in `Result`
(certifies no `fail`/`div`). Mirrors `stream.combine_spec`.

(If `[u8; 64]` proves awkward across the Charon/Aeneas array ABI, fall back to two inputs
or a single struct; the shape of the proof is identical.)

================================================================================

## 4. The Lean model (`demos/lean/Demos/Ratchet/`)

Proposed files (parallel to `Demos/StreamCipher/`):

- `Ratchet/Step.lean` — value adequacy of the extracted `ratchet_split` (loop invariant).
- `Ratchet/Chain.lean` — the abstract PRG, the chain recursion, the hybrid games, the
  telescoping advantage bound, and the asymptotic (poly-`n`) security theorem.

### 4.1 The abstract step and the chain

```lean
-- Block bridged so the extracted split applies (`Array U8 64`, or `BitVec 512`).
-- The length-doubling PRG is abstract; its security is the assumption.
structure RatchetPRG (Seed Out : Type) where
  gen : Seed → Block            -- one KDF/PRG block; `ratchet_split` carves (Seed', Out)

-- one step = abstract PRG then the *extracted* split (value adequacy collapses the Result)
def step (G : RatchetPRG Seed Out) (ck : Seed) : Seed × Out := ...   -- uses ratchet_split

-- the sequencing (part 2): thread the chain key, collect message keys
def keystream (G : RatchetPRG Seed Out) : (n : ℕ) → Seed → List.Vector Out n
  | 0,     _  => .nil
  | n+1, ck   => let (ck', mk) := step G ck;  mk ::ᵥ keystream G n ck'
```

This is structurally `streamOutputs` from VCVio's `Examples/PRGfromPRF.lean` — but our
step is a **PRG** (single value out), so security goes through the **PRG hybrid**, which
needs **no random-oracle collision argument**. (See §6: that is the whole reason we choose
the PRG hybrid over completing `PRGfromPRF.streamPRG`.)

### 4.2 The security game

Real: `keystream` from a uniform seed. Ideal: `n` independent uniform `Out` values.
Model both as a single `PRGScheme (Seed) (List.Vector Out n)` (output = the message-key
vector) and reuse VCVio's `PRGScheme.prgAdvantage`, exactly as demos 2a/2b do.

### 4.3 The hybrid argument (the core new work)

Define hybrid `Hᵢ` (for `i = 0 … n`): the **first `i` message keys are sampled uniformly**
and the chain is **re-seeded from a fresh uniform chain key** at position `i`, with the
remaining `n−i` keys produced by the real `step`/`G`. Then:

- `H₀` = real experiment (`keystream` from a uniform seed).
- `Hₙ` = ideal experiment (`n` independent uniform keys).
- **Adjacent hop `Hᵢ ~ Hᵢ₊₁`**: the only difference is whether the block at position `i`
  is `G(uniform seed)` or uniform. So `|Pr[Hᵢ] − Pr[Hᵢ₊₁]| = prgAdvantage G Rᵢ`, where the
  reduction `Rᵢ` is the explicit adversary that: samples the first `i` keys uniformly,
  receives the challenge block, `ratchet_split`s it, runs the honest chain on the resulting
  next-state for the remaining steps, and feeds the assembled vector to the distinguisher.
  (One PRG query, plus bookkeeping — "no heavier than `A`," same spirit as demo 2's reduction.)

- **Telescope** (triangle inequality on the real-valued advantages — elementary `abs_sub`,
  no special VCVio lemma needed, though `ProbComp.boolDistAdvantage_triangle` /
  `StateSeparating.advantage_triangle` exist if convenient):

  ```
  prgAdvantage (ratchetPRG G n) A  ≤  Σ_{i<n} prgAdvantage G (Rᵢ)  ≤  n · max_i prgAdvantage G (Rᵢ)
  ```

### 4.4 The headline theorems

1. **`ratchet_split_spec`** — value adequacy of the extracted loop (ε=0 node).
2. **`keystream_hybrid_advantage`** — the telescoping bound
   `prgAdvantage (ratchetPRG G n) A ≤ Σ_{i<n} prgAdvantage G (Rᵢ)`. The protocol-shape result.
3. **`ratchet_secure_asymptotic`** — *the headline.* Index `G`, the distinguisher, **and the
   chain length** by a security parameter `sp`, with `len : ℕ → ℕ` a **polynomial** chain
   length. If `G` is a secure PRG family (negligible advantage against each reduction), then
   the ratchet keystream family is pseudorandom:

   ```lean
   theorem ratchet_secure_asymptotic
       (hG  : negligible fun sp => ofReal (sup over i of (G sp).prgAdvantage (R sp i)))
       (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
       negligible fun sp => ofReal ((ratchetPRG (G sp) (len sp)).prgAdvantage (A sp)) := by
     -- bound by  len sp · ε(sp)  via keystream_hybrid_advantage, then:
     -- negligible_polynomial_mul  (n·negl is negligible for poly n)   ◀── the side condition
   ```

   The proof *consumes* `hlen` through `negligible_polynomial_mul` (or `negligible_sum` over
   `Finset.range (len sp)`). **Drop `hlen` and the proof does not close** — which is precisely
   the "sound iff n = poly" side condition made operational. That single dependency is the
   payload of the whole demo.

================================================================================

## 5. VCVio machinery to reuse (all confirmed present and proven)

- `PRGScheme`, `PRGAdversary`, `prgRealExp`/`prgIdealExp`/`prgAdvantage`
  (`VCVio/CryptoFoundations/PRG.lean`) — same surface demos 2a/2b already use.
- Negligible algebra (`VCVio/CryptoFoundations/Asymptotics/Negligible.lean`):
  - `negligible_sum` — finite sum of negligibles is negligible (the constant-`n` case).
  - `negligible_polynomial_mul` — *"key lemma for handling polynomial-loss security
    reductions"* (their words). This is exactly `n · ε` for polynomial `n`.
  - `negligible_pow_mul`, `negligible_const_mul`, `negligible_of_le`.
- Uniform-sampling probability lemmas already used in demos 2a/2b: `probOutput_bind_eq_tsum`,
  `probOutput_uniformSample`, `Equiv.tsum_eq` (for the base re-indexing).
- `List.Vector` `Fintype`/`SampleableType` plumbing for the output vector
  (`Mathlib.Data.Fintype.Vector`, as in `ByteArray.lean`).
- Optional, if we want the bound via library lemmas rather than by hand:
  `StateSeparating/Advantage.lean :: advantage_triangle` and
  `StateSeparating/Hybrid.lean :: advantage_hybrid` (telescoping over stateful handlers),
  and the asymptotic `Asymptotics/Security.lean :: secureAgainst_of_hybrid`.
- **Structural reference (do not depend on):** `Examples/PRGfromPRF.lean` — the
  state-threading `streamOutputs`/`streamPRG`/`prfReduction` is the closest existing model,
  and a good template for the *shape*. See §6 for why we do not build on it.

================================================================================

## 6. Integrity constraints (important)

- **`PRGfromPRF.streamPRG` is NOT a usable foundation.** Its central lemma
  `prfIdealGap_le_collisionProb` is a `sorry` in upstream VCVio (the random-function →
  ideal-PRG switching/collision argument is left unfinished). Building demo 3 on the
  **PRF→stream-PRG** path would mean either inheriting that `sorry` (forbidden by
  `CLAUDE.md`) or completing a research-grade coupling proof. We avoid both by using a
  **length-doubling PRG hybrid**, where each hop is a clean reduction to PRG security and
  there is no collision term. This is a deliberate design choice to keep the demo *honest
  and finishable*, and it should be stated as such in the demo's docstring.
- No `sorry`/`admit`, no new `axiom`s, no `native_decide`. The only assumptions are the
  named premises (PRG security, poly chain length) and the standard Aeneas/VCVio trust
  boundary — same posture as demos 1–2, audited by `make verify`.
- Do not hand-edit the extracted `Ratchet.lean`; fix `ratchet.rs` or the proof.

================================================================================

## 7. Stretch: forward secrecy

A second, qualitatively-protocol property worth stating once the chain is in place:
**compromising the chain key at step `j` does not endanger earlier message keys
`mk₀ … mk_{j-1}`** (they stay pseudorandom). This is the property that *motivates* a ratchet
over a flat key schedule, and it's the first place a "give the adversary the current state"
oracle enters — a step toward the adaptive, oracle-driven adversaries VCVio's `OracleComp`
is built for. Scope it as a follow-on: the hybrid for the plain pseudorandomness result is
the priority; forward secrecy reuses the same chain and one more reduction. Flag clearly
that full forward-secrecy-under-compromise is a stronger game than basic pseudorandomness.

================================================================================

## 8. Effort / risk

- **Hybrid bookkeeping** is the real work: defining `Hᵢ` cleanly, proving the adjacent-hop
  equality `|Pr[Hᵢ] − Pr[Hᵢ₊₁]| = prgAdvantage G Rᵢ`, and the telescope. Medium; the base
  re-indexing and `prgAdvantage` manipulation are already demonstrated in demos 2a/2b.
- **`[u8;64]` extraction ABI** across Charon/Aeneas — low risk (arrays already work for
  `combine`), but verify early; fall back to a struct/two-arg signature if needed.
- **`List.Vector` reasoning** for the output — minor; pattern set by `ByteArray.lean`.
- Everything rests on lemmas confirmed present and `sorry`-free in the pinned VCVio (v4.29.0).

================================================================================

## 9. Integration checklist (mirror the existing demos)

1. `demos/rust/ratchet.rs` — the source above.
2. `Makefile` `extract:` target — add the Charon+Aeneas lines for `ratchet.rs`
   (→ `Demos/Extracted/Ratchet.lean`).
3. `demos/lean/Demos/Ratchet/Step.lean`, `…/Chain.lean` — the proofs.
4. `demos/lean/Demos.lean` and `demos/lean/Audit.lean` — add the imports; add
   `#print axioms` for `ratchet_split_spec`, `keystream_hybrid_advantage`,
   `ratchet_secure_asymptotic`.
5. Top-level `README.md` — add the demo to the table and the "top-level theorems" list,
   noting it is the first demo with the `Σε` / poly-hops structure.
6. `make verify` green (only `[propext, Classical.choice, Quot.sound]`).
```
