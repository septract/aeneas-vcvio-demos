# Briefing: how Aeneas code maps to VCVio security notions

2026-05-29. Companion: [the missing remainder](2026-05-29_briefing_missing-remainder.md),
[theory](rough_theory.md).

## The pipeline

```
real Rust ──Charon──▶ LLBC ──Aeneas──▶ Lean (pure functional model, in the `Result` monad)
                                          │  bridge
                                          ▼
                                  VCVio ProbComp / OracleComp  ──▶ security theorem
```

Aeneas gives a *pure functional* model: `f : Inputs → Result Output`, deterministic,
borrows/state erased, randomness threaded as explicit inputs. `Result = ok | fail | div`.

## The bridge (do it information-preservingly)

- **Maximal bridge = the monad unit.** `L_max : Result α → ProbComp (Result α) := pure`
  keeps the whole `Result` observable; it is fully abstract w.r.t. Aeneas's observation
  (distinguishes `ok v`, `fail e`, `div`). Define this first.
- **Weaker bridges = explicit coarsenings** `κ* ∘ L_max` (handlers), each with a *named*
  side-condition for when it loses nothing. The lossy `ofResult` (ok↦pure, fail/div↦abort)
  is one such, justified on a function *iff* the function is total there.
- **Never** use a silent lossy coercion (`Result.toOption.getD default`) — that changes
  fail/div behaviour and is unsound.

## Instantiation (the OTP miniature, the general pattern)

1. Extract the primitive: `otp.xor : U64 → U64 → Result U64` (genuine Aeneas output).
2. **Totality (value adequacy), divergence-sensitive:** `otp.xor k m = ok (k ^^^ m)`
   — an equation *in `Result`*, so it certifies no `fail`/`div`.
3. Instantiate VCVio's `SymmEncAlg` with `encrypt` **driven by the extracted function**
   (keygen `= $ᵗ`, the one sampling point).
4. Reduce `encrypt` to `pure (k ^^^ m)` via (2), then discharge VCVio's *general* Shannon
   theorem `perfectSecrecyAt_of_uniformKey_of_uniqueKey` (uniform key + deterministic enc
   + unique key per (msg,ct)). The security *definition and proof* are VCVio's, verbatim.

## Why the probability is cheap here

The node is **deterministic given coins**. Probability lives only in (i) the thin `$ᵗ`
sampling and (ii) the advantage statement (top-level). Because the extracted node equals
the model node *as a function of the coins*, the induced distributions are equal, so
**advantage is preserved by congruence** — push the same coins through equal functions.
No bespoke probabilistic refinement is needed for the deterministic core; the lift is a
plain equality pushed through the game (the commutation / maximal-bridge point).

## What a green proof certifies

That the **real extracted primitive** is the model's `encrypt`, and VCVio's security
property holds of it — an `ε = 0` (exact) link at the node boundary. It says nothing about
sequencing, network, or assumptions; see the companion note.
