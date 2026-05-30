# Briefing: the missing remainder — what it takes to cover all of Signal

2026-05-29. Companion: [Aeneas→VCVio](2026-05-29_briefing_aeneas-to-vcvio.md).

## A protocol security proof has three parts

1. **Primitive operations / nodes** — the crypto + ratchet math.
2. **Sequencing / orchestration** — how operations are ordered, the responses at choice
   points, the message flow, state carried across steps.
3. **Network / adversary / trust model** — who is honest, what is authenticated, what the
   adversary can do, hardness assumptions.

## What we can and can't lift

| Part | In the artifact? | Liftable? | By what |
|---|---|---|---|
| (1) nodes | yes, pure | **yes** | Aeneas → functional model (done; see companion) |
| (2) orchestration | yes, **effectful** | yes *in principle* | FM: separation logic / Iris / interaction trees; **not** Aeneas (pure-only) |
| (3) network/trust/hardness | **no** — stipulations about the world | **no** | authored premises; adversarial *network* is modelable (UC), trust+hardness are not |

- (1) is the `ε=0` node link. Done.
- (2) is **deterministic given injected coins**, so lifting it is a *deterministic*
  refinement problem (no new probabilistic machinery for the core). It is *modelable and
  verifiable* by FM — **Igloo** (Sprenger/Basin) is the structural prototype: it links
  effectful protocol implementations to abstract models under an IO boundary and transfers
  security down; Verdi/Disel/IronFleet verify effectful protocol composition. The **gap**:
  this is barely explored *in crypto*, and not integrated with the probabilistic crypto-game
  layer (VCVio). The crypto-integrated version of Igloo is the open frontier; the only place
  genuine *probabilistic* refinement is forced is data-dependent samplers (PQ rejection
  sampling), which are localized.
- (3) cannot be lifted because there is nothing in the code to lift. The adversarial network
  is modelable as an environment; **trust/setup** (honest party, authenticated channel,
  honest keygen) and **hardness** (DDH, …) stay authored, and crucially *uncheckable against
  the code* — a too-strong assumption typechecks fine and is where deployments break.

## libsignal is only partially sans-IO (checked against the source)

- Primitives & ratchet math (`crypto.rs`, `curve`, `kem`, `ratchet`): **pure** → nodes (1).
- Randomness: **dependency-injected** (`R: Rng + CryptoRng` parameter) → sans-IO-friendly.
- Persistence: **effectful and internal.** `SessionStore`/`IdentityKeyStore`/`PreKeyStore`/
  `SignedPreKeyStore`/`KyberPreKeyStore` are `#[async_trait]`; `message_encrypt`/
  `message_decrypt`/`process_prekey_bundle` are `async fn` that **await store callbacks
  interleaved with protocol logic**. That session layer (`session.rs`, `session_cipher.rs`)
  **is** part (2), and it is *not* pure atomic nodes.

So the IO boundary to cut at is **the async `*Store` interface threaded through the protocol
ops**, not the library's outer edge.

## Bottom line

- Today: lift (1) faithfully (Aeneas→VCVio), hand-author (2) and (3) as a model, prove
  security on the model. The certified part is (1); (2) and (3) are authored.
- To "prove libsignal correct" (faithful, every line → intended effect): lift (2) under the
  store IO boundary — a **deterministic effectful refinement** (Igloo-style) **integrated
  with VCVio's probabilistic top**. This does not exist as a crypto-endorsed method; it is
  the frontier.
- (3) remains an explicit, named assumption budget regardless — the right deliverable is to
  make that budget small and legible, not to eliminate it.

## The uncomfortable part

The errors in real systems concentrate in (2) — sequencing, state, error handling,
concurrency, interaction. That is exactly the part the current lift does **not** cover. So
node-level verification concentrates assurance where errors are sparse; the error-dense
orchestration is where the unowned (2)-lift frontier lies.
