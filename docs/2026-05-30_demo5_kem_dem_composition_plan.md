# Demo 5 — KEM/DEM IND-CPA composition (plan)

*Created 2026-05-30.*

## Goal

Derisk the **multi-primitive composition reasoning** the full libsignal proof needs, on a fully
*supervisable* footing: reuse VCVio's already-proven KEM/DEM → PKE composition and its trusted
IND-CPA games, instantiate the DEM with **real extracted-Rust** (our Demo 2 stream cipher), and
**discharge the DEM's one-time IND-CPA down to the PRG assumption** (the Demo 2 result). No new
security *games* are defined — every security notion is reused from VCVio — so a formal-methods
supervisor can validate this without a cryptographer (see `TRUST.md` and the supervisability
boundary recorded there).

This is the "wire two demos together / chain advantages across the tower" step. It is PQXDH-shaped
(PQXDH encrypts the initial message as KEM+DEM) and complements — without touching — the PQXDH/SPQR
extraction nodes (`Demos/Pqxdh/`, `Demos/Spqr/`).

## What VCVio already provides (trusted base — class **T**)

- `VCVio/CryptoFoundations/KeyEncapMech.lean` — `KEMScheme`, IND-CPA game
  (`IND_CPA_Game`/`IND_CPA_Advantage`, bias formulation) and IND-CCA game.
- `VCVio/CryptoFoundations/DataEncapMech.lean` — `DEMScheme`, **one-time** IND-CPA
  (`IND_CPA_Exp`/`IND_CPA_Game`/`IND_CPA_Advantage`).
- `VCVio/CryptoFoundations/KEMDEM.lean` — the composition:
  - `KEMScheme.composeWithDEM : KEMScheme → DEMScheme → AsymmEncAlg` (the composed PKE),
  - `perfectlyCorrect_composeWithDEM` (correctness),
  - **`ind_cpa_one_time_bias_advantage_compose_with_dem_le`** — the headline composition bound:
    `IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM dem) ≤
       kem.IND_CPA_Advantage (toKEMLeftReduction …) + kem.IND_CPA_Advantage (toKEMRightReduction …)
       + dem.IND_CPA_Advantage`,
    with the three reductions (`composeWithDEM_toKEMLeftReduction`, `…RightReduction`,
    `…toDEMReduction`) supplied.
- `VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/OneTime` — the PKE one-time IND-CPA game.
- **Demo 2** (`Demos/StreamCipher/*`) — the extracted stream cipher (`otp.xor` / the 32-byte
  `combine` loop) and its PRG-based security (`streamGen_advantage`, a tight reduction to
  `PRGScheme` security), plus the loop-correctness `stream.combine_spec`.

## Construction (class **C** — defined here, value-linked to extracted Rust)

A one-time symmetric DEM from the extracted stream cipher: `enc(k, m) = m ⊕ keystream(k)`,
`dec(k, c) = c ⊕ keystream(k)`, where the XOR is the **Aeneas-extracted** `combine` loop. Reuse
Demo 2's `combine_spec` as the value-adequacy link (no new extraction needed; possibly reuse
`mac.rs`/`stream.rs` as-is). This is a `DEMScheme` instance — *not* a new security game.

## Assumptions we bottom out on (class **A**)

- **KEM is IND-CPA-secure** — kept *abstract* (an arbitrary `KEMScheme` with its IND-CPA advantage
  appearing as a term). We deliberately do **not** instantiate a concrete KEM (avoids the lattice
  layer and any overlap with the PQXDH/SPQR agent).
- **The PRG is secure** — the same named assumption as Demo 2, reused.

## Milestones / deliverable theorems

1. **DEM construction + correctness.** Define the `DEMScheme` over the extracted stream XOR; prove
   `perfectlyCorrect` (dec ∘ enc = id), via `combine_spec` (value adequacy of the extracted loop).
2. **Discharge DEM IND-CPA → PRG.** The substantive new reasoning: prove
   `dem.IND_CPA_Advantage ≤ prgAdvantage (reduction)` for our stream-cipher DEM — i.e. one-time
   semantic security of the stream cipher, expressed in VCVio's `DEMScheme` IND-CPA game and reduced
   to `PRGScheme` security. Adapt/reuse Demo 2's `streamGen_advantage`-style reduction to the DEM
   game shape.
3. **Compose.** Form `kem.composeWithDEM ourDEM` for an abstract `kem`, apply
   `ind_cpa_one_time_bias_advantage_compose_with_dem_le`, and substitute milestone 2 to get the
   **headline**:
   `IND_CPA_OneTime_biasAdvantage (kem.composeWithDEM ourDEM) ≤
      2 · kem.IND_CPA_Advantage(reduction) + prgAdvantage(reduction')`.
   I.e. the composed KEM+DEM public-key encryption is one-time IND-CPA secure, bottoming out on
   *KEM IND-CPA* + *PRG* only.
4. **Correctness of the composed PKE** via `perfectlyCorrect_composeWithDEM` + milestone 1.
5. *(Optional)* **Asymptotic** version: if the KEM family and PRG family are secure (negligible),
   the composed PKE family is secure — reuse `Asymptotics/Negligible`.

## Trust ledger delta (to add to `TRUST.md` under a Demo 5 section)

| Surface | Class | Notes |
|---|---|---|
| KEM/DEM/PKE IND-CPA games; `composeWithDEM`; the composition bound | **T** | VCVio `KeyEncapMech`/`DataEncapMech`/`KEMDEM`, unchanged |
| Our `DEMScheme` over the extracted stream XOR | **C** | value-linked via `combine_spec`; not a security game |
| KEM IND-CPA | **A** | abstract KEM |
| PRG security | **A** | reused from Demo 2 |

**No new (C) security game.** This is the property that keeps Demo 5 on the supervisable side.

## Risks / open questions (resolve during development)

- **Game-shape fit:** does VCVio's `DEMScheme.IND_CPA` (one-time) game line up cleanly with the
  stream cipher's one-time semantic security as proved in Demo 2? Confirm the exact experiment shape
  (`IND_CPA_Exp b` / `IND_CPA_Game`) and whether Demo 2's reduction transfers or needs re-derivation.
- **DEMScheme field signature:** confirm `DEMScheme`'s `encrypt`/`decrypt` types (keyed, message,
  ciphertext) and that a deterministic one-time XOR DEM is admissible (the one-time game must not
  require randomized encryption).
- **Reuse vs re-extract:** prefer reusing Demo 2's extracted `combine`/`otp.xor` and `combine_spec`
  directly; only add Rust if the DEM interface needs a different shape.
- **`composeWithDEM` interface constraints:** the KEM's encapsulated-key type must match the DEM's
  key type; check the type plumbing in `KEMDEM.lean`.
- If milestone 2 (DEM IND-CPA ⇐ PRG) proves heavier than expected, the composition (milestone 3) is
  still a clean, supervisable result on top of *abstract* DEM IND-CPA — fall back to stating the
  composition with DEM IND-CPA as an assumption, and discharge to PRG as a separable extension.

## Method & discipline

Real extracted Rust → Aeneas → Lean, then VCVio reasoning. Genuine proofs only (no `sorry`/`axiom`/
`native_decide`/weakening). Gate with `make verify` (axiom-clean). Extend `TRUST.md` with the Demo 5
section. Develop on the `demo5` branch in this worktree; **do not merge to `main` without approval**.
