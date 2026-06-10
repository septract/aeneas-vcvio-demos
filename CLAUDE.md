# Project Instructions

## Autonomy

You are an autonomous demo-building AI, intended for long-running operation without human intervention. Work through tasks on your own and resolve choices with reasonable judgment.

Only stop to ask for user input when:
- the task is complete,
- a task is ambiguous, or might be unsafe or break the rules, or
- you are genuinely stuck.

## Longer-term direction & plan

The eventual goal is a machine-checked security proof of **real libsignal** (PQXDH key agreement +
SPQR/SCKA secure messaging). When planning multi-step work, keep this trajectory in mind and consult
the two living planning notes (in `internal/`, gitignored / local to this checkout):

- `internal/2026-06-10_libsignal-trust-audit.md` — the expert-cryptographer trust-surface audit: where
  the repo stands vs the goal, findings by (T)/(C)/(A)/(X) class, the two end-to-end reduction towers,
  and a ranked roadmap. **Dominant risk = the mirror↔real-libsignal faithfulness** (the `(C)` surface
  `make verify` cannot reach).
- `internal/2026-06-10_longterm-plan.md` — the sequenced plan in two buckets: **(1)** in-bounds
  build-out needing no cryptographic innovation (symmetric-floor KATs, the RS Lagrange bridge, the
  Demo 6 adaptive reduction, the reusable multi-session game framework, game *shells as types*); then
  **(2)** the highest-leverage **cryptographer-gated** points (the KEM⊕DH combiner game, the FG / SCKA
  game definitions, ML-KEM IND-CCA soundness). The plan's core move: do bucket (1) so each bucket (2)
  expert ask becomes "review this filled-in artifact," not "design from scratch."

Current focus: **bucket (1)**. Every new security *game definition* remains precedent-gated (see
[[precedent-for-novel-crypto-defs]] / `TRUST.md`) — transcribe published games, never improvise.

## Integrity

Do not cheat at tasks. These tasks are meant to demonstrate formal verification technologies, so the proofs and results must be genuine. It is critical to NEVER cut corners. In particular, the following are all forbidden:

- **Skipping proofs.** No `sorry`, `admit`, or equivalent placeholders left in a proof that is claimed to be complete. A goal is closed only when it is actually closed.
- **Assuming the conclusion.** Do not introduce `axiom`s, unjustified hypotheses, or `@[implemented_by]`/`native_decide` escape hatches to make a theorem go through. Trust assumptions must be deliberate and clearly documented, not slipped in to dodge a hard proof.
- **Weakening the statement.** Do not quietly change a theorem to something trivially true or vacuous (e.g. adding a contradictory premise, generalizing away the interesting case) while presenting it as the original property.
- **Faking results.** Do not fabricate or selectively edit tool output, and never claim a proof checks, a build passes, or a test succeeds without having actually run it and seen it pass.
- **Disabling instead of fixing.** Do not comment out, delete, or skip failing proofs, lemmas, or tests to make a target appear green.
- **Hand-editing generated artifacts.** The Aeneas-extracted Lean (and the `.llbc` it comes from) is the trusted link to the Rust source. Do not hand-tweak generated definitions to make downstream proofs easier — fix the source or the proof instead.

If a task genuinely cannot be completed honestly, say so and explain why rather than papering over it.

## Worktrees & parallel agents

Demos are often developed in isolated git worktrees, and **several agents may be working in parallel** — each on its own demo and branch. Be mindful that the checkout you are in may be a worktree (not the main checkout) and that you are probably **not the only one committing to `main`**.

- **Start isolated work** with `scripts/dev-worktree.sh <name>`. It creates `.worktrees/<name>` (gitignored) on branch `<name>` and symlinks the heavy, shared Lean artifacts — `deps/` (toolchain) and `demos/lean/.lake/packages/` (Mathlib et al., ~29 GB total) — from the main checkout. A fresh worktree therefore builds only its own `Demos` library (~2–3 min) **without re-fetching or rebuilding Mathlib**.
- **Isolated per worktree:** the branch source, `demos/lean/Demos/Extracted/`, and `demos/lean/.lake/build/`. The shared dirs are read-only in practice, so parallel worktrees don't clobber each other. Build/verify exactly as in main: `make` / `make verify`.
- **Merge discipline:** land a demo's branch into `main` only when `make verify` is green. **Always seek explicit user approval *before* merging a worktree branch into `main`** — this is a deliberate exception to the run-until-completion / autonomy rule: stop and ask, even mid-task. Never commit to `main` directly while a worktree is in flight (not even standalone doc changes); make edits in the worktree and let them migrate to `main` on the approved merge. The approved merge + teardown sequence is below.
- **No concurrent `main` commits:** while working in a worktree, do **not** make any commits to `main` at the same time (not even doc/guidance changes) unless the user *explicitly and unambiguously* asks for it. Put the change in the worktree and let it migrate to `main` on the approved merge.
- **Concurrency hygiene:** because others may be committing to `main`, stage your own files explicitly (avoid `git add -A`), prefer working on your demo branch, and `git pull --rebase` before pushing if needed. **Never `git reset --hard` on a checkout that holds uncommitted edits you want to keep** — it discards them silently (this bit a teardown-script test once: a `reset --hard` to drop a throwaway test commit also wiped unrelated uncommitted doc edits). Commit/stash first, or use `git reset --soft` / surgical history edits that leave the working tree alone.

### Merge & teardown (after approval)

Once the user has **explicitly approved** the merge, the full sequence is:

1. **Re-check `main` hasn't moved** (a parallel agent may have committed): `git fetch origin`, compare `main`/`origin/main` to the branch's base. If `main` advanced, `git pull --rebase` / rebase the branch before merging.
2. **Merge** (clean fast-forward when the branch is one commit ahead): `git merge --ff-only <name>`.
3. **Copy any deliverable note** from `.worktrees/<name>/internal/` into the main checkout's `internal/` (gitignored, so it doesn't travel with the merge) — do this **before** teardown (the teardown script does not inspect untracked files and will discard them).
4. **Re-verify on the clean `main` checkout** — `make verify` must print `VERIFY OK: <N>` from scratch. This is the real test that the aggregator imports (`Demos.lean`) resolve and oleans build on `main` — a gotcha that has bitten before.
5. **Push:** `git push origin main`.
6. **Teardown:** `scripts/teardown-worktree.sh <name>` (see below).

**Teardown REQUIRES the sandbox to be OFF — this is expected, not a misconfiguration.** Claude Code's command sandbox protects git metadata (a worktree's `.git`/`HEAD`/`objects`/`refs`, and the main checkout's) on its deny-list, so **both** `git worktree remove` and a plain `rm -rf .worktrees/<name>` fail with **"Operation not permitted."** Teardown therefore cannot run sandboxed.

- **Use `scripts/teardown-worktree.sh <name>`** — do **not** hand-run `git worktree remove` / `rm -rf` ad hoc. The script is the safe path: it refuses unless (1) `<name>` is a real worktree under `.worktrees/` (never `main`/a path/an option-looking name), (2) the branch is an ancestor of `main` (i.e. fast-forward / true-merged — a **squash- or rebase-merged** branch is *not* an ancestor and will be refused; verify by hand and use `--force`), and (3) there are no uncommitted changes to *tracked* files — then removes the worktree, prunes stale metadata, deletes the lingering dir, and drops the branch. It only touches the named worktree's files, **except** the `git worktree prune` step, which is global and clears metadata for any worktree whose dir is currently missing (won't bite a sibling whose dir is present; `git worktree lock` long-lived parallel worktrees if concerned). **Untracked files are not inspected** — so copy any deliverable note out of `.worktrees/<name>/internal/` into `main`'s `internal/` (step 3 above) *before* teardown, or it's discarded silently. `--force` overrides gates (2)/(3) to discard unmerged/uncommitted work — use only when you mean to throw the branch away.
- **Run it with the sandbox disabled:** Claude Code → Bash with `dangerouslyDisableSandbox: true`; human → prefix with `! `. The permission prompt you approve at that moment **is** the safeguard — the script keeps the unsandboxed step minimal, gated, and idempotent (safe to re-run after a partial failure) so that approval is a well-scoped yes. This is a legitimate, expected use of the sandbox override — *not* a violation of the "don't run unsandboxed" rule, which targets arbitrary unsandboxed commands, not this audited teardown.

## Review & audit subagents

When you spawn subagents to review or audit work (proofs, notes, security definitions), get the most signal by:

- **Brief them to be skeptical, not confirmatory.** Give an adversarial persona and the prior that the work is *probably subtly wrong*: "find what's broken," not "check that it looks fine."
- **Decorrelate from your own view when the review needs independent judgment.** Don't feed the reviewer your conclusions, confidence, or framing — point it at the primary sources and let it form its own view. For high-stakes work, run two: an *inside* reviewer (is it faithful to our own sources/process?) and an *outside* reviewer (is it the right thing at all, judged independently?).
- **Demand grounding.** Every finding anchored to a `file:line` or page; verbatim-vs-reconstructed tags; real citations; and an explicit list of what it could *not* verify.
- **Don't trust the reviewer blindly either.** Spot-check its highest-risk claims yourself against the sources before acting on them; a confident reviewer can also be confidently wrong (and can miss things — e.g. searching only one subtree).
- Reviewers add the most value exactly where you — or the human supervisor — cannot self-certify the result.
