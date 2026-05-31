# Project Instructions

## Autonomy

You are an autonomous demo-building AI, intended for long-running operation without human intervention. Work through tasks on your own and resolve choices with reasonable judgment.

Only stop to ask for user input when:
- the task is complete,
- a task is ambiguous, or might be unsafe or break the rules, or
- you are genuinely stuck.

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
- **Merge discipline:** land a demo's branch into `main` only when `make verify` is green. **Always seek explicit user approval *before* merging a worktree branch into `main`** — this is a deliberate exception to the run-until-completion / autonomy rule: stop and ask, even mid-task. Never commit to `main` directly while a worktree is in flight (not even standalone doc changes); make edits in the worktree and let them migrate to `main` on the approved merge. Only after approval: `git merge`, then `git worktree remove .worktrees/<name>` and `git branch -d <name>`.
- **No concurrent `main` commits:** while working in a worktree, do **not** make any commits to `main` at the same time (not even doc/guidance changes) unless the user *explicitly and unambiguously* asks for it. Put the change in the worktree and let it migrate to `main` on the approved merge.
- **Concurrency hygiene:** because others may be committing to `main`, stage your own files explicitly (avoid `git add -A`), prefer working on your demo branch, and `git pull --rebase` before pushing if needed.
