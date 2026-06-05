#!/usr/bin/env bash
# Tear down a git worktree created by dev-worktree.sh — SAFELY.
#
# WHY THIS SCRIPT EXISTS (and why it runs UNSANDBOXED):
#   Claude Code's command sandbox protects git metadata: a worktree's
#   .git / HEAD / objects / refs (and the main checkout's) sit on the sandbox
#   deny-list, so BOTH `git worktree remove` and a plain `rm -rf` fail with
#   "Operation not permitted". Teardown therefore cannot run sandboxed; it must
#   run with the sandbox disabled. The permission prompt you approve at that
#   point IS the safeguard — this script keeps the unsandboxed step minimal,
#   gated, and auditable so that approval is an easy, well-scoped yes.
#
# SAFETY GATES — it refuses to destroy anything unless ALL hold:
#   1. <name> is a real worktree under .worktrees/ (never `main`, never a path,
#      never a leading-dash/option-looking name).
#   2. the branch is an ANCESTOR of `main` (i.e. fast-forward / true-merged — the
#      workflow's documented path). NOTE: a squash- or rebase-merged branch is NOT
#      an ancestor even though its work is on main, so this gate REFUSES it; verify
#      manually and use --force in that case.
#   3. the worktree has no uncommitted changes to TRACKED files. (Untracked files
#      are NOT inspected — copy any deliverable note out of the worktree FIRST.)
#   Pass --force to override gates 2 and 3 (discards unmerged/uncommitted work).
#   It only ever touches the NAMED worktree's files. One caveat: the `git worktree
#   prune` step is global and will clear metadata for any OTHER worktree whose dir
#   is currently missing — `git worktree lock` long-lived parallel worktrees if
#   that coincidence is a concern.
#
# USAGE:
#   scripts/teardown-worktree.sh <name>            # safe: refuses if unmerged/dirty
#   scripts/teardown-worktree.sh <name> --force    # discard unmerged/uncommitted work
#
# HOW TO RUN IT (it needs the sandbox off — see above):
#   - Claude Code:  invoke Bash with dangerouslyDisableSandbox: true
#   - human prompt: prefix the command with `! `
#   Idempotent: re-running after a partial failure finishes the job (prunes
#   stale metadata, removes a lingering dir, drops the branch).
set -euo pipefail

main="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

name="${1:?usage: teardown-worktree.sh <name> [--force]}"
force=0
[ "${2:-}" = "--force" ] && force=1

# ── 1. guard the name ───────────────────────────────────────────────────────
# Refuse: empty, the integration branch, path separators, dotfiles (.. escapes,
# hidden), AND leading-dash names (which would be parsed as options by the git
# commands below — e.g. a fat-fingered `teardown-worktree.sh --force` with no
# name). All later ref arguments are additionally `--`-terminated as defence.
case "$name" in
  ""|main|master|*/*|.*|-*) echo "refuse: bad/forbidden worktree name '$name'" >&2; exit 2 ;;
esac
wt="$main/.worktrees/$name"
branch="$name"   # dev-worktree.sh names the branch == the worktree name

registered=0
if git -C "$main" worktree list --porcelain | grep -qx "worktree $wt"; then
  registered=1
fi

# ── 2. merge-safety gate ────────────────────────────────────────────────────
if git -C "$main" show-ref --verify --quiet "refs/heads/$branch"; then
  if ! git -C "$main" merge-base --is-ancestor "$branch" main; then
    if [ "$force" -eq 0 ]; then
      echo "REFUSE: branch '$branch' has commits not in 'main' — teardown would destroy unmerged work." >&2
      echo "        Merge it into main first, or re-run with --force to discard." >&2
      exit 1
    fi
    echo "WARNING: '$branch' is NOT merged into main; --force given, discarding its unmerged commits."
  fi
fi

# ── 3. dirty-tracked-files gate (uncommitted edits to tracked files) ─────────
if [ "$registered" -eq 1 ] && [ -d "$wt" ]; then
  dirty="$(git -C "$wt" status --porcelain --untracked-files=no 2>/dev/null || true)"
  if [ -n "$dirty" ]; then
    if [ "$force" -eq 0 ]; then
      echo "REFUSE: worktree '$name' has uncommitted changes to tracked files:" >&2
      echo "$dirty" >&2
      echo "        Commit/stash them, or re-run with --force to discard." >&2
      exit 1
    fi
    echo "WARNING: discarding uncommitted tracked changes in '$name' (--force given)."
  fi
fi

# ── 4. remove the worktree ───────────────────────────────────────────────────
# `--force`: the worktree holds untracked SHARED SYMLINKS (deps/, .lake/packages)
# that `git worktree remove` won't drop otherwise. Both `git worktree remove` and
# the `rm -rf` below only UNLINK these symlinks — they never recurse into the
# shared targets in the main checkout. DO NOT append a trailing slash to "$wt"
# or target the symlinks directly (e.g. "$wt/deps/"): a trailing slash on a
# symlink makes rm delete the TARGET's contents (~28 GB shared across main + every
# worktree). Always pass the bare directory "$wt".
if [ "$registered" -eq 1 ]; then
  git -C "$main" worktree remove --force "$wt"
  # prune ONLY after we removed our own entry. `worktree prune` is GLOBAL — it
  # clears metadata for ANY worktree whose dir is currently missing — so we keep
  # it scoped to the case where we just changed worktree state, minimising the
  # chance of clipping a sibling (parallel agent) whose dir is transiently absent.
  git -C "$main" worktree prune
fi
[ -e "$wt" ] && rm -rf "$wt"   # belt-and-suspenders if a prior run left the dir behind

# ── 5. drop the (now fully-merged, or force-discarded) branch ────────────────
# Tolerate a non-force `branch -d` failure: by this point the worktree dir +
# metadata are already gone, so aborting here (under set -e) would leave a
# confusing partial state. A lingering branch is harmless and a re-run drops it.
if git -C "$main" show-ref --verify --quiet "refs/heads/$branch"; then
  if [ "$force" -eq 1 ]; then
    git -C "$main" branch -D -- "$branch"
  else
    git -C "$main" branch -d -- "$branch" \
      || echo "warn: branch '$branch' left in place (git considers it not fully merged) — delete manually if intended" >&2
  fi
fi

echo "✓ torn down worktree '$name'${branch:+ and branch '$branch'}"
echo "--- remaining worktrees ---"
git -C "$main" worktree list
