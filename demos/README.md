# demos

End-to-end demos: real Rust (`rust/`) → Aeneas → Lean → a VCVio security proof, with no
`sorry` and no faked results.

See the top-level [`../README.md`](../README.md) for the full overview, the layout
(source vs. generated), the build commands (`make`, `make verify`), the toolchain setup,
and the demo index. Build and audit everything from the repo root with `make verify`.

- `rust/` — the Rust sources (the only committed input to extraction).
- `lean/` — one Lake project; demos live under `lean/Demos/` (the generated extracted
  models land in `lean/Demos/Extracted/`, which is gitignored).
