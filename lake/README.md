# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in the live root's `formal/`, which the library reaches via
`srcDir = "../<root>/formal"`. Series 3 is closed and frozen under `archive/`; Series 4 is complete under
`series-4/`; Series 5 is the one live library:

- [`series-5/formal/`](../series-5/formal) — `Series5`, the live Series 5 development
  (`ws1`…`ws7`, `AxiomCheck`); the stratification program, `sorry`-free and axiom-clean.

See [`lakefile.toml`](lakefile.toml) for the live target.

## Build

```
cd lake
lake build        # builds Series5 (ws1…ws7 + AxiomCheck); the mathlib cache must be warm
```
