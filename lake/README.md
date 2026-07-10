# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each series' `formal/`, which its library reaches via
`srcDir = "../<series>/formal"`. Series 3 is closed and frozen under `archive/`; both Series 4 (complete)
and Series 5 (live) are built here, each as its own `lean_lib` in a distinct module namespace so the two
can coexist in one package:

- [`series-4/formal/`](../series-4/formal) — `Series4`, complete (`Series4.ws1`…`ws7`, `Series4.AxiomCheck`);
  the restriction-quality program, `sorry`-free and axiom-clean.
- [`series-5/formal/`](../series-5/formal) — `Series5`, the live development (`Series5.ws1`…`ws7`,
  `Series5.AxiomCheck`); the stratification program, `sorry`-free and axiom-clean.

The flat `ws1`…`ws7` / `AxiomCheck` module names are identical across both series, and Lean modules are
global, so each series lives under its own root namespace: Series 4's sources are in
`series-4/formal/Series4/` (modules `Series4.wsN`) and Series 5's in `series-5/formal/Series5/` (modules
`Series5.wsN`). See [`lakefile.toml`](lakefile.toml) for both targets.

## Build

```
cd lake
lake build                            # builds both Series4 and Series5 (+ each AxiomCheck)
lake build Series4 Series4.AxiomCheck # just the Series 4 axiom pass
lake build Series5 Series5.AxiomCheck # just the Series 5 axiom pass
```

The mathlib cache must be warm (both series import it).
