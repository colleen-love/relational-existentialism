# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each series' `formal/`, which its library reaches via
`srcDir = "../<series>/formal"`. Series 03–06 and 08 are closed and frozen under `archive/`
(`archive/series-03/`…`archive/series-08/`) and are no longer registered here. Series 07 (complete),
Series 09, and Series 10 (live) are built here, each as its own `lean_lib` in a distinct module namespace:

- [`series-07/formal/`](../series-07/formal) — `Series07`, complete (`Series07.ws1`…`ws7`,
  `Series07.AxiomCheck`); `sorry`-free and axiom-clean.
- [`series-09/formal/`](../series-09/formal) — `Series09`, the self-reference / diagonal program
  (`Series09.ws1`…`ws7`, `Series09.AxiomCheck`); `sorry`-free and axiom-clean.
- [`series-10/formal/`](../series-10/formal) — `Series10`, the reification program (`Series10.ws1`…`ws7`,
  `Series10.AxiomCheck`); `sorry`-free and axiom-clean.

The flat `ws1`…`ws7` / `AxiomCheck` module names are reused across series and Lean modules are global,
so each series lives under its own root namespace (e.g. Series 10's sources are in
`series-10/formal/Series10/`, modules `Series10.wsN`). See [`lakefile.toml`](lakefile.toml) for all targets.

## Build

```
cd lake
lake build                            # builds Series07 + Series09 + Series10 (+ each AxiomCheck)
lake build Series10 Series10.AxiomCheck # just the Series 10 axiom pass
lake build Series07 Series07.AxiomCheck # just the Series 07 axiom pass
```

The mathlib cache must be warm (all series import it).
