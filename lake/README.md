# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each series' `formal/`, which its library reaches via
`srcDir = "../<series>/formal"`. Series 03–06 are closed and frozen under `archive/`
(`archive/series-03/`…`archive/series-06/`) and are no longer registered here. Series 07 (complete) and
Series 08 (live) are both built here, each as its own `lean_lib` in a distinct module namespace:

- [`series-07/formal/`](../series-07/formal) — `Series07`, complete (`Series07.ws1`…`ws7`,
  `Series07.AxiomCheck`); `sorry`-free and axiom-clean.
- [`series-08/formal/`](../series-08/formal) — `Series08`, the live development (`Series08.ws1`…`ws7`,
  `Series08.AxiomCheck`); the finite-perspective program, `sorry`-free and axiom-clean.

The flat `ws1`…`ws7` / `AxiomCheck` module names are reused across series and Lean modules are global,
so each series lives under its own root namespace: Series 07's sources are in `series-07/formal/Series07/`
(modules `Series07.wsN`) and Series 08's in `series-08/formal/Series08/` (modules `Series08.wsN`). See
[`lakefile.toml`](lakefile.toml) for both targets.

## Build

```
cd lake
lake build                            # builds Series07 and Series08 (+ each AxiomCheck)
lake build Series08 Series08.AxiomCheck # just the Series 08 axiom pass
lake build Series07 Series07.AxiomCheck # just the Series 07 axiom pass
```

The mathlib cache must be warm (both series import it).
