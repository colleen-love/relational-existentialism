# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each series' `formal/`, which its library reaches via
`srcDir = "../<series>/formal"`. Series 3–6 are closed and frozen under `archive/`
(`archive/series-3/`…`archive/series-6/`) and are no longer registered here. Series 7 (complete) and
Series 8 (live) are both built here, each as its own `lean_lib` in a distinct module namespace:

- [`series-7/formal/`](../series-7/formal) — `Series7`, complete (`Series7.ws1`…`ws7`,
  `Series7.AxiomCheck`); `sorry`-free and axiom-clean.
- [`series-8/formal/`](../series-8/formal) — `Series8`, the live development (`Series8.ws1`…`ws7`,
  `Series8.AxiomCheck`); the finite-perspective program, `sorry`-free and axiom-clean.

The flat `ws1`…`ws7` / `AxiomCheck` module names are reused across series and Lean modules are global,
so each series lives under its own root namespace: Series 7's sources are in `series-7/formal/Series7/`
(modules `Series7.wsN`) and Series 8's in `series-8/formal/Series8/` (modules `Series8.wsN`). See
[`lakefile.toml`](lakefile.toml) for both targets.

## Build

```
cd lake
lake build                            # builds Series7 and Series8 (+ each AxiomCheck)
lake build Series8 Series8.AxiomCheck # just the Series 8 axiom pass
lake build Series7 Series7.AxiomCheck # just the Series 7 axiom pass
```

The mathlib cache must be warm (both series import it).
