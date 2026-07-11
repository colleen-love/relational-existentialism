# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each series' `formal/`, which its library reaches via
`srcDir = "../<series>/formal"`. Series 3–6 are closed and frozen under `archive/`
(`archive/series-3/`…`archive/series-6/`) and are no longer registered here. Series 7 is the live
development and the only library built:

- [`series-7/formal/`](../series-7/formal) — `Series7`, the live development (`Series7.ws1`…`ws7`,
  `Series7.AxiomCheck`); `sorry`-free and axiom-clean.

The flat `ws1`…`ws7` / `AxiomCheck` module names are reused across series and Lean modules are global,
so each series lives under its own root namespace: Series 7's sources are in `series-7/formal/Series7/`
(modules `Series7.wsN`). See [`lakefile.toml`](lakefile.toml) for the target.

## Build

```
cd lake
lake build                            # builds Series7 (+ Series7.AxiomCheck)
lake build Series7 Series7.AxiomCheck # just the Series 7 axiom pass
```

The mathlib cache must be warm (Series 7 imports it).
