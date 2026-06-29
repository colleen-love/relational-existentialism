# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each *root*'s `formal/`, which the libraries reach via
`srcDir = "../<root>/formal"`:

- [`foundation/formal/`](../foundation/formal) — `Foundation.*` (the traced-SMC typeclass)
- [`paper-1/formal/`](../paper-1/formal) — paper one's skeleton (empty `Paper1` root)
- [`paper-2/formal/`](../paper-2/formal) — paper two's closure (`Scratch.*`, `RelExist.*`)
- [`theory/formal/`](../theory/formal) — the shared theory layer (`Theory.*`)
- [`paper-3/formal/`](../paper-3/formal) — the modular slice (`Paper3.*`)
- `scratch/formal/` — the living frontier (paper four)

See [`lakefile.toml`](lakefile.toml) for the targets and [`../STRUCTURE.md`](../STRUCTURE.md) for the layout,
the closure gates, the fork-and-freeze discipline, and the roots-vs-infrastructure distinction (`lake/` is
infrastructure — `formal/` now only ever means "a root's Lean sources").

## Build

```
cd lake
lake build Foundation Paper1 Paper2 Theory Paper3   # all libraries, green and sorry-free
lake build                                   # default: Foundation only (fast, no mathlib)
```

The per-module status ledger that used to live here is **not** reproduced: each headline theorem is already
named with its Lean module in [`../paper-2/spec/paper-two.md`](../paper-2/spec/paper-two.md) and
[`../paper-3/spec/paper-three.md`](../paper-3/spec/paper-three.md), the single linear walks through the results.
