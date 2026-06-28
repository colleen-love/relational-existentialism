# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in each *root*'s `formal/`, which the libraries reach via
`srcDir = "../<root>/formal"`:

- [`foundation/formal/`](../foundation/formal) — `Foundation.*` (the traced-SMC typeclass)
- [`paper-1/formal/`](../paper-1/formal) — paper one's closure (`Scratch.*`, `RelExist.*`)
- [`theory/formal/`](../theory/formal) — the living frontier (`Theory.*`)
- [`paper-2/formal/`](../paper-2/formal) — the modular slice (`Paper2.*`)
- `scratch/formal/` — staging

See [`lakefile.toml`](lakefile.toml) for the targets and [`../STRUCTURE.md`](../STRUCTURE.md) for the layout,
the closure gates, the fork-and-freeze discipline, and the roots-vs-infrastructure distinction (`lake/` is
infrastructure — `formal/` now only ever means "a root's Lean sources").

## Build

```
cd lake
lake build Foundation Paper1 Theory Paper2   # all libraries, green and sorry-free
lake build                                   # default: Foundation only (fast, no mathlib)
```

The per-module status ledger that used to live here is **not** reproduced: each headline theorem is already
named with its Lean module in [`../paper-1/spec/paper-one.md`](../paper-1/spec/paper-one.md) and
[`../paper-2/spec/paper-two.md`](../paper-2/spec/paper-two.md), the single linear walks through the results.
