# `formal/` — the lake package

After the six-root reorg, `formal/` is **only the build home**: it holds the lake package
([`lakefile.toml`](lakefile.toml)), the [`lean-toolchain`](lean-toolchain), and the (large, git-ignored)
mathlib cache under `.lake`. **No Lean sources live here** — they are dispersed into each root's `formal/`:

- [`foundation/formal/`](../foundation/formal) — `Foundation.*` (the traced-SMC typeclass)
- [`paper-1/formal/`](../paper-1/formal) — paper one's closure (`Scratch.*`, `RelExist.*`)
- [`theory/formal/`](../theory/formal) — the living frontier (`Theory.*`)
- `paper-2/formal/`, `scratch/formal/` — staging

The libraries reach those roots via `srcDir = "../<root>/formal"`; see [`lakefile.toml`](lakefile.toml) for
the targets and [`../STRUCTURE.md`](../STRUCTURE.md) for the layout, the closure gates, and the
fork-and-freeze discipline.

## Build

```
cd formal
lake build Foundation Paper1 Theory   # all libraries, green and sorry-free
lake build                            # default: Foundation only (fast, no mathlib)
```

The per-module status ledger that used to live here is **not** reproduced: each headline theorem is already
named with its Lean module in [`../paper-1/spec/paper-one.md`](../paper-1/spec/paper-one.md), the single
linear walk through the result.
