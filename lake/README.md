# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in the live root's `formal/`, which the library reaches via
`srcDir = "../<root>/formal"`. After the arena reset (handoff I.II), only one library is live:

- [`series-2/formal/`](../series-2/formal) — `Series2.*`, the new-arena skeleton; spec 2.1 grows it.

See [`lakefile.toml`](lakefile.toml) for the live target and [`../STRUCTURE.md`](../STRUCTURE.md) for the turn.

## Build

```
cd lake
lake build        # builds Series2 (the only live library); an empty skeleton, green instantly
```
