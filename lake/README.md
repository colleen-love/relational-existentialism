# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in the live root's `formal/`, which the library reaches via
`srcDir = "../<root>/formal"`. After the arena reset (handoff I.II), only one library is live:

- [`paper-1/formal/`](../paper-1/formal) — `Paper1.*`, the new-arena skeleton (an empty root; spec II.1
  grows it).

The prior edifice's Lean (`Foundation.*`, `Theory.*`, the paper closures, `scratch/`) is archived under
[`../archive/archived/`](../archive/archived) as structural reference and is **not** built. See
[`lakefile.toml`](lakefile.toml) for the live target and [`../STRUCTURE.md`](../STRUCTURE.md) for the turn.

## Build

```
cd lake
lake build        # builds Paper1 (the only live library); an empty skeleton, green instantly
```

The archived development is not on the build path; to read what it proved, see
[`../archive/archived/INDEX.md`](../archive/archived/INDEX.md).
