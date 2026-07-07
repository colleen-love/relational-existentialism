# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in the live root's `formal/`, which the library reaches via
`srcDir = "../<root>/formal"`. Series 2 is closed and frozen under `archive/`; Series 3 is the one live library:

- [`series-3/formal/`](../series-3/formal) — `Series3`, the Series 3 skeleton; the Series 3 charter grows it.

See [`lakefile.toml`](lakefile.toml) for the live target.

## Build

```
cd lake
lake build        # builds Series3 (the only live library); an empty skeleton, green instantly
```
