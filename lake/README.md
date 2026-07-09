# `lake/` — the Lean package home (infrastructure, not a root)

`lake/` is **only the build home**: it holds the Lake package ([`lakefile.toml`](lakefile.toml)), the
[`lean-toolchain`](lean-toolchain), the manifest, and the (large, git-ignored) mathlib cache under `.lake`.
**No Lean sources live here** — they live in the live root's `formal/`, which the library reaches via
`srcDir = "../<root>/formal"`. Series 3 is closed and frozen under `archive/`; Series 4 is complete under
`series-4/`; Series 5 is the one live library:

- [`series-5/formal/`](../series-5/formal) — `Series5`, the Series 5 skeleton; the Series 5 charter grows it.

See [`lakefile.toml`](lakefile.toml) for the live target.

## Build

```
cd lake
lake build        # builds Series5 (the only live library); an empty skeleton, green instantly
```
