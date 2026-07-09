-- `Series5` — the live Lean root (Spec Series 5).
-- Series 3 is closed and frozen under `archive/`; Series 4 is complete under
-- `series-4/`. Series 5 opens the stratification program: a doubly-unbounded
-- tower of faced carriers `W_α` whose colimit `W_∞` is boundless above (no
-- last level, no imposed cardinal) and groundless below (no first level, no
-- atom-floor), with graded cross-level faces. The Series 5 charter
-- (`series-5/charter.md`) and its per-workstream design docs
-- (`series-5/spec/wsNN-design.md`) grow it.
--
-- STATUS: skeleton. No workstream is formalized yet, so this root carries no
-- theorems and imports nothing. Series 5 is WHOLLY STANDALONE (charter §1,
-- `series-5/spec/readme.md`): every Series 4 (and, in WS6, Series 3) lemma it
-- reuses is transcribed into `series-5/formal/wsNN.lean` and re-namespaced
-- `Series5.WSNN` — nothing is imported from `series-4/` or `archive/`.
-- Toolchain pinned as Series 4: Lean 4 `v4.15.0` / Mathlib `v4.15.0`.
--
-- As each workstream lands, register its root (`ws1`..`ws7`) in
-- `lake/lakefile.toml`, `import` it here, and add its headline theorem to the
-- `#print axioms` ledger in `AxiomCheck.lean` — mirroring the Series 4 build.
--
-- The seven workstreams the charter (§6) fixes:
--   WS1 — the tower and its colimit (blocking; the colimit gate).
--   WS2 — the explosion, and the forced answer (the spine).
--   WS3 — boundlessness without a wall.
--   WS4 — no first, no last: poles and the view from nowhere.
--   WS5 — the self-bounding of the world, revisited.
--   WS6 — relating across levels, and attention as grade-shift.
--   WS7 — the anti-trivialization audit (the verdict).

namespace Series5

end Series5
