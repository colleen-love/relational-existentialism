-- `Series7` — the live Lean root (Spec Series 7).
--
-- Series 3 is closed and frozen under `archive/`; Series 4, 5, 6 are complete under
-- `series-4/`, `series-5/`, `series-6/`. Series 7 is the capstone: it proves the **Import
-- Theorem** — atomless plurality is impossible without an import. The charter
-- (`series-7/charter.md`) and per-workstream designs (`series-7/spec/wsNN-design.md`) specify it.
--
-- Series 7 is WHOLLY STANDALONE (charter §1): every Series 4/5/6 lemma it reuses is transcribed
-- into `series-7/formal/Series7/wsNN.lean` and re-namespaced `Series7.WSNN` — nothing is imported
-- from `series-6/`, `series-5/`, `series-4/`, or `archive/`. Toolchain pinned as Series 4/5/6:
-- Lean 4 `v4.15.0` / Mathlib `v4.15.0`. The full build compiles `sorry`-free with no custom
-- axioms; every result rests only on Mathlib's standard three (`propext` / `Classical.choice` /
-- `Quot.sound`), recorded by `AxiomCheck.lean`.
--
-- HEADLINE. The central deliverable is an Impossibility (a first-class success, charter §7): the
-- **Import Theorem** `WS2.ws2_import_theorem` — no plain, behaviorally-identified, atomless
-- coalgebra is plural — driven by the general engine `WS1.ws1_atomless_bisim` (the "both-atomless"
-- bisimulation), recovering the static and dynamic collapses as instances. It is proved
-- non-circular (WS2/WS7: behavioral identity IS the no-import principle; the escapes refuted as
-- theorems), the trichotomy of distinction lands on a single coalgebra (WS3, Partial across "any
-- construction"), the program is explained (WS4: weights/labels/levels the forced drops, Series 6
-- the drop that collapsed), the one loophole is isolated and adjudicated import-in-time (WS5), the
-- heuristic ceiling drawn (WS6), and the typed verdict is `payoffsEstablished` (WS7).

-- WS1 — the engine: atomless behavior is unique on any plain coalgebra (`ws1_atomless_bisim`);
-- the static and dynamic instances recovered.
import Series7.ws1
-- WS2 — the Import Theorem (`ws2_import_theorem`) and its non-circularity (`ws2_non_circular`).
import Series7.ws2
-- WS3 — the trichotomy of distinction (`ws3_trichotomy`); exhaustive on a single coalgebra.
import Series7.ws3
-- WS4 — the imports catalogued (`ws4_program_explained`): the program explained.
import Series7.ws4
-- WS5 — the limit-atomlessness loophole (`ws5_limit_reintroduces_leaves`), adjudicated import-in-time.
import Series7.ws5
-- WS6 — the heuristic ceiling: the provable core mechanized, the universal reported heuristic.
import Series7.ws6
-- WS7 — the anti-circularity audit and the typed verdict (`payoffsEstablished`).
import Series7.ws7
