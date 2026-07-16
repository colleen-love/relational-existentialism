-- `Series07` — the live Lean root (Spec Series 07).
--
-- Series 03 is closed and frozen under `archive/`; Series 04, 05, 06 are complete under
-- `series-04/`, `series-05/`, `series-06/`. Series 07 is the capstone: it proves the **Import
-- Theorem** — atomless plurality is impossible without an import. The charter
-- (`series-07/charter.md`) and per-workstream designs (`series-07/spec/wsNN-design.md`) specify it.
--
-- Series 07 is WHOLLY STANDALONE (charter §1): every Series 04/05/06 lemma it reuses is transcribed
-- into `series-07/formal/Series07/wsNN.lean` and re-namespaced `Series07.WSNN` — nothing is imported
-- from `series-06/`, `series-05/`, `series-04/`, or `archive/`. Toolchain pinned as Series 04/05/06:
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
-- construction"), the program is explained (WS4: weights/labels/levels the forced drops, Series 06
-- the drop that collapsed), the one loophole is isolated and adjudicated import-in-time (WS5), the
-- heuristic ceiling drawn (WS6), and the typed verdict is `payoffsEstablished` (WS7).

-- WS1 — the engine: atomless behavior is unique on any plain coalgebra (`ws1_atomless_bisim`);
-- the static and dynamic instances recovered.
import Series07.ws1
-- WS2 — the Import Theorem (`ws2_import_theorem`) and its non-circularity (`ws2_non_circular`).
import Series07.ws2
-- WS3 — the trichotomy of distinction (`ws3_trichotomy`); exhaustive on a single coalgebra.
import Series07.ws3
-- WS4 — the imports catalogued (`ws4_program_explained`): the program explained.
import Series07.ws4
-- WS5 — the limit-atomlessness loophole (`ws5_limit_reintroduces_leaves`), adjudicated import-in-time.
import Series07.ws5
-- WS6 — the heuristic ceiling: the provable core mechanized, the universal reported heuristic.
import Series07.ws6
-- WS7 — the anti-circularity audit and the typed verdict (`payoffsEstablished`).
import Series07.ws7
