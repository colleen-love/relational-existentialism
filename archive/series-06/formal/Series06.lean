-- `Series06` — the live Lean root (Spec Series 06).
--
-- Series 03 is closed and frozen under `archive/`; Series 04 and Series 05 are complete under
-- `series-04/` and `series-05/`. Series 06 asks whether a *process* over the honestly atom-free
-- carrier can be genuinely globally atomless AND plural, driven from within by the diagonal.
-- The charter (`series-06/charter.md`) and per-workstream designs (`series-06/spec/wsNN-design.md`)
-- specify it.
--
-- Series 06 is WHOLLY STANDALONE (charter §1): every Series 04/05 lemma it reuses is transcribed
-- into `series-06/formal/wsNN.lean` and re-namespaced `Series06.WSNN` — nothing is imported from
-- `series-05/`, `series-04/`, or `archive/`. Toolchain pinned as Series 04/05: Lean 4 `v4.15.0` /
-- Mathlib `v4.15.0`. The full build compiles `sorry`-free with no custom axioms; every result
-- rests only on Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`),
-- recorded by `AxiomCheck.lean`.
--
-- HEADLINE (the honest verdict; see `charter-status.md`). The central result is a sharp
-- NEGATIVE that counts as success (charter §7/§8): the naive stagewise process `Proc` over the
-- finite founded-approximation carrier does NOT escape the Static Collapse. Each `Approx κ n` is
-- finite and hereditary non-emptiness forces a unique value, so Ω is the UNIQUE productive
-- thread (`WS1.ws1_productive_unique`) and productive plurality is impossible
-- (`WS1.ws1_no_productive_plurality`, `WS6.ws6_atomless_and_plural_impossible`). What IS earned:
-- the Static Collapse Theorem (WS2), the genuinely diagonal-driven engine (WS3), the lossy
-- survey / one-to-many residue and a strict arrow (WS4), agreement-is-collapse (WS5),
-- groundlessness-from-the-diagonal and no-view-from-nowhere (WS6), and the typed verdict
-- `payoffsEstablished` (WS7). Genuine atomless plurality, the endogenous arrow, and earned
-- relativity are owed to the richer carrier home (metric C4 / guarded).

-- WS1 — the carrier `Proc`, Ω, productivity, and the gate: Ω is the unique productive thread
-- (`ws1_productive_unique`), so productive plurality is impossible (`ws1_no_productive_plurality`).
import Series06.ws1
-- WS2 — the Static Collapse Theorem (`ws2_static_collapse`), escapes-are-imports
-- (`ws2_escapes_are_imports`), subsumptions, and the forced answer (obstructed on C2).
import Series06.ws2
-- WS3 — the engine: the residue IS the Cantor diagonal and the sole definiens of the successor
-- (`ws3_residue_is_diagonal`, `ws3_diagonal_drives`); the engine identity; the omega orbit.
import Series06.ws3
-- WS4 — the arrow: lossy survey / one-to-many residue, a strict order; the endogeneity FAILURE
-- (a first moment, imported depth axis).
import Series06.ws4
-- WS5 — relativity: agreement-is-collapse; the LAUNDERING finding (bare same-depth
-- incomparability); the Ω-absolute-frame branch (Newton = collapse, and Ω is not it).
import Series06.ws5
-- WS6 — the headline: incompleteness inherited, groundlessness-from-the-diagonal, no view from
-- nowhere; and the achievement as an Impossibility (`ws6_atomless_and_plural_impossible`).
import Series06.ws6
-- WS7 — the anti-trivialization audit and the typed program verdict (`payoffsEstablished`).
import Series06.ws7
