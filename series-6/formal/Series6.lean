-- `Series6` — the live Lean root (Spec Series 6).
--
-- Series 3 is closed and frozen under `archive/`; Series 4 and Series 5 are complete under
-- `series-4/` and `series-5/`. Series 6 asks whether a *process* over the honestly atom-free
-- carrier can be genuinely globally atomless AND plural, driven from within by the diagonal.
-- The charter (`series-6/charter.md`) and per-workstream designs (`series-6/spec/wsNN-design.md`)
-- specify it.
--
-- Series 6 is WHOLLY STANDALONE (charter §1): every Series 4/5 lemma it reuses is transcribed
-- into `series-6/formal/wsNN.lean` and re-namespaced `Series6.WSNN` — nothing is imported from
-- `series-5/`, `series-4/`, or `archive/`. Toolchain pinned as Series 4/5: Lean 4 `v4.15.0` /
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
import ws1
-- WS2 — the Static Collapse Theorem (`ws2_static_collapse`), escapes-are-imports
-- (`ws2_escapes_are_imports`), subsumptions, and the forced answer (obstructed on C2).
import ws2
-- WS3 — the engine: the residue IS the Cantor diagonal and the sole definiens of the successor
-- (`ws3_residue_is_diagonal`, `ws3_diagonal_drives`); the engine identity; the omega orbit.
import ws3
-- WS4 — the arrow: lossy survey / one-to-many residue, a strict order; the endogeneity FAILURE
-- (a first moment, imported depth axis).
import ws4
-- WS5 — relativity: agreement-is-collapse; the LAUNDERING finding (bare same-depth
-- incomparability); the Ω-absolute-frame branch (Newton = collapse, and Ω is not it).
import ws5
-- WS6 — the headline: incompleteness inherited, groundlessness-from-the-diagonal, no view from
-- nowhere; and the achievement as an Impossibility (`ws6_atomless_and_plural_impossible`).
import ws6
-- WS7 — the anti-trivialization audit and the typed program verdict (`payoffsEstablished`).
import ws7
