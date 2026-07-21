# Program 2 Series 4 (2.4), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: B (design). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN. This is the first series of Phase 2 (the physics of the built universe, `charter-extension.md`).*

---

## 0. Snapshot

- **Phase:** A complete (charter committed). B (design) COMMITTED — six design files (`spec/README.md`, `spec/ws1-design.md`…`ws5-design.md`) as one batch, no `formal/` file yet (Phase B gate held). **Precondition:** Series 2.3 has landed (SHAPE-DRAWN, program verdict CONSTRUCTED-AND-WALLED).
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The imported chain (`P2S3`, `P2S2`, `P2S1`, `P2S0`, `P1`) is built and registered, reaching all lower layers transitively.
- **Axiom state:** the imported layers are axiom-clean on the standard three. Series build N/A.
- **Gate state:** green upstream. S4's `formal/` will import `P2S3` only (gate `(P2S3|P2S4)`), reaching S2/S1/S0/P1 transitively.
- **Costume gate (Phase-2 discipline):** PASSES at charter — the knot is AXIS-BUILDING (a new lateral axis), not import-powered. The multiplicity of peers is Series 07 (the acknowledged ground); the verdict must rest on axis-independence, verified at Phase F (audit c).
- **Open SERIOUS findings:** none. Phase C returned two SERIOUS (C1-S1, C1-S2), both closed **Fixed** by rename in Phase D; a fresh-seed Phase C re-run is pending to confirm zero SERIOUS.

## 1. The carrier — the world (built here) on the imported chain

**S4 stands on the imported chain** (`program-2/series-3`, namespace `P2S3`, reaching `P2S2` / `P2S1` / `P2S0` / `P1` transitively) and its working material is chiefly the Series 2.0 attention carrier and the Series 2.2 lateral texture. Unlike prior series, S4 BUILDS its main carrier — the world — as WS1, and that world is the shared ground the rest of Phase 2 inherits. The pieces S4 builds on:

| Carrier piece | Where |
|---|---|
| The attention carrier `attends`, directed knowing, `outDest`, `rankLift`, reification rank | `P2S0` (transitive) |
| The knowing-asymmetry (makes the metric directed): `ws3_direction_not_recoverable` | `P2S0` (transitive) |
| The lateral texture: incomparable reaches, same-rank peers (`slf`/`p`/`q` at rank 0) | `P2S2` (transitive) |
| Collapse engine, recoverability test, the seated import | `P1.Core` / `P2S0.ws4` (transitive) |
| **The world** (a genuine lateral population of same-rank import-distinguished peers, local attention graph) | **built at S4 WS1** |

**Design note (PX-1 discharged):** the Series 2.2 twoness was tower/rank-based (base-and-rung). The world S4 builds is exactly the PX-1 lift — same-rank import-distinguished peers rather than a rung — and 2.4 is where the program tests whether that lateral multiplicity is real (DISTINCT) or collapses (REDUCED).

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_lateral_extent`, `ws1_peers_non_recoverable`, `ws1_not_collapsed` (a genuine lateral world, real extent, not a tower) | OPEN | — |
| WS2 | `ws2_lateral_step_no_rank`, `ws2_reify_no_lateral` (the axes come apart) | OPEN | — |
| WS3 | `ws3_lateral_is_import` (Series 07), directed + granular + self-relative metric | OPEN | — |
| WS4 (the knot) | `ws4_two_axes` (independent axes, both moves witnessed, REDUCED reachable, no fiat, no costume) | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO ABSOLUTE FRAME — no proof term asserts a distance frame-independently; every metric claim is FOR a self; a global metric is claimed only where forced. UNVERIFIED.
- (b) THE FORK NOT BY FIAT — REDUCED genuinely reachable, both a lateral-move-without-rank and a rank-move-without-lateral witnessed, the verdict discriminating. UNVERIFIED.
- (c) THE KNOT IS NOT THE MULTIPLICITY (the costume gate) — the verdict rests on axis-independence, not on the import-powered existence of many. UNVERIFIED.
- (d) SPACE IS AN IMPORT — `ws3_lateral_is_import` a proof term resting on Series 07. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| C1-S1 | C | SERIOUS | `ws1_world_is_lateral` def-name embeds forbidden content-name "world" (audit e) | **Fixed** — renamed `ws1_lateral_extent` (no forbidden word; "lateral" is a strip-word, not on the §6 grep list). Same proposition. |
| C1-S2 | C | SERIOUS | `ws5_audit_space_import` def-name embeds forbidden content-name "space" (audit e) | **Fixed** — renamed `ws5_audit_lateral_import`. Same proposition (`¬ Recoverable (latLiftW hinf)`). |
| C1-S3 | C | REAL | `ws5_audit_names_not_terms : True` is a bare placeholder; cannot itself enforce audit (e) | Addressed — kept as the accepted house pattern (S2/S3 precedent); docstring clarified that (e) is a meta-property about identifiers, ENFORCED by the §6 mechanical grep at Phase E, not by this `True`. |
| C1-S4 | C | COSMETIC | `ws3_granular` first conjunct `reachIn 0 x y ↔ x = y` is definitionally trivial | Noted; kept — it documents the discrete floor (step 0 = identity); the second conjunct (a least positive step) is genuine, so the theorem is non-vacuous. |

## 5. Deviations from charter (disclosed)

- **2026-07-21 (Phase D, from C1-S1/C1-S2).** Two of the charter's provisional target names embedded forbidden content-words and were renamed to neutral identifiers (the charter permits this; §2 target table updated): `ws1_world_is_lateral → ws1_lateral_extent`, and the audit clause `ws5_audit_space_import → ws5_audit_lateral_import`. Propositions unchanged; only the identifiers changed. No narrowing of any target — the same facts are proved under neutral names.

No target narrowing between charter and design. Any narrowing between design and build will be disclosed here at the moment it happens.

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.4 adds none and closes none; it draws the self-relativity of space sharper.

## 7. Phase log

- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.4 established as SPACE, the first shake of Phase 2: build THE WORLD (a genuine lateral population of same-rank import-distinguished peers with a local attention graph) as the ground, define two gradings (a directed granular self-relative breadth-distance, and reification depth), prove the axes come apart (WS2) and the lateral separation is an import (WS3, Series 07), and at the knot prove the two-axes fork DISTINCT with REDUCED genuinely reachable, no fiat and no costume (the knot on axis-independence, not on multiplicity). No distance asserted absolutely. Costume gate passes at charter (axis-building). Scaffold (`spec/`, `formal/`) to be created at Phase B. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build. Weigh the candidate witness world (a lateral ring/graph of same-rank peers with local, possibly directed attention, plus a reified element to witness the vertical axis).
- **2026-07-21 — Phase B.** Six design files committed as one batch before any `formal/` file (Phase B gate held): `spec/README.md` (imported chain, shared witness, discipline, triage, outcomes, module layout) and `spec/ws1-design.md`…`spec/ws5-design.md`. The shared witness is fixed: the WORLD `W = Fin 4` (a directed 3-ring of same-rank peers `w0/w1/w2` at rank 0 plus a reified peer `r` at rank 1) with two gradings `rankW` (vertical) and `latW` (lateral coordinate), and the collapsed TOWER `T = Fin 3` where `latT = rankT` (REDUCED realized). The crux is the cross-pattern of separations: `latW` separates `(w0,w2)` where `rankW` does not, and `rankW` separates `(r,w0)` where `latW` does not, so neither grading is a function of the other (axis-independence, the finding — audit c), while REDUCED is genuinely reachable on `T` (no fiat — audit b). The breadth metric is path-grounded via a length-indexed `reachIn` on the LOCAL (non-complete) graph, self-relative from `w0` (audit a, d). `P2S4` module naming fixed (`P2S4.lean` imports `P2S4.ws1`…`ws5`; `ws1` imports `P2S3`; `AxiomCheck` root); registration deferred to Phase E per protocol. Next: Phase C, blind design review on the signatures only.
- **2026-07-21 — Phase C (design review, blind, delegated).** Generated `spec/blind-seed-C.md` (self-contained, neutral framing: the two carriers, the signatures, mechanical success criteria, audit a–e, strip test + forbidden names, rubric). Spawned a blind `general-purpose` reviewer pointed at the seed ONLY; it certified blindness (read exactly that one file). It worked every finite computation by hand and CONFIRMED them: the cross-pattern (`latW` separates `(w0,w2)` where `rankW` does not; `rankW` separates `(r,w0)` where `latW` does not) is genuine and load-bearing, `latT = rankT` on `T` is a real coincidence witness, `verdict` is non-constant, `reachIn` grounds `latW` as the shortest path from `w0`. Audit (a)–(d) all found SATISFIED, pressing hardest on (c): "Not a costume" — the DISTINCT verdict rests on the cross-pattern, not on multiplicity. Findings: **C1-S1, C1-S2 SERIOUS** (two def-names embed forbidden content-words "world"/"space"); **C1-S3 REAL** (the `True` names-audit placeholder); **C1-S4 COSMETIC** (a trivial conjunct). See the ledger.
- **2026-07-21 — Phase D (design repair).** Closed both SERIOUS findings by the 2a binary as **Fixed** (rename, same proposition): `ws1_world_is_lateral → ws1_lateral_extent`, `ws5_audit_space_import → ws5_audit_lateral_import`. Addressed C1-S3 by clarifying the names-audit docstring (the meta-property is enforced by the §6 grep, not by the `True`). Noted C1-S4. Updated `spec/ws1-design.md`, `spec/ws5-design.md`, and the §2 target table. Next: re-run Phase C with a fresh seed; the fixes are pure renames, so a zero-SERIOUS pass is expected.
