# Program 2 Series 5 (2.5), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: COMPLETE (Exit criteria met). Current verdict: **ACYCLIC** (`ws5_verdict_eq : verdict true true true true false = Outcome.acyclic`, by `rfl`), confirmed by the blind code review (Phase F, zero SERIOUS). The build is sorry-free, axiom-clean (standard three), gate-green, names-grep clean; audits (a)–(e) VERIFIED. This is the second series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE LOOP: closed time, on the fold as its ground — the relating loops but time does not.*

---

## 0. Snapshot

- **Phase:** COMPLETE. Exit criteria met: Phase F returned zero SERIOUS; build sorry-free, axiom-clean, gate-green; names grep clean; the WS5 verdict computes ACYCLIC; every SERIOUS finding closed (none). Summaries written. **Precondition:** Series 2.4 landed (DISTINCT, including Charter Extension 1).
- **Verdict:** ACYCLIC (computed by `rfl`, `ws5_verdict_eq`; to be confirmed at Phase F).
- **Build state:** `formal/P2S5` built — `P2S5.lean` (aggregator), `P2S5/ws1.lean`…`ws5.lean`, `P2S5/AxiomCheck.lean`. Imports `P2S4` only, reaching `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively. Registered in `lake/lakefile.toml` (target `P2S5`, in `defaultTargets`) and `scripts/gate.sh`.
- **Axiom state:** every payoff reduces to Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`) or none, via `AxiomCheck`. No `sorry`.
- **Gate state:** GREEN including `program-2/series-5` (`^import (P2S4|P2S5)…`).
- **Names grep (§6):** CLEAN — every hit of the forbidden-word grep is docstring/comment prose; no declaration or identifier is a forbidden whole word.
- **Costume gate (Phase-2 discipline):** PASSES — the knot is DIAGONAL/CYCLE-powered (the coexistence of cyclic relating and acyclic time, and the fold's uniqueness), not import-powered, and NOT rank-well-foundedness alone. `verdict` returns `acyclic` only with `relatingCycles` AND `loopedReachable` true. To be confirmed at Phase F (audit c).
- **Open SERIOUS findings:** none (design review returned zero SERIOUS; code review pending).

## 1. The carrier — the fold on the imported chain

**S5 stands on the imported chain** (`program-2/series-4`, namespace `P2S4`, reaching `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively). Its working material is chiefly the Series 2.1 tick/causation and the P1 diagonal. Like S4, it builds its topological object — the fold — fresh. The pieces S5 builds on:

| Carrier piece | Where |
|---|---|
| The tick and causation: `ws4_causal_order_endogenous` (reification raises rank), the reification rank | `P2S1` (transitive) |
| The cycle-reification: `ws1_cycle_reifies` (a attends b attends c attends a reifies) | `P2S0` / `P2S1` (transitive) |
| The diagonal (makes the fold): `ws2_residue_free`, `ws1_no_self_total_hold`, the residue | `P1.Reader` (transitive) |
| Collapse engine, recoverability, atomlessness (no leaf, no smallest) | `P1.Core` / `P2S0` (transitive) |
| **The fold** (no poles; the largest bending into the smallest through the diagonal; Ω = {Ω} the seam) | **built at S5 WS1** |

**Design note (from `charter-extension.md` §4, 2.5):** poles/fold ALONE would be a corollary-assembly of already-proved facts (the K1/Bookkeeping trap at series scale). The weight sits on the LOOP (a genuine fork); the fold is its ground. This charter anchors there.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_no_pole_below`, `ws1_no_pole_above`, `ws1_reify_nonvacuous`, `ws1_fold`, `ws1_no_total_count` (the topology of the whole: no poles, the fold on the diagonal, the whole uncountable from within) | BUILT | Phase E (pending F) |
| WS2 | `ws2_relating_cycles` (attention genuinely cycles `p0 ⇄ p1` and reifies to `kA`) | BUILT | Phase E (pending F) |
| WS3 | `causalDep` (structural), `ws3_causal_rank_lift` (proved), `causation_acyclic`, `ws3_causation_acyclic` (no closed causal loop on the tick carrier) | BUILT | Phase E (pending F) |
| WS4 (the knot) | `loop_forces_selfloop`, `ws4_loop_only_at_fold` (the fold the sole candidate, on the diagonal), `ws4_no_fold_on_tower` (ACYCLIC), `ws4_looped_reachable` + `ws4_fold_no_rank` (LOOPED reachable, no fiat) | BUILT | Phase E (pending F) |
| WS5 | `verdict`, `ws5_verdict_eq` (= `acyclic` by `rfl`), `ws5_verdict_discriminates`, `ws5_flags_justified`, audit `ws5_audit_no_absolute_frame` / `_fork_genuine` / `_knot_is_coexistence` / `_fold_is_diagonal` / `_names_not_terms` (a–e) | BUILT | Phase E (pending F) |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason (and note the §6 forbidden-word grep: "time"/"loop"/"self"/"fold" etc. may not appear in identifiers).

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO POLES DECIDED ABSOLUTELY — the topology is stated structurally (no smallest = `SHNE`, no largest = the reification section, the fold), self-relative where a quantity is involved. **VERIFIED (`ws5_audit_no_absolute_frame`; Phase F).**
- (b) THE FORK NOT BY FIAT — LOOPED genuinely reachable (`ws4_looped_reachable`), causation's acyclicity proved from the rank-lift (`ws3_causal_rank_lift`, `causalDep` has no rank in its definition), the fold admitting no rank-lift (`ws4_fold_no_rank`), the verdict discriminating. **VERIFIED (`ws5_audit_fork_genuine`; Phase F).**
- (c) THE KNOT IS THE COEXISTENCE, NOT WELL-FOUNDEDNESS (the costume gate) — `verdict` returns `acyclic` only with `relatingCycles` AND `loopedReachable` true; it rests on cyclic-relating-with-acyclic-time and the fold's uniqueness, not on rank being well-founded alone. **VERIFIED (`ws5_audit_knot_is_coexistence`; Phase F, pressed hardest).**
- (d) THE FOLD IS THE DIAGONAL — `ws1_fold` and the second conjunct of `ws4_loop_only_at_fold` rest on the P1 diagonal (`ws2_residue_distinct` / `ws1_no_self_total_hold`), not on a seated import. **VERIFIED (`ws5_audit_fold_is_diagonal`; Phase F).**
- (e) NAMES-NOT-TERMS — the §6 grep is clean of forbidden content-names (hits are docstring prose only; no identifier is a forbidden whole word). **VERIFIED (Phase E grep + Phase F reviewer; `ws5_audit_names_not_terms` the placeholder).**

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| C1–C6 | C | PASS | Audit (a)–(e) and the strip test all pass; `verdict` gates `acyclic` on `relatingCycles` AND `loopedReachable` jointly (not well-foundedness alone), `causalDep` is structural (acyclicity proved), the fold rests on the diagonal, no identifier is a forbidden whole-word. | n/a (no defect) |
| C7-S1 | C | REAL | `ws5_flags_justified` prose overclaimed "exactly the WS1–WS4 propositions": the `loopOnlyAtFold` slot was justified by the rank-lift (WS3) rather than the genuine loop-forces-self-edge content, and WS1 enters via audit (d), not as a flag. | **(Fixed)** conjunct 3 of `ws5_flags_justified` rewired to `∀ x, TransGen causalDep x x → ∃ z, causalDep z z` (WS4, via `loop_forces_selfloop`); prose corrected to name WS1's entry point as audit (d) (`ws5_audit_fold_is_diagonal`, on `ws1_fold`). Not SERIOUS; no design re-review triggered. |
| C8-S1 | C | COSMETIC | `ws4_loop_only_at_fold` bundles two independent facts (rank localization + diagonal) under one name — the intended "fold." | Accepted (the bundling is the payoff). |
| C9-S1 | C | COSMETIC | WS1 payoffs are restatements/conjunctions of imported diagonal facts. | Accepted (restatement layer, non-vacuous). |
| F1–F(audits) | F | PASS | Blind CODE review: every signature proves EXACTLY its claimed type (no `sorry`/`axiom`/admitted hypothesis, none weaker than claimed, no circular appeal); audits (a)–(e) all pass, the hardest presses (c) knot-not-well-foundedness, (b) fork-not-fiat, (d) fold-is-diagonal, (e) names-grep, confirmed against the real proof terms; strip test survives on every payoff. | n/a (no defect) |
| F1-S1 | F | COSMETIC | `ws5_audit_names_not_terms := trivial` is a `True` placeholder. | Accepted (audit e is meta, enforced by the §6 grep, which passes). |
| F2-S1 | F | COSMETIC | `ws5_flags_justified` / `ws5_audit_no_absolute_frame` take an unused `hinf`/`κ`. | Accepted (matches the design signature; over-hypothesis only). |
| F3-S1 | F | COSMETIC | `transgen_rank_lt` grouped under WS4 in the seed but implemented in `ws3.lean`. | Accepted (location only; in scope via import, exact type proved). |
| F4-S1 | F | COSMETIC | `ws4_loop_only_at_fold` bundles two logically independent conjuncts. | Accepted (the intended "fold"; both survive the strip). |
| F5-S1 | F | COSMETIC | `ws5_flags_justified` feeds `loop_forces_selfloop` the distinct-edge lift discarding `t ≠ u`. | Accepted (sound; the rank-lift is strictly stronger, holding for all pairs). |
| G1-S1 | G (post-review bar-raise) | REAL | Costume-gate bar-raise: `ws5_audit_knot_is_coexistence` stripped to "(a cycle exists somewhere) ∧ (causation is acyclic)" — two independently-true facts, not the proven INTERACTION. "The relating loops but time does not" (the same cyclic edges carry no causation) lived only in WS2's docstring, not as a proof term. Literal audit (c) still passed (the verdict does require the cycle), so REAL not SERIOUS. | **(Fixed)** added `ws2_cycle_not_causal` (`ws3.lean`): the same `p0 ⇄ p1` edges carry no `causalDep` (`p0`, `p1` are `¬ isTick`), by `decide`; folded into `ws5_audit_knot_is_coexistence` so the coexistence is now the proven statement THIS LOOP IS NON-CAUSAL ∧ causation is acyclic. Verdict unchanged (ACYCLIC). Build re-verified sorry-free, axiom-clean, gate-green, names-grep clean. |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing between charter and design, or design and build, is disclosed here at the moment it happens.

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.5 adds none and closes none; it draws the shape of the whole and the acyclicity of time sharper.

## 7. Phase log

- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.5 established as THE LOOP, the second series of Phase 2: build THE FOLD (the topology of the whole — no smallest by atomlessness, no largest by unbounded reification, the largest bending into the smallest through the diagonal, the seam Ω = {Ω}, and the whole uncountable from within) as the ground; prove the relating genuinely cycles (WS2) yet causation is acyclic (WS3, on Series 2.1's rank-raising causation); and at the knot prove the sole candidate for a closed causal loop is the fold, forking ACYCLIC / LOOPED / SHAPE-DRAWN, no fiat and no costume (the knot on the coexistence of cyclic relating and acyclic time, not on rank-well-foundedness alone). Costume gate passes at charter (diagonal/cycle-powered). Scaffold (`spec/`, `formal/`) to be created at Phase B. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build. Weigh the witness: the Series 2.4 world (or a small cycle carrier) for the attention loop, a reification-dependency relation given structurally so its acyclicity is proved (not definitional), and a self-membered witness for the fold.
- **2026-07-21 — Phase B.** Design batch written and committed as one unit (`spec/ws1-design.md`…`ws5-design.md`, `spec/README.md`), before any `formal/` file (Phase B gate). Primitives fixed: the causal relation `causalDep attends comp t u := comp u ∧ t ∈ attends u` (a structural reification-dependency, NO rank in the definition, so audit (b) holds and acyclicity is proved not stipulated); the fold as the P1 diagonal (`ws1_no_self_total_hold` / `ws2_residue_distinct`, audit (d)). Two witnesses, both `Cardinal.{0}` on `Fin`: the tick carrier `TCar = Fin 7` (reached from `P2S1`) for the ACYCLIC zone (the relating cycles `p0 ⇄ p1` while `causalDep` strictly raises `rankT`, no self-membered composite), and the fold carrier `FCar = Fin 1` (fresh) for the LOOPED-reachable zone (a self-membered `om = {om}` gives a genuine causal self-loop admitting no rank-lift, so the fork is not by fiat). Verdict `verdict : Bool⁵ → Outcome`, `= acyclic` by `rfl`, discriminating, flags earned by the WS1–WS4 headlines; ACYCLIC demands the WS2 cyclic-relating flag AND the LOOPED-reachable flag, so the knot rests on the coexistence not on well-foundedness alone (audit c). All signatures VALIDATED against the compiler in a throwaway target (imports `P2S4`, sorry-free, axioms within the standard three) before commit, so Phase E builds to proven-buildable contracts. `P2S5` module naming fixed (Phase E registration recipe in `protocol.md`). Next: Phase C, generate `spec/blind-seed-C.md` and spawn a blind reviewer.
- **2026-07-21 — Phase C (design review, blind, delegated).** Generated `spec/blind-seed-C.md` (signatures, mechanical success criteria, audit checks a–e, strip test, forbidden-word list, rubric — no motivating prose). Spawned a blind `general-purpose` reviewer pointed at the blind seed ONLY; it confirmed reading no forbidden file. Verdict: ZERO SERIOUS. Audit (c) traced — `verdict` reaches `acyclic` only with `relatingCycles` AND `loopedReachable` true (not well-foundedness alone); audit (b) — `causalDep` structural, acyclicity proved, self-edge reachable; audit (d) — `ws1_fold` / `ws4_loop_only_at_fold` rest on the diagonal, no import; audit (e) — no identifier is a forbidden whole-word. One REAL (C7-S1), two COSMETIC. Findings recorded in §4.
- **2026-07-21 — Phase D (design repair).** C7-S1 closed **(Fixed)**: `ws5_flags_justified` conjunct 3 rewired from the rank-lift to the genuine WS4 proposition `∀ x, TransGen (causalDep attendsT isTick) x x → ∃ z, causalDep attendsT isTick z z` (loop forces a self-constituting relatum, via `loop_forces_selfloop`); `spec/ws5-design.md` prose corrected to name WS1's entry point as audit (d) rather than a verdict flag. C8/C9 accepted COSMETIC. No SERIOUS finding closed by a design edit, so no Phase C re-loop; Phase C passes with zero SERIOUS. Next: Phase E, write and register `formal/P2S5`.
- **2026-07-21 — Phase E (code).** Built `formal/P2S5` to the post-repair signatures: `P2S5.lean` (aggregator), `P2S5/ws1.lean`…`ws5.lean`, `P2S5/AxiomCheck.lean`, in the `P2S5` namespace, importing `P2S4` only. Registered the library in `lake/lakefile.toml` (added to `defaultTargets`) and the closure check in `scripts/gate.sh` (`^import (P2S4|P2S5)…`). WS1 the fold on the diagonal + the poles; WS2 the relating cycles; WS3 the structural `causalDep` with acyclicity PROVED from `ws3_causal_rank_lift`; WS4 `ws4_loop_only_at_fold` (bundling the rank localization with the diagonal) + `ws4_looped_reachable`/`ws4_fold_no_rank` (LOOPED reachable, no fiat); WS5 the computed verdict. §6 mechanical checks all pass: `lake build P2S5 P2S5.AxiomCheck` compiles; no `sorry`; `AxiomCheck` shows only the standard three axioms (or none); `scripts/gate.sh` green including S5; the forbidden-word grep hits are docstring prose only (no identifier is a forbidden whole word). Universe note: the general `{X : Type u}` payoffs (`ws1_fold`, `ws1_no_total_count`, `ws4_loop_only_at_fold`) auto-bind `κ` per-theorem rather than a section `variable`, so `κ` tracks `X`'s universe. **WS5 verdict COMPUTED: ACYCLIC** (`ws5_verdict_eq`, by `rfl`) — the relating loops but time does not; the fold is the sole loop candidate, unrealized on the genuine tower, its self-reference a degenerate fixed point (the diagonal). Next: Phase F, generate `spec/blind-seed-F.md` and spawn a blind code reviewer over `formal/`.
- **2026-07-21 — Phase F (code review, blind, delegated).** Generated `spec/blind-seed-F.md` (the signatures updated to the post-C7 `ws5_flags_justified`, plus the instruction to verify the CODE proves each type and to grep `formal/` for forbidden whole-words). Spawned a blind `general-purpose` reviewer pointed at the blind seed AND the `formal/` sources only; it confirmed reading no forbidden file. Verdict: ZERO SERIOUS, ZERO REAL. Every signature proves EXACTLY its claimed type (no `sorry`/`axiom`/admitted hypothesis, none weaker, no circular appeal); audits (a)–(e) all pass with the hardest presses (c)/(b)/(d)/(e) confirmed against the real proof terms; strip test survives on every payoff. Five COSMETIC notes (F1–F5), all sanctioned by the design (the `True` audit-(e) placeholder, unused `hinf`, a cross-file lemma location, the intended two-fact bundling, a discarded-but-sound `t ≠ u`). Findings recorded in §4.
- **2026-07-21 — Exit.** Phase F returned zero SERIOUS and the build is sorry-free, axiom-clean (standard three), gate-green, names-grep clean; the WS5 verdict computes ACYCLIC; audits (a)–(e) VERIFIED; every SERIOUS finding closed by the 2a binary (none arose). No Phase F re-loop (no SERIOUS closed by a code edit). Wrote `summary.md` and `summary-technical.md`. Series 2.5 is DONE: **THE LOOP — ACYCLIC. The relating loops but time does not; causation spirals up, and the sole seam where a causal loop could close, the self-membered fold, is a degenerate fixed point (the diagonal), while a genuine causal loop is shown reachable only on a separate posited carrier, so the acyclicity is earned, not stipulated.**
- **2026-07-21 — Post-review bar-raise (G1-S1).** A REAL costume-gate finding: `ws5_audit_knot_is_coexistence` had stripped to a bare conjunction of two independent facts (a cycle exists; causation is acyclic) rather than the proven interaction that the loop is the place causation is NOT. Closed **(Fixed)**: added `ws2_cycle_not_causal` (the `p0 ⇄ p1` cycle edges carry no `causalDep`, by `decide`, since `p0`/`p1` are `¬ isTick`) and folded it into audit (c), so the coexistence is now load-bearing — "the relating loops but time does not" is a proof term, not a docstring. `AxiomCheck` extended. Design (`ws5-design.md`) and summaries synced. Verdict UNCHANGED: ACYCLIC. §6 checks re-run: sorry-free, axiom-clean (standard three), gate-green, names-grep clean.
