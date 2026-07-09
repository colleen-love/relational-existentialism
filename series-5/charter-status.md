# Relational Existentialism — Series 5: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: the charter is the stable statement of intent, edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds. When you want to know "what does Series 5 claim," read the charter. When you want to know "where is Series 5," read this. (Series 4 introduced this split after Series 3 let REV-A…REV-H amendments pollute its charter inline; Series 5 keeps the discipline.)*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success) · **Partial** (part proved, obstruction made precise) · **Failed** (not achieved, documented why) · **Trivialized** (the WS7-only verdict: the §5.4 unification turned out definitional — a success, a sharp negative about the conjecture) · **Not started**.
- **Coincidence status** (charter §7, the coincidence rule): for each §5.4 payoff, whether the definitional form and an independently forced form were separately proved and shown to coincide. Values: **Coincidence proved** · **Definitional-only** (cheap form holds, forced form open) · **N/A** (no cheap form) · **Pending**.
- **Design status** (Series 5 batching): because designs are created as a batch before any build (see `protocol.md` §2), each workstream first reaches **Design committed** before it can reach any proof status. A workstream that is **Design committed / Not built** has a stable contract but no Lean.
- **Naming discipline** (inherited): a bundle is named by its parts, never `*_resolved` / `series5_resolved`, while any hole remains.
- **Anti-laundering discipline** (charter §5.4/§6, inherited from Series 4 review 2): every payoff carries a *strip test* — delete "face"/"view"/"level" from the statement and check whether it still goes through as a bare index fact. A payoff that survives the strip is an index fact honestly flagged, not an earned carrier theorem. The strip-test column is load-bearing for WS3/WS4/WS6/WS7.
- Every claim of "sorry-free / axiom-clean" is provisional until a machine-checked `#print axioms` against the pinned Lean/Mathlib is recorded. **As of status v2 the build is complete and the `#print axioms` output is committed in [`spec/axiom-check-log.md`](./spec/axiom-check-log.md)** (all headline theorems on `propext` / `Classical.choice` / `Quot.sound`).

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v5 — full build (Phase C) + **pass 1 addressed** (Phase E) + **S1 charter-§9 refactor completed** (Phase F: universe-poly `Tower` + `cardinalTower` discharges the flagship-payoff antecedent) + **pass 2 addressed** (Phase G: derivation count corrected to one, V3/graded-law/forced-answer relabelled, axiom log regenerated) + **pass 3 clean** (no SERIOUS finding; V3 distinct-face form recorded as open #14; series can close). No mathematics changed after Phase F; `payoffsEstablished` stands. |
| **Design docs** | `series-5/spec/ws01…ws07-design.md` + `README.md` — **committed**. Each: 3–7 candidate framings with Lean signatures + ambient theory + success/failure conditions, a paper-decidable triage collapsed to a table, the winner developed into a full mathematical design. |
| **Formalization** | **BUILT.** `ws1.lean … ws7.lean`, `Series5.lean`, `AxiomCheck.lean` — self-contained (closure gate confirms nothing imported from `series-4/` or `archive/`), pinned Lean 4.15.0 / Mathlib v4.15.0. `lake build` green; `#print axioms` on every headline theorem shows only `propext` / `Classical.choice` / `Quot.sound` — **recorded in [`spec/axiom-check-log.md`](./spec/axiom-check-log.md)** (closes the S3 "static, not shown" finding). Two in-build design fixes (WS1) + honest scopings recorded per workstream. |
| **Central question** (charter §8) | **The split answer landed as forecast, and the tower existential is now DISCHARGED (S1 closed, charter-§9 refactor complete).** Boundlessness-without-a-wall (WS3), groundless-no-collapse plurality (WS4), cross-level leak-free relating (WS6) survive their strip tests — and now hold of a **genuinely built** doubly-unbounded object: `Tower` was made universe-polymorphic (`Idx : Type w`, `Winf : Type (max u w)`) and `cardinalTower : Tower.{u, u+1}` (index `Cardinal.{u} × ℤ`, connected by the constructed `boundRelax` injective legs) **satisfies `DoubleUnboundedness`** (`ws7_cardinalTower_du`), so the payoffs hold with **no open antecedent** (`ws7_notop_unconditional`, `ws7_payoffs_unconditional`). The C2 pre-registration (comment: "a proper class / large directed set"; charter §9: "the tower existential needs a proper-class index") is now realized, not just named: `ws7_setindexed_walls` / `ws7_no_du_tower` carry the honest `[Small.{u} T.Idx]` scope (the collapse is a fact about *small* indices, which `cardinalTower`'s index escapes). Poles / naive-no-view / attention are index facts / laundering / Trivialized, as forecast. |
| **Headline positive (built, unconditional)** | Explosion Dilemma (WS2, Impossibility) · no strict graded distributive law (WS6, Impossibility, KS diagonal) · `nuLk_card_ge` (labelled Lambek + Cantor) · leak-free cross-level composition (WS6, floor-free via ℤ) · the ℤ index facts · the distinctness anchors · **the colimit gate SETTLED with a real non-degenerate tower (`ws1_gate_settled`: `boundRelax` injective legs + `growingTower`)** · **the doubly-unbounded tower BUILT (`cardinalTower : Tower.{u, u+1}`, `ws7_cardinalTower_du`) — so the flagship payoffs hold of a real object with no open antecedent (`ws7_notop_unconditional`, `ws7_payoffs_unconditional`)** · the §4.1 collapse mechanized as a fact about *small* indices (`ws7_setindexed_walls`, now `[Small.{u} T.Idx]`). |
| **Headline (formerly S1-conditional, now discharged)** | `ws3_no_top`, `ws3_wall_vs_grain`, `ws4_no_completing_view`, `ws7_payoffs_hold`, `ws7_notop_from_du`, the anchors — all take `DoubleUnboundedness`, which **`cardinalTower` now satisfies** (`ws7_cardinalTower_du`). The unconditional instances `ws7_notop_unconditional` / `ws7_payoffs_unconditional` apply them to that built tower. The C2 fix was pre-registered (charter §9: proper-class / universe-bumped index) and is now realized in `Tower.{u,w}` + `cardinalTower`. |
| **Signature risk** | Trivialization — **refuted**: three payoffs survive strip; leak-freeness is a demonstrated second fact (`ws7_leakfree_NOT_from_du`); three anchors refute `trivialized`; and the payoffs now hold of a genuinely built doubly-unbounded object, not a mere conditional. The whole-program adjudication no longer waits on the tower existential (S1 closed). Verdict `payoffsEstablished` stands. |
| **Blocking item** | **None open.** WS1 colimit gate — DISCHARGED and SETTLED (`ws1_bisim_eq_colim` + `boundRelax`/`boundRelax_injective`/`growingTower`/`ws1_gate_settled`). The doubly-unbounded **index** (the one remaining tower open, register #1b) — DISCHARGED by the charter-§9 universe-bump refactor: `Tower` is now `Tower.{u,w}` with `Idx : Type w`, `Winf : Type (max u w)`, and `cardinalTower` (proper-class index `Cardinal.{u} × ℤ`) satisfies `DoubleUnboundedness`. |
| **Verdict (WS7)** | **`payoffsEstablished`.** `ws7_verdict_eq`/`ws7_not_trivialized`/`ws7_not_one_du` are correct about the inductive `ProgramVerdict`; `ws7_verdict_eq` is a `rfl` definitional check (pass-1 R4 / pass-2 C1). The payoffs hold of a **constructed** object — `ws7_payoffs_unconditional` applies the four payoffs to `cardinalTower`, whose `DoubleUnboundedness` is proved (`ws7_cardinalTower_du`). **Honest derivation count (pass-2 S1): one, not two** — only no-top genuinely derives from double-unboundedness; descent (`ws7_descent_nofirst_on_spine`) is the no-first-level index fact on a spine, not a derivation. The label stands (anchors + the leak-free second fact carry it). |

---

## Workstream status

*All seven are **Built** as of status v1 (Phase C). The rows below record the committed design contract and the **outcome as built** (with any honest scoping), so a review session knows both the target and what the code actually delivers.*

### WS1 — The tower and its colimit  ·  *blocking*
**Status: Built — gate discharged.** · Carrier decision: **C2** (ordinal-cofinal directed colimit with bound-relaxing inclusions). Contract in `spec/ws01-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| Colimit exists (directed system) | `ws1_colim_equiv` (D1) | **Discharged** (directed colimit; four `ι` laws via `le_refl`/`le_trans`/`directed`) |
| **The colimit gate** (existential) | `destInf` + `ws1_bisim_eq_colim` (D2) | **Discharged** — `destInf` realized as the representative-independent successor set `succSet` (the `Σ' a, …` codomain is not `Quot.lift`-definable; **design fix**); `ws1_bisim_eq_colim` via level-local `nuLk_bisim_eq` + `toColim` injective legs |
| Ω recovered with honest local bound | `ws1_omega_selfloop` + `ws1_local_bound` (D3) | **Discharged** |
| Connecting maps exist (the §9 existential) | `boundRelax` + `boundRelax_injective` + `growingTower` + `ws1_gate_settled` (built) | **SETTLED.** The bound-relaxing *injective coalgebra morphisms* between different-cardinal `νLk` are **constructed** (via terminality); `growingTower` (strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`, real non-`id` legs) witnesses a genuine non-degenerate tower — so the gate holds of a real object, not just `constTower`. The charter-§9 "most likely single point of failure" discharged. |
| Doubly-unbounded **index** exists (the §9 proper-class refactor) | `Tower.{u,w}` (universe-poly `Idx : Type w`, `Winf : Type (max u w)`) + `cardinalTower` + `ws7_cardinalTower_du` (built) | **DISCHARGED (register #1b closed).** `cardinalTower : Tower.{u, u+1}` has proper-class index `Cardinal.{u} × ℤ` (lex order: no greatest / cofinal cardinals via `Cardinal`, no least via `ℤ`), the same `boundRelax` legs, and **satisfies `DoubleUnboundedness`** — so the flagship payoffs hold of it unconditionally (`ws7_payoffs_unconditional`). The pre-registered C2 fix, realized. |

*As built:* the gate reduces to the level-local `nuLk_bisim_eq` (labelled-carrier bisimulation-is-identity, derived from Mathlib `Cofix.bisim_rel`) plus injectivity of the colimit legs — exactly the design's reduction. Two Lean-realization fixes were required (both recorded in the Closed log, neither weakening a target): `succSet` for `destInf`, and an explicit bound-relaxation `LkRelax` in the `ι_dest` law. The colimit-functor `F_∞` fallback was **not needed** (WS6's graded law is stated on a standalone graded carrier, not on one `F_∞`).

### WS2 — The explosion, and the forced answer  ·  *the spine*
**Status: Built — Impossibility + Discharged, no-first-level Partial (definitional).** · Index decision: **`ℤ`** (I1). Contract in `spec/ws02-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| Explosion Dilemma | `ws2_explosion_dilemma` (E1) | **Impossibility proved** (both horns transcribed: `ws4_no_top_cardinal` + `ws5_global_groundless_collapses`) |
| Supremum defeats §4.1 | `ws2_supremum_walls` (E3) | **Discharged** (cardinal wall at `⨆ n, κ n`) |
| Index: no least / no greatest / self-dual | `ws2_no_least`, `ws2_no_great`, `ws2_self_dual` | **Discharged** (`omega` facts; self-duality via `n ↦ -n : ℤ ≃o ℤᵒᵈ`) |
| No first level, earned | `ws2_no_atom_floor` | **Partial — definitional** (built as the index form `no-least ⇒ strictly-lower level`; the *carrier* descent is owed to WS6 — open obligation #2, exactly as pre-registered) |
| Provenance dichotomy (F2) | `Boundless` + `ws2_forced_answer` | **Discharged as a dichotomy over a stipulated 2-case type only** (pass-2 R5): `ws2_forced_answer` is `cases` over the two constructors of `Boundless` (`rfl`/`trivial`) — it does *not* force the answer or prove essential-uniqueness (that every boundless-and-plural construction *is* a tower), which stays open #3. `WallsByFiat` / `CardinalValuesChosen` are `:= True` report-flags, not characterizations. Read as *dichotomy-by-provenance* |

*As built:* the Dilemma is the conjunction of two transcribed Series 4 theorems; the `ℤ` order facts are `omega` one-liners. `ws2_no_atom_floor` is honestly **definitional** at the index level — the descending carrier map that would earn it is WS6's (still open #2).

### WS3 — Boundlessness without a wall
**Status: Built — B2 discharged, survives strip.** · **Coincidence duty:** single-level wall vs tower grain (`ws3_wall_vs_grain`). Contract in `spec/ws03-design.md`.

| Obligation | Target | Outcome (built) · strip test |
|---|---|---|
| No global cap | `ws3_no_global_cap` (B1) | **Discharged** (from WS2 unbounded cardinals) · *index fact, kept as lemma* |
| **No object relates to everything** | `ws3_no_top` (B2) | **Discharged** · **survives strip** — the escaping object is produced at a higher level `β` (from `hunb`), needing `nuLk_card_ge` at `β`; delete no-last-level and there is no `β`. Carries a `Nonempty Q` hypothesis (needed for `nuLk_card_ge`) |
| Bound is the grain | `ws3_bound_is_grain` (B3) | **Discharged** (interpretive corollary; simplified from the design's `IsGlobalCapOf` plumbing to the conjunction it packages) |
| Coincidence: wall vs grain | `ws3_wall_vs_grain` | **Coincidence proved** (single-level fiat `ws4_no_top_cardinal_at` ∧ tower grain `ws3_no_top`) |
| Face-counting wall (B4) | `ws3_faces_cannot_bound` | **Impossibility (inherited)** — faces cannot bound branching (`carrier_card_ge`); Series 5 dissolves, does not solve |

*As built:* the load-bearing new machinery is labelled-carrier terminality + Lambek giving `nuLk_card_ge : κ ≤ #(νLk κ Q)` (for `Nonempty Q`) and per-level `toColim` injectivity — these make the higher-level escaping object real, so no-last-level is genuinely load-bearing (survives the WS7 strip test).

### WS4 — No first, no last: poles and the view from nowhere  ·  *two severe coincidence duties*
**Status: Built — A2 earned; V3 earned as no-top-positional (face inert, #14); V2 demoted; poles an index fact.** · **Forward edge to WS6 resolved** (imports WS6's `ViewAt`/`FaceReaches`/`ws6_tower_unknowable`). Contract in `spec/ws04-design.md`.

| Obligation | Target | Outcome (built) · strip test |
|---|---|---|
| Unbounded above / below | `ws4_unbounded_above/below` (A1) | **Discharged** · *bare index facts, kept as lemmas* (+ `ws4_unbounded_above/below_int` for `ℤ`) |
| **Groundless, no collapse** | `ws4_groundless_no_collapse` (A2) | **Discharged** · **survives strip** — plurality survives the colimit (two distinct faced loops, `toColim` injective) ∧ the single-carrier collapse anchor. *Descent* conjunct deferred to WS6's graded spine (open #2) |
| Coincidence: singly-bounded collapses | `ws4_singly_bounded_collapses` | **Impossibility** (transcribed `ws5_global_groundless_collapses`) |
| Poles coincide (self-dual index) | `ws4_poles_coincide` (P1) | **Discharged for `ℤ`** · **fails strip** — index fact; philosophical reading flagged interpretation |
| Poles split (lopsided) | `ws4_poles_split` (P2) | **Typed honest alternative** (`ℕ`: a least, no greatest) |
| View is positioned | `ws4_view_is_positioned` (V1) | **Discharged (definitional `rfl`)** — simplified to "a view is at a level" (the design's `viewOf = faceAt` is heterogeneously typed across the bound level) |
| No view from nowhere, naive | `ws4_no_view_from_nowhere` (V2) | **LAUNDERS** — built as `ws2_no_least ∧ ws2_no_great`, a bare order fact — **recorded, NOT a payoff** |
| **No completing view** | `ws4_no_completing_view` (V3) | **Discharged as no-top read positionally** (= `ws6_tower_unknowable` = `ws3_no_top` at `toColim v.obj`; `FaceReaches` = `RelatesInf`, `ViewAt` wrapper inert). Pass-3 R-WS4/6: the face is **not** load-bearing — V3's genuine gain over Series 4 is that no-top is now forced by no-last-level, not a distinct face-reach mechanism. The distinct-face form is open #14 |

*As built:* V2 (index-only) launders and is honestly demoted; V3 (a view's face misses an object at a higher level, via `ws3_no_top`) is the earned no-view — but **its content is no-top's, not the face's** (pass-3 R-WS4/6: `FaceReaches` = `RelatesInf`, so stripping the face leaves `ws3_no_top` intact; the face wrapper is inert). Its real gain over Series 4 is that no-top is now forced by no-last-level, not a fiat κ; the distinct-face-mechanism form the design promised is open #14. The WS4↔WS6 cycle is broken by having WS6 own `ViewAt`/`FaceReaches`/`ws6_tower_unknowable` and WS4 re-export V3.

### WS5 — The self-bounding of the world, revisited  ·  *the "grain not wall" thesis*
**Status: Built — grain-not-wall tower-wide, residual fiat reported.** Contract in `spec/ws05-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| M1 / M2 negatives stand | `ws5_contraction_insufficient`, `ws5_quotient_insufficient` | **Impossibility** (standing, unrefuted — about the wrong locus) |
| M3 global collapse stands | `ws5_global_groundless_collapses` | **Impossibility** — exactly the hypothesis the tower avoids |
| Endogenous, tower-wide | `ws5_endogenous_tower` (G1) | **Discharged** (conjoins `ws1_local_bound` + `ws3_no_global_cap` + standing M1) |
| Earned adjudication | `ws5_stratification_frees_bound` (G2) | **Coincidence proved** (single-carrier bound ∧ tower freedom, of different objects) |
| Off-spine improper-face route (G3) | `ws5_selfface_trivial` | **Rejected** — self-face trivial (empty or improper); endogeneity comes from between-levels, not from extending the spine |
| Residual fiat, honest report | `UnboundednessForced` / `CardinalValuesChosen` / `ws5_residual_fiat` (G4) | **Partial (honest report)** — necessity of unboundedness earned (WS2); particular cardinal values chosen |

*As built:* G1/G2 are conjunctions of already-established facts — the content is in the *statement* (pairing the standing M1 negative with the recovered tower freedom), as the design intends. G3's rejection is mechanized via `ws5_selfface_trivial`.

### WS6 — Relating across levels, and attention as grade-shift  ·  *the deepest technical risk*
**Status: Built — leak-free + DL1 impossibility; DL2 delivered as a grade-shift coherence (not a distributive law, pass-2 R4 / #13); relating=composition definitional (#12); attention Trivialized.** · Grade decision: **GF1** (inert `ℤ`-label). Contract in `spec/ws06-design.md`.

| Obligation | Target | Outcome (built) · coincidence |
|---|---|---|
| **Cross-level leak-freeness** | `ws6_crosslevel_never_annihilate` (A/GF1) | **Discharged** · `ws3_faces_never_annihilate` instantiated at `Q := GLabel Q` verbatim; floor-free because `ℤ` has no bottom |
| Descent non-terminating | `ws6_descent_nonterminating` (B) | **Discharged** (from `ℤ` no-least) — stated for a **constructed descending spine** `descState`, not `∀ x` (false in general); honestly exhibits that groundless descent exists and never bottoms out |
| Relating-to = composed-of | `ws6_relating_is_composition` (B) | **NOT a coincidence — duty OPEN** (`Iff.rfl` on one identical definition; S2b, register #12) |
| Incompleteness inherited | `ws6_lawvere_incomplete`, `ws6_omega_nonterminating` (INC1) | **Discharged** (carrier-independent, transcribed) |
| Tower unknowable (new) | `ws6_tower_unknowable` (INC2) | **Discharged** (via `ws3_no_top` on the view's object) — **its content *is* no-top read positionally** (`FaceReaches` = `RelatesInf`; no independent face-reach argument), pass-2 R1 |
| Coincidence: unknowable = no-view | `ws4_unknowable_eq_noview` (in WS4) | **One theorem BY CONSTRUCTION** (`rfl` on an alias — V3 defined as INC2; S2a — not a proved coincidence) |
| Attention as grade-shift | `attend` (AT1) | **Definable; Trivialized** — no coincidence with an independent attention notion (AT2 replicator / AT3 convergence) on this carrier, the predicted honest negative |
| No strict graded law | `ws6_no_strict_graded_law` (DL1) | **Impossibility** (transcribed KS four-set diagonal, grade-inert) |
| Graded observation-coherent shift | `ws6_graded_obs_coherent_shift_exists` (DL2) | **Discharged as a coherence, NOT a distributive law** (pass-2 R4): renamed from `GradedWeakDistLaw`/`ws6_graded_weak_law_exists` — `GradedObsCoherentShift` is a `ℤ`-bijection commuting with observation `LkMap`, carrying **none** of the `DistLaw` monad laws. The genuine graded weak *distributive law* (Egli–Milner `λ` commuting with observation *and* grade) is **OPEN** (register #13). The inert-`ℤ` payoff is real; the "distributive law" name was retired |

*As built:* choosing `ℤ` pays off twice — leak-freeness transports verbatim (grade inert under `lcomp`), and grade-shift is a `ℤ`-bijection commuting with observation (DL2). Three honest downgrades vs the design's prediction: **`ws6_relating_is_composition` is definitional-only** (not a genuine two-relation `↔`, #12), **the DL2 positive is a grade-shift coherence, not a distributive law** (pass-2 R4, the genuine weak law is #13), and **attention is Trivialized** (as predicted). Lemma B (convergence) stays open.

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Built — verdict `payoffsEstablished`.** Contract in `spec/ws07-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| The single fact | `DoubleUnboundedness` + `ws7_double_unboundedness` (F1) | **Discharged** (no least/greatest + unbounded cardinals) |
| **The single fact holds of a BUILT tower (S1 discharged)** | `cardinalTower` (WS3) + `ws7_cardinalTower_du` | **Discharged.** `cardinalTower : Tower.{u, u+1}` (proper-class index `Cardinal.{u} × ℤ`) satisfies `DoubleUnboundedness` — the charter-§9 refactor complete; `ws7_setindexed_walls`/`ws7_no_du_tower` now honestly scoped `[Small.{u} T.Idx]` |
| **Payoffs of the built tower (no open antecedent)** | `ws7_notop_unconditional`, `ws7_payoffs_unconditional` | **Discharged.** The four payoffs of `ws7_payoffs_hold` applied to `cardinalTower` with its own `DoubleUnboundedness` witness — no `hunb` hypothesis left standing |
| Payoffs hold (a conjunction) | `ws7_payoffs_hold` (T2) | **Discharged as a conjunction only** (not a derivation — Series 4 R1 discipline) |
| Genuine derivation from double-unboundedness | `ws7_notop_from_du` | **One derivation** (pass-2 S1): no-top genuinely derives (consumes the unbounded-cardinals conjunct, runs the `ws3_no_top` cardinality argument). Descent (`ws7_descent_nofirst_on_spine`, renamed from `ws7_descent_from_du`) is **NOT** a second derivation — it does not take `DoubleUnboundedness`; it is the no-first-level *index* fact on the `descState` spine. Honest count: one derivation, one second fact, anchors |
| Counterweight: leak-freeness is a second fact | `ws7_leakfree_NOT_from_du` | **Discharged** — leak-freeness holds unconditionally *and* the walled `constTower` is not doubly-unbounded, so it is genuinely a second fact |
| Distinctness anchors | `ws7_notop_vs_collapse_distinct`, `ws7_tower_vs_carrier_distinct`, `ws7_poles_vs_notop_distinct` (T3) | **Discharged — 3 mechanized rows** (Series 4 managed 2) |
| Typed verdict | `ProgramVerdict` + `ws7_verdict` (T4) | **`payoffsEstablished`** — `ws7_not_one_du` (reduction partial), `ws7_not_trivialized` (anchors refute); `ws7_verdict_eq` = `rfl` |
| Anti-laundering ledger | doc-comment (per-file strip-test notes) | The triage collapsed into the verdict decision |

*As built:* the verdict lands deterministically at the honest middle — **one** payoff derives from double-unboundedness (no-top), **one** is a demonstrated second fact (leak-freeness, witnessed by the constant tower), descent is the no-first-level index fact on a spine (not a derivation, pass-2 S1), three distinctness anchors refute trivialization; and the antecedent now holds of a built tower (`ws7_payoffs_unconditional`). `ws7_not_trivialized` / `ws7_verdict_eq` depend on *no* axioms. The pass-1 ledger's "two derivations" is corrected to one — the label `payoffsEstablished` is unchanged (the anchors and the second fact carry it).
*Self-audit disclosure:* Claude-auditing-Claude (charter §9); the distinctness anchors are the objective part.

---

## The §5.4 payoffs — headline tracker

*The charter's central question is whether stratification earns, relocates, or relabels each payoff. As built (Phase C) + review-pass-1 relabelled (Phase E) + **S1 discharged (Phase F)**. **Update:** the former "conditional (S1)" caveat is lifted — `cardinalTower` (`ws7_cardinalTower_du`) is a genuinely built doubly-unbounded tower, so the tower payoffs are earned *of a constructed object* (`ws7_payoffs_unconditional`), not just of the antecedent.*

| Payoff (charter §5.4) | Workstream | Verdict (built) · strip test | Coincidence |
|---|---|---|---|
| Boundlessness without a wall | WS3, WS4 | **Earned, of a built tower** — `ws3_no_top` survives strip (higher level supplies escaping object); holds of `cardinalTower` with no open antecedent (`ws7_notop_unconditional`) | **Proved** (`ws3_wall_vs_grain` — two genuine proofs; the one honest coincidence) |
| Groundlessness without collapse | WS4, WS5 | **Partial** — `ws4_groundless_no_collapse` proves *plurality* (unconditional, survives strip) + the single-carrier collapse anchor; the *descent* half is deferred to WS6's bespoke spine (R2/R3), not on `Winf T` | Proved (`ws4_singly_bounded_collapses`) |
| Cross-level relating, leak-free | WS6 | **Earned, unconditional** (transported verbatim; floor-free via ℤ) | **OPEN** — `ws6_relating_is_composition` is `Iff.rfl` on one definition (S2b), *not* a coincidence; identification duty unmet |
| Poles coincide at the layer level | WS4 | **Index fact** (order self-duality; fails strip) — reading flagged interpretation | N/A (index property) |
| No view from nowhere, forced | WS4 | **V2 launders** (demoted); **V3 = no-top read positionally** (pass-2 R1): `ws4_no_completing_view` is `ws3_no_top` through `FaceReaches` = `RelatesInf`, *not* a distinct mechanism; its genuine gain over Series 4 is that no-top is now forced by no-last-level, not by a fiat κ. Holds of `cardinalTower` (`ws7_payoffs_unconditional`) | **One theorem by construction** (`ws4_unknowable_eq_noview` is `rfl` on an alias — S2a; V3 *defined as* INC2, not a proved coincidence) |
| Incompleteness (inherited + tower) | WS6 | **INC1 earned, unconditional** (transcribed); **INC2 (`ws6_tower_unknowable`) earned given the built tower** (holds of `cardinalTower`'s `DoubleUnboundedness`) | One theorem by construction (S2a) |
| Attention as grade-shift | WS6, WS7 | **Trivialized** — definable, coincidence negative on this carrier | Definitional-only → Trivialized |
| Plurality preserved | WS3 | **Earned, unconditional** (survives the colimit by `toColim_level_inj`) | N/A |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Statuses updated after the Phase C build; a review pass (Phase D) audits the closures.*

1. **The colimit gate** — WS1. **CLOSED, and SETTLED with a real witness.** `ws1_bisim_eq_colim` (level-local `nuLk_bisim_eq` + injective legs) + `ws1_colim_equiv` + `ws1_local_bound`, built; `destInf` realized as `succSet` (design fix). The charter-§9 "most likely single point of failure" — the *existence* of bound-relaxing injective coalgebra-morphism connecting maps — is now **constructed** (`boundRelax`, `boundRelax_injective`) and assembled into a genuine non-degenerate tower `growingTower` (strictly increasing cardinals), witnessed by `ws1_gate_settled`. The gate no longer rests only on the abstract `Tower` with assumed fields or the degenerate `constTower`.
1b. **The doubly-unbounded `Tower` inhabitant** — WS1. **CLOSED (the pre-registered §9 refactor, completed Phase F).** Review pass 1 (S1) traced this to a design under-implementation: the C2 candidate's *comment* says "a proper class / large directed set with no greatest element" and charter §9 says "the tower existential needs a proper-class index," but C2's own Lean *sketch* (and this file's original `Tower`) typed `Idx : Type u`, collapsing it. The refactor is now done: `Tower` is `Tower.{u,w}` (`Idx : Type w`, `Winf : Type (max u w)`, `ws3_no_top` reproved universe-generically), and **`cardinalTower : Tower.{u, u+1}`** — proper-class index `Cardinal.{u} × ℤ` (lex order), same `boundRelax` injective legs — **satisfies `DoubleUnboundedness`** (`ws7_cardinalTower_du`: no greatest / cofinal cardinals via `Cardinal` + Cantor, no least via `ℤ`). So the flagship payoffs hold of it with no open antecedent (`ws7_notop_unconditional`, `ws7_payoffs_unconditional`). `ws7_setindexed_walls`/`ws7_no_du_tower` retain the honest `[Small.{u} T.Idx]` scope (the §4.1 collapse is a fact about *small* indices, which `cardinalTower`'s index provably escapes); `ws7_properclass_index_cofinal` remains as the index-level statement. Axiom-clean (standard three).
2. **No-first-level earned, not posited** — WS2/WS6. **OPEN (Partial — definitional).** `ws2_no_atom_floor` built at the *index* level only; the descending *carrier* map (WS6) is not built, so no-first-level is definitional. Trigger-to-close: a cross-level descending edge into `W_b` on the tower carrier. (WS6's `descState` gives a descending spine on the standalone graded carrier, not yet on `Winf T`.)
3. **Essential-uniqueness of the forced answer** — WS2. **OPEN (heuristic).** `ws2_forced_answer` dichotomy built; "every boundless-and-plural construction *is* a doubly-unbounded tower" remains defended-but-not-proved (charter §9), as Series 4 did.
4. **Cross-level leak-freeness transports** — WS6. **CLOSED.** `ws6_crosslevel_never_annihilate` = `ws3_faces_never_annihilate` at `Q := GLabel Q`, verbatim; floor-free because `ℤ` has no bottom.
5. **Graded observation-coherent shift (DL2)** — WS6. **CLOSED as a coherence** (pass-2 R4 relabel — was "graded weak distributive law", which over-claimed). `ws6_graded_obs_coherent_shift_exists` : `Nonempty (GradedObsCoherentShift κ Q)` — `gradeShiftStr` is a `ℤ`-bijection commuting with observation (GF1), carrying none of the `DistLaw` monad laws. No strict law (`ws6_no_strict_graded_law`, Impossibility) alongside. The genuine graded weak *distributive law* is #13.
6. **No-view earned, not laundered** — WS4. **CLOSED with an honest scope** (see #14). V3 (`ws4_no_completing_view`) is the earned no-view, but pass-3 R-WS4/6 established its content is `ws3_no_top`'s, not the face's (`FaceReaches` = `RelatesInf`, wrapper inert); the genuine gain over Series 4 is that no-top is now forced by no-last-level, not a fiat κ. V2 (`ws4_no_view_from_nowhere`) demoted, recorded as the bare order fact. The distinct-face-mechanism form is open #14.
7. **Poles coincide or split** — WS4. **CLOSED (index fact).** `ws4_poles_coincide` for `ℤ` (flagged interpretation, fails strip); `ws4_poles_split` the typed lopsided alternative.
8. **Attention coincidence** — WS6/WS7. **OPEN → Trivialized.** `attend` definable; neither AT2 (replicator) nor AT3 (Lemma B convergence) lands on this carrier. Reported **Trivialized** — a success per §7 (the predicted honest negative). Lemma B stays open.
9. **Tower-unknowable = no-view, adjudicated** — WS6/WS4. **CLOSED (answer: one theorem, by construction).** `ws4_unknowable_eq_noview` (`rfl` on an alias — V3 := INC2); not a proved coincidence, but the "one or two?" duty is legitimately answered "one" (S2a).
10. **The verdict and the distinctness anchor** — WS7. **CLOSED.** `ws7_verdict = payoffsEstablished` with 3 mechanized distinctness rows and per-file strip-test notes.
11. **Machine-checked axiom pass** — all. **CLOSED (evidence committed).** `AxiomCheck.lean` output recorded in [`spec/axiom-check-log.md`](./spec/axiom-check-log.md); every headline theorem on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`/`admit`/`axiom`/`native_decide`-free. Closes review finding S3.
12. **Genuine `relating = composed-of` coincidence** — WS6. **OPEN (was mislabelled definitional-only).** Per S2b: `RelatesAtGrade` and `IsComposedOfAtGrade` are the *same* definition, so `ws6_relating_is_composition` (`Iff.rfl`) is **not** a coincidence. Trigger-to-close: a genuinely separate composition-side relation built from `lcomp` (design Part-B "one from `destInf`, one from `lcomp`"), proved `↔` the observation side.
13. **Genuine graded weak distributive law** — WS6. **OPEN (pass-2 R4).** `ws6_graded_obs_coherent_shift_exists` delivers a grade-shift bijection commuting with observation (`GradedObsCoherentShift`), *not* a distributive law `λ : T F ⇒ F T` carrying the `DistLaw` monad laws (charter §5.5, "the deepest technical risk": composition-as-algebra and observation-as-coalgebra cohering across levels). Trigger-to-close: build an Egli–Milner-style `λ` commuting with observation *and* grade, with the bialgebra laws, and prove it exists (or prove it cannot, dissolving DL2). The impossibility DL1 (`ws6_no_strict_graded_law`) stands regardless.
14. **A distinct-face-mechanism no-view (V3), not no-top read positionally** — WS4/WS6. **OPEN (pass-3 R-WS4/6).** `ws4_no_completing_view` is `ws3_no_top` at `toColim T v.obj` (`FaceReaches` = `RelatesInf`, the `ViewAt` wrapper inert), so its content is no-top's, not an independent face-reach argument — relabelled honestly in code and the tracker (pass-2 R1). Its genuine gain over Series 4 is that no-top is now forced by no-last-level (`hunb`), not by a fiat κ; the *distinct-mechanism* form the WS4 design promised (a face-reach object with its own `< κ_α` and finite-descent bounds, missing an object by a face argument not reducible to `ws3_no_top`) is **not** built. Trigger-to-close: build that object and prove it, or keep V3 reported as "no-top positional; earned content is no-top's, forced by no-last-level." Criterion (vii) is *partially* met: no-view is forced by no-last-level, but the "facing structure is load-bearing" sub-clause is not.

**Residual opens after Phase G / pass-3 (the honest outcome):** register **1b CLOSED** in Phase F (the doubly-unbounded tower is built — `cardinalTower` + `ws7_cardinalTower_du`). Remaining opens: **#2** (no-first-level definitional — the descending *carrier* map on `Winf T` is still owed; this is also the pass-2 S1 point: descent is the index fact on the spine, not a derivation), **#3** (essential-uniqueness heuristic — `ws2_forced_answer` classifies a stipulated 2-case type, pass-2 R5), **#8** (attention Trivialized), **#12** (relating=composition coincidence), **#13** (the genuine graded weak distributive law — the DL2 positive delivered is a grade-shift coherence, pass-2 R4), **#14** (a distinct-face-mechanism no-view — V3 is no-top read positionally, pass-3 R-WS4/6). **The split the design forecast held, and now unconditionally:** carrier/face-load-bearing payoffs survive their strip tests *and* hold of a genuinely built doubly-unbounded tower; index-reducible ones are flagged. **Pass 3 (`spec/project-review-3.md`) is a clean pass — no SERIOUS finding**, the six items above are correctly-labelled terminal Partials / "prove-that" obligations, and none of them the headline depends on. The honest headline is **earned of a constructed object**: `payoffsEstablished` stands, the tower is genuinely built, and the sharp negatives (Explosion Dilemma, no strict law) are real.

---

## Closed log

### [build pass, Phase C] WS1–WS7 built — full `sorry`-free, axiom-clean compile

All seven `formal/wsNN.lean` + `Series5.lean` + `AxiomCheck.lean` compile; `#print axioms`
records only `propext` / `Classical.choice` / `Quot.sound` on every headline theorem. The
closure gate confirms self-containment (no import from `series-4/` or `archive/`).

**Design fixes made in-build (Phase C, per protocol §2 Phase C — recorded, target not weakened):**
- **WS1 `destInf` codomain.** The design typed `destInf : Winf T → Σ' a, LkObj κ_α Q (Winf T)`.
  That `Σ'` codomain is **not** `Quot.lift`-definable: the level index `α` depends on the
  representative, so two representatives of one colimit point give unequal `⟨a,_⟩`. Realized
  faithfully as the representative-independent successor **set** `succSet : Winf T → Set (Q × Winf T)`
  (well-defined via `ι_dest`); the honest local `< κ_α` bound is recovered separately as
  `ws1_local_bound`. No target weakened — the gate and no-top consume `succSet`/`RelatesInf`.
- **WS1 `ι_dest` bound-relaxation.** The design's `lstr (ι h x) = LkMap (ι h) (lstr x)` is
  ill-typed (`LkObj κ_α` vs `LkObj κ_β` differ by the cardinality predicate). Realized as
  `lstr (ι h x) = LkRelax (mono h) (LkMap (ι h) (lstr x))`, an explicit inclusion that is the
  identity on the underlying set — exactly the design's "relaxes the bound" prose.

**Honest scopings recorded (per workstream):**
- **WS2 `ws2_no_atom_floor`** — delivered as the **index form** (`no-least ⇒ strictly-lower level`);
  the *carrier* descent (a face descending into `W_b`) is owed to WS6 (open obligation #2), so
  no-first-level is **definitional pending WS6** exactly as pre-registered.
- **WS3 no-top** carries a `Nonempty Q` hypothesis (needed for `nuLk_card_ge`; without labels
  `νLk κ ∅` is a point). Honest and necessary; `Q` is plural anyway for the plurality payoff.
- **WS4 V1 (`ws4_view_is_positioned`)** simplified to "a view is at a level" (`rfl`); the design's
  `viewOf = faceAt` form is heterogeneously typed across the bound level. V1 is definitional, as
  the design already flags. **V2 (`ws4_no_view_from_nowhere`)** is recorded as `ws2_no_least ∧
  ws2_no_great` — the laundering form, **not** a payoff. **V3 (`ws4_no_completing_view`)** is the
  earned payoff (= `ws6_tower_unknowable`), with `ws4_unknowable_eq_noview` the one-theorem coincidence.
- **WS4 `ws4_groundless_no_collapse`** delivers the earned halves — plurality survives the colimit
  (strip-surviving) ∧ the single-carrier collapse anchor — and defers the tower-carrier *descent*
  (every object has a strictly finer relatum) to the WS6 graded spine `descState` /
  `ws6_descent_nonterminating` (open obligation #2).
- **WS6 `ws6_relating_is_composition`** delivered **definitionally** (`Iff.rfl`); the genuine
  two-definition coincidence is the open residue (as the design's coincidence duty (i) anticipates).
- **WS6 attention (`attend`)** is **definable and reported Trivialized** — no coincidence with an
  independent attention notion (AT2 replicator / AT3 convergence) on this carrier, the design's
  predicted honest negative.
- **WS6 descent** is stated for a **constructed descending spine** (`descState`), not `∀ x : Winf T`
  (which is false in general — not every object descends forever); this honestly exhibits that
  groundless descent *exists* and never bottoms out (uses `ℤ` no-least load-bearingly).

**Payoff verdicts as built (matching the §5.4 tracker):** boundlessness-without-a-wall **earned**
(`ws3_no_top` survives strip — higher level supplies the escaping object); groundless-no-collapse
**earned** (`ws4_groundless_no_collapse` via object plurality + the single-carrier collapse anchor);
cross-level leak-free **earned** (`ws6_crosslevel_never_annihilate`, transported verbatim, floor-free
via `ℤ`); no strict distributive law **Impossibility** (`ws6_no_strict_graded_law`, KS diagonal);
graded observation-coherent shift **Discharged** (`ws6_graded_obs_coherent_shift_exists` — a grade-shift coherence, *not* a distributive law; genuine weak law open #13, pass-2 R4); Explosion Dilemma **Impossibility**
(`ws2_explosion_dilemma`); poles **index fact** (`ws4_poles_coincide`, flagged interpretation) with
lopsided alternative (`ws4_poles_split`); no-view V2 **laundering / demoted**, V3 **earned as no-top-positional** (face inert, #14);
attention **Trivialized**; verdict **`payoffsEstablished`**.

- Axiom check: **run** against the pinned build; all headline theorems on the standard three.
- Charter touched? **No** — status-only; the charter design is unchanged (the two WS1 fixes are
  Lean-realization corrections of ill-typed/undefinable design sketches, recorded here, not
  target changes).

---

*Earlier note (superseded): the design batch was committed but unbuilt. Entries land here as builds pass review.*

*Template for future entries:*

<!--
### [date] WSn reported — Status: {Discharged | Impossibility proved | Partial | Failed | Trivialized}
- Discharged: {theorems}
- Impossibility proved: {theorems, why they count as success}
- Open / routed: {obligation → owning workstream}
- Coincidence: {proved | definitional-only | N/A}
- Strip test: {which payoffs survived, which are index facts}
- Methodology note: {correction or hand-off, if any}
- Axiom check: {run against pinned build | static | owed}
- Charter touched? {no — status-only | yes, and why the design itself needed a fix}
-->

---

## Series-review log

*Series 5 batches review at the whole-series level (see `protocol.md` §2–§3): a review session reads all built code against all design contracts and charter criteria, blind to motivating prose, and writes `series-review.md`; a code session addresses it; repeat. This log indexes those passes.*

- **Phase C (build-all)** complete: `ws1…ws7` built, `sorry`-free and axiom-clean.
- **Phase D pass 1** (`spec/project-review-1.md`): 3 SERIOUS (S1 conditional payoffs / no-witnessed-model tower; S2 coincidence-rule `rfl`s; S3 static axiom check), 5 REAL (R1–R5), plus ACCEPTABLE + clean-survivors.
- **Phase E pass 1 (addressed, this session):**
  - **S1 — traced to a pre-registered design point, mechanized both ways, relabelled.** S1's conditional-payoffs gap is the charter-§4.1/§9 obstruction the design *already named*: C2's comment specifies "a proper class / large directed set," charter §9 says "the tower existential needs a proper-class index," but C2's Lean sketch (and this file's `Tower`) typed `Idx : Type u`, collapsing it. Mechanized both sides: `ws7_setindexed_walls` (`Type u` index → supremum wall), `ws7_no_du_tower` (`¬ DoubleUnboundedness` for any present tower), and **`ws7_properclass_index_cofinal`** (the pre-registered `Type (u+1)` index *does* satisfy the unbounded-cardinals condition, via Cantor). Snapshot / payoff tracker / register #1b relabelled to **Partial (conditional on the pre-registered §9 proper-class-index refactor)** — not a lowered bar and not a Series 6 pivot, but Series 5's own pre-registered fix, still owed as a universe-bump refactor of `Tower`/`Winf`.
  - **S2a/S2b — relabelled.** `ws4_unknowable_eq_noview` docstring: one theorem *by construction* (V3 := INC2), not a proved coincidence. `ws6_relating_is_composition` + `IsComposedOfAtGrade` docstrings: `Iff.rfl` on one definition, identification duty **OPEN** (register #12), removed from the coincidence column of the payoff tracker.
  - **S3 — closed with evidence.** `spec/axiom-check-log.md` commits the `#print axioms` output + build/gate result (register #11 genuinely CLOSED).
  - **R1–R5 — kept as correctly-labelled Partials / relabels** (no-first-level definitional; descent on a bespoke spine; `ws4_groundless_no_collapse` reports plurality+anchor, descent deferred; verdict scope conditional; `CardinalValuesChosen := True` is a prose report, not a characterization). GradedWeakDistLaw's "not full distributivity" caveat noted (design-scoped DL2).
- **No SERIOUS finding remains open:** S2/S3 were relabelled/closed in Phase E; **S1 is now CLOSED in Phase F** — the tower inhabitant is built (`cardinalTower` + `ws7_cardinalTower_du`), the pre-registered §9 universe-bump refactor of `Tower`/`Winf` carried out, and the flagship payoffs discharged of a constructed object (`ws7_payoffs_unconditional`). What was a non-terminal Partial is now a genuine closure, within Series 5, exactly as pre-registered — never a Series 6 pivot.
- **Gate settled (follow-up to S1, prior session).** Prompted by the charter-§9 pointer ("Most likely single point of failure; settled first"), the gate's genuine existential — the *existence* of bound-relaxing injective coalgebra-morphism connecting maps — was constructed: `boundRelax` (terminal-morphism into the larger `νLk`), `boundRelax_injective` (via `nuLk_bisim_eq`), `boundRelax_refl`/`boundRelax_trans` (functoriality), assembled into `growingTower` (strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`) and witnessed by `ws1_gate_settled`. The gate now holds of a genuine non-degenerate tower, not just the abstract `Tower` or the degenerate `constTower`. Axiom-clean (standard three). **This is the gate ("settled first") the charter flags as the program's most likely single point of failure — discharged with a real object.**
- **Phase F — the S1 charter-§9 refactor COMPLETED (this session).** The one remaining SERIOUS mathematical gap (register #1b, the doubly-unbounded *index*) is now closed by building the pre-registered proper-class-indexed tower, not merely naming it:
  - **`Tower` made universe-polymorphic.** `Tower.{u,w}` with `Idx : Type w` (was `Type u`); `Winf : Type (max u w)` (was `Type u`, which silently forced `w ≤ u` — the very collapse). `ws3_no_top` reproved universe-generically (the escaping-object cardinality argument now injects `carrier β ↪ ↥(lstr y).1` entirely within `Cardinal.{u}`, avoiding any cross-universe `#(Winf T)` comparison).
  - **`cardinalTower : Tower.{u, u+1}` built** (WS3): proper-class index `Cardinal.{u} × ℤ` under the lexicographic order, levels at `max ℵ₀ c`, connected by the same `boundRelax` injective legs. `ws7_cardinalTower_du` proves it satisfies `DoubleUnboundedness` — no greatest index / cofinal cardinals via the `Cardinal` coordinate + Cantor, no least via the `ℤ` coordinate.
  - **Payoffs discharged.** `ws7_notop_unconditional` and `ws7_payoffs_unconditional` apply `ws3_no_top` / `ws7_payoffs_hold` to `cardinalTower` with its own `DoubleUnboundedness` witness — the flagship payoffs now hold of a genuinely built object with **no open antecedent**. S1's "sound conditionals; subject not yet built" is answered: the subject is built.
  - **Honest scoping retained.** `ws7_setindexed_walls` / `ws7_no_du_tower` now carry `[Small.{u} T.Idx]`: the §4.1 supremum collapse is a theorem about *small*-indexed towers (`constTower`, `growingTower`), and `cardinalTower`'s index is provably not `u`-small — so there is no contradiction, exactly as intended. `ws7_properclass_index_cofinal` stays as the index-level lemma.
  - All new theorems axiom-clean (`propext` / `Classical.choice` / `Quot.sound`); `spec/axiom-check-log.md` updated. Full `lake build` green.
- **Phase D pass 2** (`spec/project-review-2.md`): re-reviewed the Phase-F build blind. **1 SERIOUS (S1, a relabel), 5 REAL (R1–R5), 4 COSMETIC, S3 carried (process).** The pass explicitly confirms the headline stands: "the doubly-unbounded tower is genuinely built … `ws7_notop_unconditional` / `ws7_payoffs_unconditional` discharge the flagship antecedent against a constructed object — the pass-1 S1 'sound conditional, no subject' is genuinely closed." No finding asks for a lowered bar; every correction is a relabel of a name/description that overreads a proof term, plus the two genuine open proofs (#2, #13) that would *earn* what is currently posited.
- **Phase G — pass-2 addressed (this session).** All relabels applied; no mathematics changed, `payoffsEstablished` unchanged, full `lake build` green:
  - **S1 (SERIOUS, relabel) — derivation count corrected to one.** `ws7_descent_from_du` → **`ws7_descent_nofirst_on_spine`**: it does not take `DoubleUnboundedness` and is the no-first-level *index* fact on the `descState` spine, not a derivation. The WS7 module header, the `ws7_verdict` docstring, the WS7 block, the snapshot verdict row, and the payoff ledger now read "**one** derivation (no-top) + **one** second fact (leak-free) + anchors." Verdict label stands (anchors + second fact carry it). To *earn* a second derivation: open #2 (the carrier-level descent on `Winf T`).
  - **R1 (REAL, relabel) — V3 is no-top read positionally.** `ws4_no_completing_view` / `ws6_tower_unknowable` docstrings and the payoff tracker now state that `FaceReaches` = `RelatesInf` and the content is exactly `ws3_no_top`; the genuine gain over Series 4 is that no-top is now forced by no-last-level, not a distinct face-reach mechanism.
  - **R4 (REAL, rename) — the DL2 positive is a coherence, not a distributive law.** `GradedWeakDistLaw` → **`GradedObsCoherentShift`**, `ws6_graded_weak_law_exists` → **`ws6_graded_obs_coherent_shift_exists`** (a `ℤ`-bijection commuting with observation, carrying no `DistLaw` monad laws). The genuine graded weak distributive law is new open obligation **#13**; the impossibility DL1 stands.
  - **R5 (REAL, docstring) — placeholder Props flagged.** `ws2_forced_answer` docstring: it classifies the stipulated 2-case `Boundless` type (does not force the answer / prove essential-uniqueness, open #3). `WallsByFiat` / `CardinalValuesChosen` marked `:= True` report-flags, not characterizations.
  - **S3 (process) — axiom log regenerated.** `spec/axiom-check-log.md` re-emitted against the Phase-F + pass-2 build (2026-07-09) via `lake env lean … AxiomCheck.lean`, including the new/renamed theorems; every headline theorem on the standard three (or none). Closes the pass-2 "committed, not re-verified" standing.
  - **R2/R3 (REAL) and C1–C4 (COSMETIC)** were already correctly labelled — kept: #2 (no-first-level definitional), #12 (relating=composition `Iff.rfl`), the typed verdict as a summary label, the two WS1 design fixes, `Nonempty Q`, `ColimBisim`'s common-level.
- **Phase D pass 3** (`spec/project-review-3.md`): regenerated blind against the Phase-F + pass-2 build. **No SERIOUS finding.** Verdict confirmed: "`payoffsEstablished` stands, honestly earned; the tower is genuinely built; the sharp negatives (Explosion Dilemma, no strict law) are real." The strip tests were re-run independently: no-top **earns** its face (fails when `hunb` is deleted — the pass condition); the built doubly-unbounded tower is confirmed real ("the single most important thing that changed since pass 1"); no laundering found. One REAL relabel owed and now applied — **R-WS4/6**: V3 no-view is no-top read positionally (the `ViewAt` wrapper is inert), which was already relabelled in code/tracker (pass-2 R1); recorded here as explicit open obligation **#14** (the distinct-face-mechanism form). The pass also carried **S-AX** (axiom emit "static, not re-run" — the review environment lacked the toolchain); this is *already discharged*: the log was re-emitted against the addressed build in Phase G (S3) via `lake env lean … AxiomCheck.lean`. The remaining REAL items (#2, #3, #8, #12, #13) are the same correctly-labelled terminal Partials / open proofs. Exit criterion met: no SERIOUS remains; the series can close.
- *Series 5 status: closed at `payoffsEstablished` with a genuinely built doubly-unbounded tower. The honest remaining ledger is the "prove-that" obligations #2 (carrier descent), #12 (composition-side relation), #13 (graded weak distributive law), #14 (distinct-face no-view), the heuristic #3, and the terminal Trivialized #8 — none required to keep the verdict.*

*Template:*

<!--
### [date] Series-review pass N — series-review.md written / addressed
- Findings raised: {S# serious, R# real, C# cosmetic}
- Addressed in build pass N: {what changed, relabel vs fix}
- Reopened workstreams: {WS#}
- Charter touched? {no — status-only}
-->

---

## Charter-change log

*Distinct from workstream progress: this logs edits to `charter.md` itself. The charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress. Each entry: what changed, why it was a design error and not a status update, and the date.*

- **REV-0 (initial):** charter created; no changes. All seven workstream design docs drafted under `spec/wsNN-design.md` and committed this session.

---

*Status file v0. Maintained alongside `charter.md` (stable), `protocol.md` (the process), and `spec/wsNN-design.md` (per-workstream designs). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem; keep review passes in the Series-review log and charter edits in the charter-change log, both out of the workstream progress. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
