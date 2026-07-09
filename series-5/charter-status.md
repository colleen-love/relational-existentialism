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
| **This status file** | v2 — full build (Phase C) + **blind review pass 1 addressed** (Phase E; `spec/project-review-1.md`). Headlines relabelled honestly per S1. |
| **Design docs** | `series-5/spec/ws01…ws07-design.md` + `README.md` — **committed**. Each: 3–7 candidate framings with Lean signatures + ambient theory + success/failure conditions, a paper-decidable triage collapsed to a table, the winner developed into a full mathematical design. |
| **Formalization** | **BUILT.** `ws1.lean … ws7.lean`, `Series5.lean`, `AxiomCheck.lean` — self-contained (closure gate confirms nothing imported from `series-4/` or `archive/`), pinned Lean 4.15.0 / Mathlib v4.15.0. `lake build` green; `#print axioms` on every headline theorem shows only `propext` / `Classical.choice` / `Quot.sound` — **recorded in [`spec/axiom-check-log.md`](./spec/axiom-check-log.md)** (closes the S3 "static, not shown" finding). Two in-build design fixes (WS1) + honest scopings recorded per workstream. |
| **Central question** (charter §8) | **Partial — the split answer landed as forecast, but conditional on a tower existential the present `Tower` encoding cannot satisfy (S1).** Boundlessness-without-a-wall (WS3), groundless-no-collapse (WS4), cross-level leak-free relating (WS6) survive their strip tests — **but as theorems conditional on `hunb`/`DoubleUnboundedness`, which `ws7_setindexed_walls` proves *no* present `Tower Q` satisfies**, because the `Tower` structure typed `Idx : Type u`, collapsing C2's *pre-registered* proper-class index (design C2 comment: "a proper class / large directed set"; charter §9: "the tower existential needs a proper-class index"). `ws7_properclass_index_cofinal` mechanizes that the pre-registered proper-class index *does* satisfy the condition. Poles / naive-no-view / attention are index facts / laundering / Trivialized, as forecast. |
| **Headline positive (built, unconditional)** | Explosion Dilemma (WS2, Impossibility) · no strict graded distributive law (WS6, Impossibility, KS diagonal) · `nuLk_card_ge` (labelled Lambek + Cantor) · leak-free cross-level composition (WS6, floor-free via ℤ) · the ℤ index facts · the distinctness anchors · **the colimit gate SETTLED with a real non-degenerate tower (`ws1_gate_settled`: `boundRelax` injective legs + `growingTower`, charter-§9 single-point-of-failure discharged)** · the §4.1 collapse mechanized both ways (`ws7_setindexed_walls` + `ws7_properclass_index_cofinal`). These need no tower *index* existential. |
| **Headline conditional (S1)** | `ws3_no_top`, `ws3_wall_vs_grain`, `ws5_endogenous_tower`, `ws4_no_completing_view`, `ws6_tower_unknowable`, `ws7_payoffs_hold`, `ws7_notop_from_du`, the anchors — all take `hunb`/`DoubleUnboundedness`, which no *present* `Tower Q` satisfies. **Sound conditionals; subject not yet built.** The fix is pre-registered (charter §9): a proper-class / universe-bumped index, shown to work at the index level by `ws7_properclass_index_cofinal`. |
| **Signature risk** | Trivialization — **refuted at the conditional level** (three payoffs survive strip; leak-freeness is a demonstrated second fact; three anchors refute `trivialized`). It **cannot** be adjudicated at the whole-program level until the tower is transported onto the pre-registered proper-class index (S1). Verdict scope is conditional (R4). |
| **Blocking item** | **WS1 colimit gate — DISCHARGED, and now SETTLED with a real non-degenerate tower.** `ws1_bisim_eq_colim` (bisimulation-is-identity, via level-local `nuLk_bisim_eq` + injective legs) + `ws1_colim_equiv` + `ws1_local_bound` + `ws1_omega_selfloop`. The charter-§9 "most likely single point of failure" — that the **connecting maps exist** (bound-relaxing *injective coalgebra morphisms* between different-cardinal `νLk`) — is now **constructed**: `boundRelax` (via terminality), `boundRelax_injective` (bisimulation), assembled into `growingTower` (strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`, real non-`id` legs), with `ws1_gate_settled` the witness. So the gate holds of a genuine object, not just an abstract `Tower` with assumed fields (no longer only the degenerate `constTower`). **Separate open:** the doubly-unbounded *index* (proper class), the §9 universe-bump refactor — see the DoubleUnboundedness row and register #1b. |
| **Verdict (WS7)** | **`payoffsEstablished` — for towers satisfying `DoubleUnboundedness`.** `ws7_verdict_eq`/`ws7_not_trivialized`/`ws7_not_one_du` are correct about the inductive `ProgramVerdict` and the conditional theorems; `ws7_verdict_eq` is a `rfl` definitional check, not evidence for the mathematics (R4). No payoff holds of a constructed object — `ws7_no_du_tower` proves the antecedent is unsatisfiable on this type. |

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
| Connecting maps exist (the §9 existential) | `boundRelax` + `boundRelax_injective` + `growingTower` + `ws1_gate_settled` (built) | **SETTLED.** The bound-relaxing *injective coalgebra morphisms* between different-cardinal `νLk` are **constructed** (via terminality); `growingTower` (strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`, real non-`id` legs) witnesses a genuine non-degenerate tower — so the gate holds of a real object, not just `constTower`. The charter-§9 "most likely single point of failure" discharged. *Still open:* the doubly-unbounded **index** (proper class), separate — register #1b |

*As built:* the gate reduces to the level-local `nuLk_bisim_eq` (labelled-carrier bisimulation-is-identity, derived from Mathlib `Cofix.bisim_rel`) plus injectivity of the colimit legs — exactly the design's reduction. Two Lean-realization fixes were required (both recorded in the Closed log, neither weakening a target): `succSet` for `destInf`, and an explicit bound-relaxation `LkRelax` in the `ι_dest` law. The colimit-functor `F_∞` fallback was **not needed** (WS6's graded law is stated on a standalone graded carrier, not on one `F_∞`).

### WS2 — The explosion, and the forced answer  ·  *the spine*
**Status: Built — Impossibility + Discharged, no-first-level Partial (definitional).** · Index decision: **`ℤ`** (I1). Contract in `spec/ws02-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| Explosion Dilemma | `ws2_explosion_dilemma` (E1) | **Impossibility proved** (both horns transcribed: `ws4_no_top_cardinal` + `ws5_global_groundless_collapses`) |
| Supremum defeats §4.1 | `ws2_supremum_walls` (E3) | **Discharged** (cardinal wall at `⨆ n, κ n`) |
| Index: no least / no greatest / self-dual | `ws2_no_least`, `ws2_no_great`, `ws2_self_dual` | **Discharged** (`omega` facts; self-duality via `n ↦ -n : ℤ ≃o ℤᵒᵈ`) |
| No first level, earned | `ws2_no_atom_floor` | **Partial — definitional** (built as the index form `no-least ⇒ strictly-lower level`; the *carrier* descent is owed to WS6 — open obligation #2, exactly as pre-registered) |
| Forced-answer dichotomy | `Boundless` + `ws2_forced_answer` (F2) | **Discharged** as a dichotomy; essential-uniqueness scoped open (charter §9) |

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
**Status: Built — A2 + V3 earned, V2 demoted, poles an index fact.** · **Forward edge to WS6 resolved** (imports WS6's `ViewAt`/`FaceReaches`/`ws6_tower_unknowable`). Contract in `spec/ws04-design.md`.

| Obligation | Target | Outcome (built) · strip test |
|---|---|---|
| Unbounded above / below | `ws4_unbounded_above/below` (A1) | **Discharged** · *bare index facts, kept as lemmas* (+ `ws4_unbounded_above/below_int` for `ℤ`) |
| **Groundless, no collapse** | `ws4_groundless_no_collapse` (A2) | **Discharged** · **survives strip** — plurality survives the colimit (two distinct faced loops, `toColim` injective) ∧ the single-carrier collapse anchor. *Descent* conjunct deferred to WS6's graded spine (open #2) |
| Coincidence: singly-bounded collapses | `ws4_singly_bounded_collapses` | **Impossibility** (transcribed `ws5_global_groundless_collapses`) |
| Poles coincide (self-dual index) | `ws4_poles_coincide` (P1) | **Discharged for `ℤ`** · **fails strip** — index fact; philosophical reading flagged interpretation |
| Poles split (lopsided) | `ws4_poles_split` (P2) | **Typed honest alternative** (`ℕ`: a least, no greatest) |
| View is positioned | `ws4_view_is_positioned` (V1) | **Discharged (definitional `rfl`)** — simplified to "a view is at a level" (the design's `viewOf = faceAt` is heterogeneously typed across the bound level) |
| No view from nowhere, naive | `ws4_no_view_from_nowhere` (V2) | **LAUNDERS** — built as `ws2_no_least ∧ ws2_no_great`, a bare order fact — **recorded, NOT a payoff** |
| **No completing view** | `ws4_no_completing_view` (V3) | **Discharged** (= `ws6_tower_unknowable`) · **survives strip** (the face's reach is load-bearing) — the genuine V2 Series 4 lacked; `ws4_unknowable_eq_noview` is the one-theorem coincidence |

*As built:* V2 (index-only) launders and is honestly demoted; V3 (a view's face misses an object at a higher level, via `ws3_no_top`) survives the strip and is the real repair. The WS4↔WS6 cycle is broken by having WS6 own `ViewAt`/`FaceReaches`/`ws6_tower_unknowable` and WS4 re-export V3.

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
**Status: Built — leak-free + DL1/DL2 discharged; relating=composition definitional; attention Trivialized.** · Grade decision: **GF1** (inert `ℤ`-label). Contract in `spec/ws06-design.md`.

| Obligation | Target | Outcome (built) · coincidence |
|---|---|---|
| **Cross-level leak-freeness** | `ws6_crosslevel_never_annihilate` (A/GF1) | **Discharged** · `ws3_faces_never_annihilate` instantiated at `Q := GLabel Q` verbatim; floor-free because `ℤ` has no bottom |
| Descent non-terminating | `ws6_descent_nonterminating` (B) | **Discharged** (from `ℤ` no-least) — stated for a **constructed descending spine** `descState`, not `∀ x` (false in general); honestly exhibits that groundless descent exists and never bottoms out |
| Relating-to = composed-of | `ws6_relating_is_composition` (B) | **NOT a coincidence — duty OPEN** (`Iff.rfl` on one identical definition; S2b, register #12) |
| Incompleteness inherited | `ws6_lawvere_incomplete`, `ws6_omega_nonterminating` (INC1) | **Discharged** (carrier-independent, transcribed) |
| Tower unknowable (new) | `ws6_tower_unknowable` (INC2) | **Discharged** (via `ws3_no_top` on the view's object) |
| Coincidence: unknowable = no-view | `ws4_unknowable_eq_noview` (in WS4) | **One theorem BY CONSTRUCTION** (`rfl` on an alias — V3 defined as INC2; S2a — not a proved coincidence) |
| Attention as grade-shift | `attend` (AT1) | **Definable; Trivialized** — no coincidence with an independent attention notion (AT2 replicator / AT3 convergence) on this carrier, the predicted honest negative |
| No strict graded law | `ws6_no_strict_graded_law` (DL1) | **Impossibility** (transcribed KS four-set diagonal, grade-inert) |
| Graded weak distributive law | `ws6_graded_weak_law_exists` (DL2) | **Discharged** — `GradedWeakDistLaw` witnessed by `gradeShiftStr` (a `ℤ`-bijection commuting with observation `LkMap`); the inert-`ℤ` payoff |

*As built:* choosing `ℤ` pays off twice — leak-freeness transports verbatim (grade inert under `lcomp`), and grade-shift is a `ℤ`-bijection commuting with observation (DL2). Two honest downgrades vs the design's prediction: **`ws6_relating_is_composition` is definitional-only** (not a genuine two-relation `↔`), and **attention is Trivialized** (as predicted). Lemma B (convergence) stays open.

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Built — verdict `payoffsEstablished`.** Contract in `spec/ws07-design.md`.

| Obligation | Target | Outcome (built) |
|---|---|---|
| The single fact | `DoubleUnboundedness` + `ws7_double_unboundedness` (F1) | **Discharged** (no least/greatest + unbounded cardinals) |
| Payoffs hold (a conjunction) | `ws7_payoffs_hold` (T2) | **Discharged as a conjunction only** (not a derivation — Series 4 R1 discipline) |
| Genuine derivations from double-unboundedness | `ws7_notop_from_du`, `ws7_descent_from_du` | **Discharged** (two payoffs genuinely derive) |
| Counterweight: leak-freeness is a second fact | `ws7_leakfree_NOT_from_du` | **Discharged** — leak-freeness holds unconditionally *and* the walled `constTower` is not doubly-unbounded, so it is genuinely a second fact |
| Distinctness anchors | `ws7_notop_vs_collapse_distinct`, `ws7_tower_vs_carrier_distinct`, `ws7_poles_vs_notop_distinct` (T3) | **Discharged — 3 mechanized rows** (Series 4 managed 2) |
| Typed verdict | `ProgramVerdict` + `ws7_verdict` (T4) | **`payoffsEstablished`** — `ws7_not_one_du` (reduction partial), `ws7_not_trivialized` (anchors refute); `ws7_verdict_eq` = `rfl` |
| Anti-laundering ledger | doc-comment (per-file strip-test notes) | The triage collapsed into the verdict decision |

*As built:* the verdict lands deterministically at the honest middle — two payoffs derive from double-unboundedness, leak-freeness is a second fact (witnessed by the constant tower), three distinctness anchors refute trivialization. `ws7_not_trivialized` / `ws7_verdict_eq` depend on *no* axioms.
*Self-audit disclosure:* Claude-auditing-Claude (charter §9); the distinctness anchors are the objective part.

---

## The §5.4 payoffs — headline tracker

*The charter's central question is whether stratification earns, relocates, or relabels each payoff. As built (Phase C) + review-pass-1 relabelled (Phase E). **S1 caveat carried into the headline:** every "Earned (tower)" row is **conditional on `hunb`/`DoubleUnboundedness`, which `ws7_setindexed_walls` proves no `Tower Q` satisfies** — so it is earned *of the antecedent*, not of a constructed object.*

| Payoff (charter §5.4) | Workstream | Verdict (built) · strip test | Coincidence |
|---|---|---|---|
| Boundlessness without a wall | WS3, WS4 | **Earned, conditional (S1)** — `ws3_no_top` survives strip (higher level supplies escaping object), *given* `hunb`, which no built tower satisfies | **Proved** (`ws3_wall_vs_grain` — two genuine proofs; the one honest coincidence) |
| Groundlessness without collapse | WS4, WS5 | **Partial** — `ws4_groundless_no_collapse` proves *plurality* (unconditional, survives strip) + the single-carrier collapse anchor; the *descent* half is deferred to WS6's bespoke spine (R2/R3), not on `Winf T` | Proved (`ws4_singly_bounded_collapses`) |
| Cross-level relating, leak-free | WS6 | **Earned, unconditional** (transported verbatim; floor-free via ℤ) | **OPEN** — `ws6_relating_is_composition` is `Iff.rfl` on one definition (S2b), *not* a coincidence; identification duty unmet |
| Poles coincide at the layer level | WS4 | **Index fact** (order self-duality; fails strip) — reading flagged interpretation | N/A (index property) |
| No view from nowhere, forced | WS4 | **V2 launders** (demoted); **V3 earned, conditional (S1)** (face's reach load-bearing) | **One theorem by construction** (`ws4_unknowable_eq_noview` is `rfl` on an alias — S2a; V3 *defined as* INC2, not a proved coincidence) |
| Incompleteness (inherited + tower) | WS6 | **INC1 earned, unconditional** (transcribed); **INC2 (`ws6_tower_unknowable`) conditional (S1)** | One theorem by construction (S2a) |
| Attention as grade-shift | WS6, WS7 | **Trivialized** — definable, coincidence negative on this carrier | Definitional-only → Trivialized |
| Plurality preserved | WS3 | **Earned, unconditional** (survives the colimit by `toColim_level_inj`) | N/A |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Statuses updated after the Phase C build; a review pass (Phase D) audits the closures.*

1. **The colimit gate** — WS1. **CLOSED, and SETTLED with a real witness.** `ws1_bisim_eq_colim` (level-local `nuLk_bisim_eq` + injective legs) + `ws1_colim_equiv` + `ws1_local_bound`, built; `destInf` realized as `succSet` (design fix). The charter-§9 "most likely single point of failure" — the *existence* of bound-relaxing injective coalgebra-morphism connecting maps — is now **constructed** (`boundRelax`, `boundRelax_injective`) and assembled into a genuine non-degenerate tower `growingTower` (strictly increasing cardinals), witnessed by `ws1_gate_settled`. The gate no longer rests only on the abstract `Tower` with assumed fields or the degenerate `constTower`.
1b. **The doubly-unbounded `Tower` inhabitant** — WS1. **OPEN (Partial — the pre-registered §9 refactor).** Review pass 1 (S1) traced this to a design under-implementation: the C2 candidate's *comment* says "a proper class / large directed set with no greatest element" and charter §9 says "the tower existential needs a proper-class index," but C2's own Lean *sketch* (and this file's `Tower`) typed `Idx : Type u`, collapsing it. `ws7_setindexed_walls` mechanizes the resulting §4.1 collapse (a `u`-small index has a supremum); `ws7_no_du_tower` : `¬ DoubleUnboundedness T` for any present tower; **`ws7_properclass_index_cofinal` mechanizes that the pre-registered proper-class index (`Type (u+1)`) *does* satisfy the unbounded-cardinals condition** (via Cantor). Trigger-to-close: the **charter-§9 refactor** — universe-bump `Tower.Idx` to a proper-class type and re-state `Winf`/payoffs over it (with the cross-universe cardinality bookkeeping that entails). This is Series 5's own pre-registered fix, not a new construction. Until then the flagship payoffs are **conditional** (headline Partial).
2. **No-first-level earned, not posited** — WS2/WS6. **OPEN (Partial — definitional).** `ws2_no_atom_floor` built at the *index* level only; the descending *carrier* map (WS6) is not built, so no-first-level is definitional. Trigger-to-close: a cross-level descending edge into `W_b` on the tower carrier. (WS6's `descState` gives a descending spine on the standalone graded carrier, not yet on `Winf T`.)
3. **Essential-uniqueness of the forced answer** — WS2. **OPEN (heuristic).** `ws2_forced_answer` dichotomy built; "every boundless-and-plural construction *is* a doubly-unbounded tower" remains defended-but-not-proved (charter §9), as Series 4 did.
4. **Cross-level leak-freeness transports** — WS6. **CLOSED.** `ws6_crosslevel_never_annihilate` = `ws3_faces_never_annihilate` at `Q := GLabel Q`, verbatim; floor-free because `ℤ` has no bottom.
5. **Graded weak distributive law** — WS6. **CLOSED.** `ws6_graded_weak_law_exists` — `gradeShiftStr` is a `ℤ`-bijection commuting with observation (GF1). No strict law (`ws6_no_strict_graded_law`, Impossibility) alongside.
6. **No-view earned, not laundered** — WS4. **CLOSED.** V3 (`ws4_no_completing_view`) survives the strip (the face's reach is load-bearing); V2 (`ws4_no_view_from_nowhere`) demoted, recorded as the bare order fact.
7. **Poles coincide or split** — WS4. **CLOSED (index fact).** `ws4_poles_coincide` for `ℤ` (flagged interpretation, fails strip); `ws4_poles_split` the typed lopsided alternative.
8. **Attention coincidence** — WS6/WS7. **OPEN → Trivialized.** `attend` definable; neither AT2 (replicator) nor AT3 (Lemma B convergence) lands on this carrier. Reported **Trivialized** — a success per §7 (the predicted honest negative). Lemma B stays open.
9. **Tower-unknowable = no-view, adjudicated** — WS6/WS4. **CLOSED (answer: one theorem, by construction).** `ws4_unknowable_eq_noview` (`rfl` on an alias — V3 := INC2); not a proved coincidence, but the "one or two?" duty is legitimately answered "one" (S2a).
10. **The verdict and the distinctness anchor** — WS7. **CLOSED.** `ws7_verdict = payoffsEstablished` with 3 mechanized distinctness rows and per-file strip-test notes.
11. **Machine-checked axiom pass** — all. **CLOSED (evidence committed).** `AxiomCheck.lean` output recorded in [`spec/axiom-check-log.md`](./spec/axiom-check-log.md); every headline theorem on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`/`admit`/`axiom`/`native_decide`-free. Closes review finding S3.
12. **Genuine `relating = composed-of` coincidence** — WS6. **OPEN (was mislabelled definitional-only).** Per S2b: `RelatesAtGrade` and `IsComposedOfAtGrade` are the *same* definition, so `ws6_relating_is_composition` (`Iff.rfl`) is **not** a coincidence. Trigger-to-close: a genuinely separate composition-side relation built from `lcomp` (design Part-B "one from `destInf`, one from `lcomp`"), proved `↔` the observation side.

**Residual opens after review pass 1 (the honest outcome):** **1b** (the doubly-unbounded tower inhabitant — the SERIOUS S1 item; `ws7_setindexed_walls` shows the *present* `Idx : Type u` encoding walls, `ws7_properclass_index_cofinal` shows the pre-registered proper-class index works — the fix is the §9 universe-bump refactor), #2 (no-first-level definitional), #3 (essential-uniqueness heuristic), #8 (attention Trivialized), #12 (the relating=composition coincidence, reopened). **The split the design forecast held** *within the conditional*: carrier/face-load-bearing payoffs survive their strip tests, index-reducible ones are flagged — but the whole class of tower payoffs sits under the S1 conditional, so the honest headline is **Partial (conditional on the tower, pending the §9 proper-class-index refactor)**, not "earned."

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
graded weak law **Discharged** (`ws6_graded_weak_law_exists`); Explosion Dilemma **Impossibility**
(`ws2_explosion_dilemma`); poles **index fact** (`ws4_poles_coincide`, flagged interpretation) with
lopsided alternative (`ws4_poles_split`); no-view V2 **laundering / demoted**, V3 **earned**;
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
- **No SERIOUS finding remains open as mislabelled:** S1 is now reported Partial at the headline with the obstruction mechanized; S2/S3 are relabelled/closed. The single remaining SERIOUS-severity *mathematical* gap (the tower inhabitant) is a **non-terminal Partial**: the fix is pre-registered (charter §9 proper-class index; `ws7_properclass_index_cofinal` shows it works at the index level), owed as a universe-bump refactor of `Tower`/`Winf` within Series 5 — *not* a Series 6 pivot. Reported honestly at the headline per the protocol.
- **Gate settled (follow-up to S1, this session).** Prompted by the charter-§9 pointer ("Most likely single point of failure; settled first"), the gate's genuine existential — the *existence* of bound-relaxing injective coalgebra-morphism connecting maps — was constructed: `boundRelax` (terminal-morphism into the larger `νLk`), `boundRelax_injective` (via `nuLk_bisim_eq`), `boundRelax_refl`/`boundRelax_trans` (functoriality), assembled into `growingTower` (strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`) and witnessed by `ws1_gate_settled`. The gate now holds of a genuine non-degenerate tower, not just the abstract `Tower` or the degenerate `constTower`. Axiom-clean (standard three). **This is the gate ("settled first") the charter flags as the program's most likely single point of failure — now discharged with a real object.** The remaining tower open is only the doubly-unbounded *index* (register #1b, the §9 universe-bump).
- *Next: Phase D pass 2 (regenerate the review against this addressed build) if desired.*

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
