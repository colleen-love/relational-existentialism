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
- Every claim of "sorry-free / axiom-clean" is provisional until a machine-checked `#print axioms` against the pinned Lean/Mathlib is recorded. **As of this pass nothing is built; all axiom claims are design-predicted, not verified.**

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v1 — all seven design docs committed; **full formal build lands, `sorry`-free and axiom-clean** (Phase C, this session) |
| **Design docs** | `series-5/spec/ws01…ws07-design.md` + `README.md` — **committed**. Each: 3–7 candidate framings with Lean signatures + ambient theory + success/failure conditions, a paper-decidable triage collapsed to a table, the winner developed into a full mathematical design. |
| **Formalization** | **BUILT.** `ws1.lean … ws7.lean`, `Series5.lean`, `AxiomCheck.lean` — self-contained (Series 4/3 machinery transcribed; closure gate confirms nothing imported from `series-4/` or `archive/`), pinned Lean 4.15.0 / Mathlib v4.15.0. `lake build` green; `#print axioms` on all 34 headline theorems shows only `propext` / `Classical.choice` / `Quot.sound` (two verdict theorems depend on none). Two in-build design fixes recorded below (WS1); several honest scopings recorded per workstream. |
| **Central question** (charter §8) | **The split answer landed as forecast.** Boundlessness-without-a-wall (WS3), groundlessness-without-collapse (WS4), and cross-level leak-free relating (WS6) are **earned** (survive their strip tests); the pole coincidence (WS4), the naive no-view V2 (WS4), and attention-as-grade-shift (WS6) are **index facts / laundering / Trivialized**, honestly flagged. Verdict **`payoffsEstablished`**, not `oneDoubleUnboundedness` — mechanized in `ws7_verdict`. |
| **Headline positive (built)** | Explosion Dilemma (WS2, Impossibility) · no-top powered by no-last-level, surviving its strip test (WS3) · groundless-no-collapse via the local/global decoupling (WS4) · leak-free cross-level composition, floor-free because ℤ has no bottom (WS6) · no strict graded distributive law (WS6, Impossibility, inherited KS diagonal) · graded weak law exists (WS6). |
| **Signature risk** | Trivialization — **caught, verdict landed at the honest middle.** Three payoffs survive their strip tests, leak-freeness is a demonstrated second fact (`ws7_leakfree_NOT_from_du`, holds on the walled `constTower`), and three distinctness anchors refute `trivialized`. |
| **Blocking item** | **WS1 colimit gate** — **DISCHARGED.** `ws1_bisim_eq_colim` (a colimit bisimulation, restricted at a common level, is contained in the diagonal, via the level-local `nuLk_bisim_eq` + injective legs). `ws1_colim_equiv`, `ws1_local_bound`, `ws1_omega_selfloop` also built. A concrete `constTower` witnesses `Tower Q` is inhabited (non-vacuity); a *doubly-unbounded* inhabitant with bound-relaxing injective coalgebra-morphism legs remains the charter-§9 existential (the abstract `Tower` is the WS1 deliverable, per the design). |
| **Verdict (WS7)** | **`payoffsEstablished`** — built. `ws7_verdict_eq` : `ws7_verdict = payoffsEstablished`; `ws7_not_trivialized`; `ws7_not_one_du`. Two payoffs derive from double-unboundedness (`ws7_notop_from_du`, `ws7_descent_from_du`); leak-freeness is a second fact (`ws7_leakfree_NOT_from_du`, holds on the walled `constTower`). |

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
| Non-vacuity / doubly-unbounded inhabitant | `constTower` (built) / abstract `Tower` | Constant tower witnesses `Tower Q` inhabited; a *doubly-unbounded* inhabitant (bound-relaxing injective coalgebra-morphism legs) stays the **charter-§9 existential** — the abstract `Tower` is the deliverable, so `∀ T` payoffs are conditional on such a tower |

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
| Relating-to = composed-of | `ws6_relating_is_composition` (B) | **Definitional-only** (`Iff.rfl`) — the genuine two-definition coincidence is the open residue (coincidence duty (i) not fully earned) |
| Incompleteness inherited | `ws6_lawvere_incomplete`, `ws6_omega_nonterminating` (INC1) | **Discharged** (carrier-independent, transcribed) |
| Tower unknowable (new) | `ws6_tower_unknowable` (INC2) | **Discharged** (via `ws3_no_top` on the view's object) |
| Coincidence: unknowable = no-view | `ws4_unknowable_eq_noview` (in WS4) | **One theorem, adjudicated** (same proof term; `rfl`) — placed in WS4 (imports WS6) to keep the module graph acyclic |
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

*The charter's central question is whether stratification earns, relocates, or relabels each payoff. This is the one-glance answer, **as built** (Phase C).*

| Payoff (charter §5.4) | Workstream | Verdict (built) · strip test | Coincidence |
|---|---|---|---|
| Boundlessness without a wall | WS3, WS4 | **Earned** (`ws3_no_top` survives strip — higher level supplies escaping object) | **Proved** (`ws3_wall_vs_grain`) |
| Groundlessness without collapse | WS4, WS5 | **Earned** (object plurality survives colimit + single-carrier collapse anchor) | Proved (`ws4_singly_bounded_collapses`) |
| Cross-level relating, leak-free | WS6 | **Earned** (transported verbatim; floor-free via ℤ) | **Definitional-only** (`ws6_relating_is_composition` is `Iff.rfl` — genuine coincidence open) |
| Poles coincide at the layer level | WS4 | **Index fact** (order self-duality; fails strip) — reading flagged interpretation | N/A (index property) |
| No view from nowhere, forced | WS4 | **V2 launders** (demoted); **V3 earned** (face's reach load-bearing) | **Proved via V1 + V3** (V2 rejected) |
| Incompleteness (inherited + tower) | WS6 | **Earned** (INC1 transcribed, INC2 new) | **One theorem** (`ws4_unknowable_eq_noview`, adjudicated) |
| Attention as grade-shift | WS6, WS7 | **Trivialized** — definable, coincidence negative on this carrier | Definitional-only → Trivialized |
| Plurality preserved | WS3 | **Earned** (survives the colimit by `toColim_level_inj`) | N/A |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Statuses updated after the Phase C build; a review pass (Phase D) audits the closures.*

1. **The colimit gate** — WS1. **CLOSED.** `ws1_bisim_eq_colim` (level-local `nuLk_bisim_eq` + injective legs) + `ws1_colim_equiv` + `ws1_local_bound`, built. `destInf` realized as `succSet` (design fix). *Residual:* a doubly-unbounded `Tower` *inhabitant* is still the charter-§9 existential (only `constTower`, a walled witness, is built).
2. **No-first-level earned, not posited** — WS2/WS6. **OPEN (Partial — definitional).** `ws2_no_atom_floor` built at the *index* level only; the descending *carrier* map (WS6) is not built, so no-first-level is definitional. Trigger-to-close: a cross-level descending edge into `W_b` on the tower carrier. (WS6's `descState` gives a descending spine on the standalone graded carrier, not yet on `Winf T`.)
3. **Essential-uniqueness of the forced answer** — WS2. **OPEN (heuristic).** `ws2_forced_answer` dichotomy built; "every boundless-and-plural construction *is* a doubly-unbounded tower" remains defended-but-not-proved (charter §9), as Series 4 did.
4. **Cross-level leak-freeness transports** — WS6. **CLOSED.** `ws6_crosslevel_never_annihilate` = `ws3_faces_never_annihilate` at `Q := GLabel Q`, verbatim; floor-free because `ℤ` has no bottom.
5. **Graded weak distributive law** — WS6. **CLOSED.** `ws6_graded_weak_law_exists` — `gradeShiftStr` is a `ℤ`-bijection commuting with observation (GF1). No strict law (`ws6_no_strict_graded_law`, Impossibility) alongside.
6. **No-view earned, not laundered** — WS4. **CLOSED.** V3 (`ws4_no_completing_view`) survives the strip (the face's reach is load-bearing); V2 (`ws4_no_view_from_nowhere`) demoted, recorded as the bare order fact.
7. **Poles coincide or split** — WS4. **CLOSED (index fact).** `ws4_poles_coincide` for `ℤ` (flagged interpretation, fails strip); `ws4_poles_split` the typed lopsided alternative.
8. **Attention coincidence** — WS6/WS7. **OPEN → Trivialized.** `attend` definable; neither AT2 (replicator) nor AT3 (Lemma B convergence) lands on this carrier. Reported **Trivialized** — a success per §7 (the predicted honest negative). Lemma B stays open.
9. **Tower-unknowable = no-view, adjudicated** — WS6/WS4. **CLOSED.** `ws4_unknowable_eq_noview` (`rfl`) — one theorem, not two.
10. **The verdict and the distinctness anchor** — WS7. **CLOSED.** `ws7_verdict = payoffsEstablished` with 3 mechanized distinctness rows and per-file strip-test notes.
11. **Machine-checked axiom pass** — all. **CLOSED.** `AxiomCheck.lean` run against pinned Lean 4.15.0 / Mathlib v4.15.0; all 34 headline theorems on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free.

**Residual opens after the build (the honest outcome, as forecast):** #2 (no-first-level definitional pending a tower-carrier descending map), #3 (essential-uniqueness, heuristic), #8 (attention, Trivialized), and one not pre-listed — the **doubly-unbounded `Tower` inhabitant** (charter §9 existential; only the walled `constTower` is built, so the `∀ T` payoffs are conditional). A further build could also promote `ws6_relating_is_composition` from definitional-only to a genuine two-relation coincidence. **The split the design forecast held:** carrier/face-load-bearing payoffs (no-top, non-collapse, no-completing-view, leak-free) are earned; index-reducible ones (poles, naive no-view, attention) are index facts / laundering / Trivialized, honestly flagged.

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

- *Phase C (build-all) complete: `ws1…ws7` built, `sorry`-free and axiom-clean. No blind review pass (Phase D) yet — `series-review.md` not written. Next: a blind whole-series review against the built code and the design contracts.*

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
