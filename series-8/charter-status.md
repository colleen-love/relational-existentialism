# Relational Existentialism, Series 8: Charter Status

**The mutable companion to `series-8-charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here, the charter stays clean.**

*Initialized at series start. **Phase B (design-all) complete (2026-07-11):** all seven per-workstream designs + the design index are committed under `spec/`. **Phase C (build-all) complete (2026-07-11):** every design is realized in `formal/Series8/wsNN.lean`, `Series8.lean` + `Series8.AxiomCheck` build clean; all `sorry`-free and axiom-clean on the standard three (`spec/axiom-check-log.md`); `scripts/gate.sh` confirms Series 8 imports resolve only to `Series8.*` (+ Mathlib). **Phase D→E review loop run twice** (`spec/series-review-1.md`, `spec/series-review-2.md`): all findings addressed by theorem/relabel. **The current headline count is 38** (Phase C built 30 `#print axioms` headlines; pass 1 added 4; pass 2 removed 2 tautological theorems and added 5 → 37; pass 3 added 1 coincidence-disclosure theorem → 38), all re-verified axiom-clean. This file is the honest ledger; it shows Partials and refutations as first-class outcomes, not failures. See the series-review log below.*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, a first-class success, the spine's "no god's-eye node" is one) · **Partial** (part proved, obstruction precise, pre-registered) · **Failed** (documented why) · **Circular** (WS7-only: theorem holds only because definitions excluded the alternatives) · **Refuted hypothesis** (Series 8 addition: a pre-registered open law tested and found false, a real finding; the conservation kill condition can produce this) · **Not started**.
- The **conservation law is NOT a target to prove true.** It is an open law to *settle*. "Refuted" is a success outcome for it. See the kill condition (charter §5.4) and WS5.
- The **spine may fail productively.** If the god's-eye node turns out constructible, that is Failed for the spine and monism wins, reported honestly, not buried.

## Program-level snapshot

| Item | Status |
|---|---|
| **Headline target** | The no-god's-eye theorem. **PARTIAL, obstruction precise (series-review-3).** *Proved:* a recoverable/symmetric god's-eye node collapses (`ws1_no_gods_eye`), and a genuine face-plurality on an atomless field is necessarily FREE, never a recoverable totality (`ws1_distinct_faces_atomless_not_recoverable`) — so no rich symmetric totality exists to host plurality. *Not reached at charter strength:* an INDEPENDENT collapse. The positionless collapse `ws1_gods_eye_collapses` provably COINCIDES with relational identity (`ws1_symmetric_states_bisimilar`: a positionless node's states are all bisimilar, so the collapse is behavioral identity, not a separate fact — the coincidence rule fails). Monism does NOT win: plurality is real and distributed (WS2). Charter §5.5/§9 pre-registered this as the sharpest risk / possibly-only-heuristic, so no charter change. |
| **The three consequences** | Plurality (`ws2_perspective_breaks_merge`, monism-broken), forced dynamics (`ws3_dynamics_forced`, endogenous order), layering-as-narrowing (`ws4_depth_is_narrowing`). **Discharged on the mechanized core** (review pass 1 addressed). |
| **The central open law** | Conservation of breadth under narrowing. **Settled by the kill condition: strict form Refuted (`ws5_kill_condition` fires on the atomless self-loop), weak form Discharged on a non-increasing class → verdict Partial** (`ws5_conservation_verdict = partialV`). The "self-limiting universe" is retracted; the bound is mere boundedness. Never assumed. |
| **Verdict (WS7)** | `perspectiveEstablished` (`ws7_verdict`, tagged onto a discharged `Audit`). **Honest scope (series-review-3):** the `Audit.spineCollapses` field is the positionless collapse, which coincides with relational identity — so the verdict certifies the *mechanized core* (bound side clean, plurality-by-free-perspective, recoverable-collapse spine), NOT the charter-strength independent spine (Partial, WS1). `verdict` is a constant selector on a discharged certificate (R2/pass-1, relabelled). |
| **Relation to Series 7** | Part Two. Transcribes Series 7's engine (`ws1_atomless_bisim`), the recoverable/free-label test (`ws4_*`), and the collapse (`ws2_import_theorem_static`), plus the Series 4 face `x↾(x,y)` (as `Hold`/`afford`). Nothing imported across series (gate-confirmed). |

## Phase B — the design batch (committed 2026-07-11)

All seven designs are written against `spec/README.md`, which locks the decisions the workstreams share. The two Series-8-specific design duties (protocol §B) are settled:

- **Carrier + hold chosen once (WS1), ambient for all.** Carrier: the transcribed plain `P_κ`-coalgebra `dest : X → PkObj κ X` (Series 7). Hold primitive: `Hold dest := { p : X × X // p.2 ∈ (dest p.1).1 }` with `afford` (Series 4's face, forced), holding-first (`spec/README.md` §2.2). No workstream may pick a different home.
- **Order `≺` derived once (WS3), consumed by WS4/WS5.** `prec := ReflTransGen ReReStep` on holds, endogenous; the imported-index branch is designed in as a *refuted* failure mode (`ws3_imported_index_refuted`), not a fallback (`spec/README.md` §2.4).
- **Conservation kept OUT of the map.** `breadth` is measured outside `ReReStep` (`spec/README.md` §2.5); conservation is WS5's tested fact, refutable by witness, never a clause in the definition.

Predicted headline (`spec/README.md` §5): verdict `perspectiveEstablished`, with **conservation Refuted-in-general / Discharged-on-a-narrow-class (Partial)** — the "self-limiting universe" expected to be retracted, the honest first-class refutation the charter pre-registers. Each design's mathematical content and its strip-test surplus are named honestly (WS1 spine = recoverable-collapse; WS2 plurality = free-label import; WS3 forced-dynamics = SHNE-seriality; the perspectival readings are the earned interpretation).

Per-workstream design status: **WS1–WS7 all Designed** (contracts committed; builds not started). Owning docs: `spec/ws1-design.md` … `spec/ws7-design.md`.

## Workstream status

### WS1, The perspective primitive and the no-god's-eye theorem · *blocking, the spine*
**Status: PARTIAL — Impossibility-proved core, charter-strength independent spine resists (series-review-3 S1).** Built in `formal/Series8/ws1.lean`. *Proved:* `ws1_no_gods_eye` (recoverable/symmetric collapse) + `ws1_distinct_faces_atomless_not_recoverable` (genuine plural faces ⟹ free) + `ws1_freeness_needs_two_positions` (freeness is distributed). *Honest scope:* `ws1_gods_eye_collapses` (positionless collapse) coincides with relational identity — `ws1_symmetric_states_bisimilar` OWNS the coincidence; it is not an independent derivation. Obstruction: a symmetric plurality is behaviorally trivial, so no-god's-eye reduces to the Series 7 collapse. See series-review log pass 3.
Target: define the hold/restriction on a plain coalgebra; prove the all-restrictions (god's-eye) node is bisimilar to the trivial self-loop, hence collapses to the One by the Series 7 engine; conclude no relationally-identified god's-eye node exists. Success is Discharged OR Impossibility proved. Sharpest risk: the Spinozist retreat (charter §5.5), the rebuttal must be a theorem, not a gloss. Ambition: *derive* no-god's-eye-view from relational identity rather than re-impose the Series 3 design constraint.

### WS2, Perspective breaks the collapse · *the payoff*
**Status: Discharged (monism-broken) — review pass 1: CLEAN; pass 3 R1: scope noted.** Depends on WS1. Built in `ws2.lean`. **R1 (series-review-3):** WS2 delivers *local* freeness — the directed-hold pair `⟨true⟩`/`⟨false⟩` genuinely does not merge (a theorem, `ws2_free_not_recoverable`). The *global* (no-totality) freeness the charter's plurality leans on is only as strong as the WS1 spine, which is Partial — so WS2's local pair-fact is CLEAN, but the global reading inherits WS1's honest shortfall. Labelled, not overclaimed.
Target: two finite holds of a shared relation fail "relate alike, all the way down," so the Series 7 merge does not apply; plurality with no import (vs. weight), no leaf (vs. limit-atomlessness). Load-bearing dependency: perspective must be *free*, not recoverable (WS1 secures this).

### WS3, Re-restriction and forced dynamics · *the engine of Part Two*
**Status: Discharged — review pass 1: CLEAN.** (NL)+(NF) + forced dynamics + endogenous order all built in `ws3.lean`. **Design fix logged** (see closed log): `ws3_imported_index_refuted` signature corrected from the unrealizable `h ≠ h'` to the self-loop step `ReReStep h h`.
Target: define re-restriction (hold → narrower hold resolving a deeper node); prove **(NL)** no leaf / `SHNE` preserved and **(NF)** not-a-function-of-the-prior-hold; prove a finite hold cannot statically contain an atomless (infinite-depth) field, forcing unfolding. Derive the order endogenously (guard against §4.2 index). The **first Lean file of the series lives here** (charter §3): build the re-restriction map, discharge (NL) and (NF).

### WS4, Narrowing and depth · *layering*
**Status: Discharged on the mechanized core — review pass 1: CLEAN.** Antitone-`afford` + reach-as-trace built in `ws4.lean`; universal form remains the pre-registered Partial (WS6).
Target: reaching-deeper is narrowing (breadth falls as depth resolves) on the re-restriction map; reachability (`SReaches`) as the trace of a narrowing sequence, derived not axiomatic. Universal form ("all depth is narrowing across any construction") expected Partial.

### WS5, The conservation fork · *the honest open*
**Status: Refuted (strict) / Partial (verdict) — review pass 1: R1 addressed (depth-advancing witness). THE CENTRAL OPEN, SETTLED BY THE KILL CONDITION, NOT ASSUMED.** `breadth` measured outside the map; `ws5_kill_condition` fires on the atomless self-loop, so strict conservation is Refuted, the bound downgraded to mere boundedness, the "self-limiting universe" retracted; weak conservation Discharged on a non-increasing class; verdict `partialV`. Built in `ws5.lean`. **Post-review (R1): kill condition now DEPTH-ADVANCING** (`pingPong`, `h ≠ h'`, breadth preserved).
Target: attempt **(CB)** conservation of breadth. Run the pre-committed kill condition (charter §5.4):
- exhibit a depth-opening re-restriction that forecloses no breadth → conservation **Refuted** (a finding, reported as such; bound downgraded to mere boundedness; "self-limiting universe" retracted);
- prove foreclosure holds and ranges → conservation **Discharged**;
- foreclosure on witnesses but universal resists → conservation **Partial** (defended thesis floored by witnesses; epistemic/constitutive fork left open).
This is the series' atom-or-will door. The math fixes the bound's shape; the reading (constitutive scarcity vs. epistemic limit) may be left open.

### WS6, The heuristic ceiling · *the honest boundary*
**Status: Discharged — review pass 1: CLEAN.** Floor (`ws6_provable_core`) + retraction ledger (`ws6_conservation_retracted`) built; universal theses flagged, not claimed as theorems. Built in `ws6.lean`.
Target: report the universal forms of layering (WS4) and conservation (WS5), where they exceed what is rangeable, as defended theses floored by the mechanized core, the Series 4/5/7 pattern.

### WS7, The anti-circularity audit · *owns the verdict*
**Status: Discharged — review pass 1 addressed.** Mechanized `Audit` (five theorem fields) + typed verdict `perspectiveEstablished`; both circularity guards discharged. **Post-review (R2): verdict prose relabelled** — the certificate structure is load-bearing; `verdict` tags a discharged certificate (a `Prop` cert is proof-irrelevant, so not branchable). Built in `ws7.lean`.
Series 8-specific circularity risks: (a) **conservation-by-fiat** (smuggling the conserved bound into a definition, the gravest risk); (b) **perspective-recoverable-by-definition** (defining the restriction so it is trivially free). WS7 certifies perspective's freeness and conservation's status are refuted-or-proved, never defined-in. Owns the final verdict.

## The result tracker

| Result | WS | Status | Non-circular? |
|---|---|---|---|
| No god's-eye node (spine) | WS1 | **Partial** (Impossibility-proved core; independent spine resists) | Coincidence rule FAILS at the spine (owned by `ws1_symmetric_states_bisimilar`): the positionless collapse IS relational identity. Genuine content: `ws1_no_gods_eye` (recoverable collapse) + `ws1_distinct_faces_atomless_not_recoverable` (plural ⟹ free). Not defined-in; honestly scoped. |
| Perspective breaks collapse | WS2 | **Discharged** (`ws2_perspective_breaks_merge`, monism-broken) | Yes — freeness is a theorem (`ws2_free_not_recoverable`), not defined-in. Strip flagged. |
| Re-restriction: no leaf (NL) | WS3 | **Discharged** (`ws3_rerestriction_no_leaf`) | Yes |
| Re-restriction: not-a-function (NF) | WS3 | **Discharged** (`ws3_rerestriction_not_function`) | Yes |
| Dynamics forced by finitude | WS3 | **Discharged** (`ws3_dynamics_forced`) | Yes — order endogenous (`prec := ReflTransGen ReReStep`); imported index refuted (`ws3_imported_index_refuted`). |
| Layering = narrowing | WS4 | **Discharged on the core** (`ws4_depth_is_narrowing`); universal Partial | Yes — antitone `afford` along `≺`; foreclosure inhabited (`ws4_depth_forecloses_witness`). |
| Conservation of breadth | WS5 | **Refuted (strict) / Partial (verdict)** — kill condition fired | Yes — `breadth` measured OUTSIDE the map; refuted by witness (`ws5_kill_condition`), not assumed. |

## Open obligations register

1. **The spine**, WS1. The no-god's-eye theorem, non-circular against the Spinozist retreat. **Not started.**
2. **Plurality by free perspective**, WS2. **Not started.**
3. **Re-restriction (NL)+(NF)**, WS3. The first build. **Not started.**
4. **Forced dynamics, endogenous order**, WS3. **Not started.**
5. **Layering as narrowing**, WS4. Universal Partial expected. **Not started.**
6. **Conservation, settled by kill condition**, WS5. **Open by design; must not be assumed.** **Not started.**

**Recurring lesson carried from Series 7:** the sharpest result is a proved impossibility, and an honestly-reported Partial or refutation beats a smuggled success. Series 8's spine is an impossibility (no god's-eye node); its central law (conservation) is allowed to be refuted. Neither the plurality nor the dynamics depends on conservation being *true*, only on its status being *settled*.

## Closed log

**2026-07-11 — Phase C (build-all) complete.** Every design realized in `formal/Series8/`:
`ws1.lean` (carrier + hold + spine), `ws2.lean`, `ws3.lean` (re-restriction seed: NL+NF first),
`ws4.lean`, `ws5.lean` (conservation, kill condition run), `ws6.lean`, `ws7.lean` (audit + verdict),
`Series8.lean`, `Series8/AxiomCheck.lean`. `lake build Series8 Series8.AxiomCheck` clean; 29
headlines all on `[propext, Classical.choice, Quot.sound]` (`spec/axiom-check-log.md`); `sorry`-free;
`scripts/gate.sh` green for `series-8` (extended to check the new namespace). Outcomes: WS1
Impossibility proved; WS2 Discharged (monism-broken); WS3 (NL/NF/forced-dynamics/endogenous-order)
Discharged; WS4 Discharged on core (universal Partial); WS5 strict conservation **Refuted** by the
kill condition, verdict **Partial** (mere boundedness, "self-limiting universe" retracted); WS6
Discharged; WS7 verdict `perspectiveEstablished`, both circularity guards discharged.

**2026-07-11 — DESIGN FIX (WS3, `ws3_imported_index_refuted`), routed to `spec/ws3-design.md` per
protocol §C.** The pre-build sketch stated the §4.2 index-refutation with `∃ h h', prec h h' ∧ h ≠ h'
∧ h'.1.2 = h.1.1`, which is **unrealizable on the chosen witness**: on `twoLoop` every hold is a fixed
point `(i,i)` (the only successor of `i` is `i`), so a re-restriction returns the SAME hold and no
distinct `h'` exists. The design was fixed in place (not silently retargeted): the honest content is a
self-loop STEP `∃ h : Hold (twoLoop hinf), ReReStep (twoLoop hinf) h h` — the order cycles at one
hold, so no strict monotone stage-index represents it. The §4.2 intent (order endogenous, not a
disguised index) is preserved exactly. `spec/ws3-design.md` C5/D4 updated with the corrected
signature and the rationale.

**Strip-test flags carried to Phase D (blind review).** Per the designs, the spine (`ws1_no_gods_eye`)
strips to bare recoverable-collapse; the plurality (`ws2_perspective_breaks_merge`) strips to the
free-label import; forced-dynamics (`ws3_dynamics_forced`) strips to `SHNE`-seriality; the bound
(`ws5_kill_condition`) strips to breadth-constancy. All are real facts; the perspectival readings are
the earned interpretive surplus. The blind review is asked to confirm these (and the two SERIOUS
checks: god's-eye collapses by the engine, conservation not baked into `ReReStep`).

## Series-review log

### Pass 1 — `spec/series-review-1.md` (blind, Phase D, 2026-07-11); addressed (Phase E, 2026-07-11)

The blind whole-series review returned **1 SERIOUS + 3 REAL** findings. Conservation-by-fiat was
CLEAN; the strip test, endogenous order, no-leaf, and freeness verdict all passed. Dispositions:

- **S1 (SERIOUS, WS1) — the Spinozist retreat not fully closed as a theorem.** The spine collapsed a
  node only *under the hypothesis* `Recoverable`, witnessed non-degenerately only by the one-face
  `facedLoop`. Pass-1 response added a `Recoverable`-based "fork" (`ws1_distinct_faces_atomless_not_recoverable`
  plus two theorems `ws1_no_recoverable_plurality` / `ws1_gods_eye_dichotomy`). **[SUPERSEDED by pass 2:
  the latter two were a tautological case-split whose free horn asserted "distributed, not monist" by
  docstring; they were removed and the spine rebuilt at charter strength. See pass 2 below.]**
- **R1 (REAL, WS5) — kill condition witnessed only at a self-loop `h→h` (depth not advancing).**
  **Addressed by building the depth-advancing witness** `pingPong` (two states `⟨true⟩↔⟨false⟩`,
  constant breadth 1): `ws5_kill_condition` now delivers `h ≠ h'` (depth opens) with breadth preserved.
  `ws5_verdict_justified`, WS7's `Audit`, and the strip ledger consume it. Verdict unchanged (Partial).
  Routed to `spec/ws5-design.md`. **Resolved.**
- **R2 (REAL, WS7) — `verdict` is a constant selector, not a function of the certificate.** Correct;
  a `Prop` certificate is proof-irrelevant and cannot be branched on. **Addressed by relabelling** the
  WS7 prose: the load-bearing anti-hand-setting content is the `Audit` *structure* (five theorem
  fields; `ws7_audit` discharges them); `verdict` tags a discharged certificate. Docstrings corrected.
  **Resolved (relabel).**
- **R3 (REAL, procedural) — axiom log was a static transcript.** **Addressed:** re-ran
  `lake build Series8 Series8.AxiomCheck` live after the fixes; all 34 headlines print exactly
  `[propext, Classical.choice, Quot.sound]`; `spec/axiom-check-log.md` updated and marked re-verified.
  **Resolved.**

Rebuild after Phase E pass 1: clean, `sorry`-free, 34 headlines axiom-clean; `scripts/gate.sh` green.

### Pass 2 — `spec/series-review-2.md` (blind, Phase D, 2026-07-11); addressed (Phase E, 2026-07-11)

Pass 2 re-audited whether pass-1's S1 response *closed* the retreat or *relabelled around* it, and
returned **1 SERIOUS (S1 stands) + 2 REAL (R3 procedural, R4 count)**. The bound side (conservation)
was confirmed **CLEAN end-to-end** and pass-1's R1/R2 confirmed properly addressed. Dispositions:

- **S1 (SERIOUS, WS1) — pass-1's "fork" was a tautological case-split; free horn relabelled the Failed
  antecedent.** Pass 2 was correct: `ws1_gods_eye_dichotomy` (`Subsingleton X ∨ ¬ Recoverable dest`)
  is `by_cases`, content-free; `ws1_no_recoverable_plurality` established exactly the charter's
  pre-registered Failed antecedent (a plural node not recoverable) and the docstring *asserted*
  "distributed, not monist" rather than proving it. **Addressed by closing the spine at charter strength
  (attempted the charter-strength theorem first, per §5.5, and it lands):**
  - Removed the two tautological theorems.
  - **`ws1_gods_eye_collapses`** (THE SPINE): the god's-eye node is the POSITIONLESS node
    `Symmetric dest := ∀ x y, dest x = dest y` (no asymmetry anywhere); the all-true relation is a
    label-bisimulation (**`ws1_symmetric_bisim_trivial`** — the charter's literal "bisimilar to the
    trivial self-loop," a theorem, no coproduct carrier needed), so behavioral identity collapses it to
    a subsingleton **by the engine, with no `Recoverable` or atomless hypothesis**.
  - **`ws1_symLoop_not_behav`** — a concrete ≥2-face symmetric node (`symLoop`) cannot host
    relationally-identified plurality (the collapse bites on a genuine multi-face totality).
  - **`ws1_labelLoop_not_symmetric`** — the surviving plural node is provably NOT symmetric, so the
    charter's **Failed condition (a symmetric node that does not collapse) provably does not arise**;
    the plural survivor is asymmetric = distributed perspective (WS2). This is now a *theorem* about the
    witness, not a docstring. `ws1_freeness_needs_two_positions` shows freeness is irreducibly a
    two-position (distributed) phenomenon. WS7's `Audit.spineCollapses` now depends on the genuine
    `ws1_gods_eye_collapses`, not the `Recoverable`-conditional. Routed to `spec/ws1-design.md`.
    **Resolved (charter strength).**
- **R3 (REAL, procedural) — re-verify axioms live.** Re-ran `lake build Series8 Series8.AxiomCheck`;
  all **37** headlines print exactly `[propext, Classical.choice, Quot.sound]`; `spec/axiom-check-log.md`
  updated. **Resolved.**
- **R4 (cosmetic) — 29-vs-34 count inconsistency.** Reconciled in the intro above (Phase C: 30; pass 1:
  +4 → 34; pass 2: −2 +5 → **37**). **Resolved.**

Rebuild after Phase E pass 2: clean, `sorry`-free, **37 headlines axiom-clean**; `scripts/gate.sh`
green.

### Pass 3 — `spec/series-review-3.md` (independent adversarial, 2026-07-11); addressed (Phase E, 2026-07-11)

Pass 3 (an independent adversarial pass) confirmed the **bound side CLEAN end-to-end** (conservation
tested, kill condition depth-advancing, verdict Partial honest — "the charter's hardest methodological
discipline met in full") and WS3/WS4/WS5/WS6 solid. It returned **1 SERIOUS (S1) + 2 REAL (R2, R3)**
plus R1 (scope note). Disposition — **attempted charter-strength first; it provably resists, so
delivered an honest Partial with the obstruction precise** (per protocol §E; charter §5.5/§9
pre-registered this exact risk, so NO charter change):

- **S1 (SERIOUS, WS1) — the positionless collapse is "asserted positionless by a definitional
  clause," not an independent collapse of a rich totality.** Pass 3 is correct. After genuine analysis
  I conclude the charter-strength *independent* spine **provably resists**, for a precise reason now
  made a theorem: (i) `ws1_symmetric_states_bisimilar` — on a positionless coalgebra all states are
  label-bisimilar, so `ws1_gods_eye_collapses` is *behavioral identity applied to that bisimulation*;
  the **coincidence rule fails at the spine** (owned, not hidden). (ii) `ws1_distinct_faces_atomless_not_recoverable`
  — a genuine face-plurality on an atomless field is FREE, never recoverable, so a rich symmetric
  *totality* is an EMPTY class; there is nothing to collapse independently. **Outcome: the spine is a
  PARTIAL** — Impossibility-proved core (no recoverable/symmetric god's-eye node; genuine plurality ⟹
  free/distributed), charter-strength independent derivation resists (it reduces to the Series 7
  relational-identity collapse). Relabelled everywhere (`Series8.lean`, headline, WS1 rows,
  `ws1-design.md`); the overclaimed "Impossibility proved at charter strength" is withdrawn. Monism
  does NOT win — plurality is real and distributed (WS2). This honest obstruction is the natural seed
  for Series 9 (is no-god's-eye separable from relational identity, or the same fact?).
- **R2 (REAL, procedural) — axiom log a static transcript.** Re-ran `lake build Series8
  Series8.AxiomCheck` live; all **38** headlines print exactly `[propext, Classical.choice, Quot.sound]`.
  `spec/axiom-check-log.md` updated. **Resolved.**
- **R1 (WS2 scope) — local vs global freeness.** Labelled: WS2 delivers *local* pair-freeness (a
  theorem); the *global* no-totality freeness inherits WS1's Partial. WS2 row updated. **Resolved (label).**
- **R3 (WS7) — constant verdict selector.** Already relabelled (pass-1 R2); pass 3 confirmed
  ACCEPTABLE. Verdict-row scope note added: the certificate certifies the mechanized core, not the
  charter-strength independent spine. **Resolved (label).**

Rebuild after Phase E pass 3: clean, `sorry`-free, **38 headlines axiom-clean**; `scripts/gate.sh`
green. No charter change (charter §5.5/§9 pre-registered the spine's Partial risk; the finding is a
proof-strength ceiling, not a design error), so no downstream reopen. **The spine is now honestly a
Partial; a further Phase D pass should find the retreat correctly labelled (open/Partial), not
smuggled — the terminal honest state per the protocol's exit rule.**

---

*No em dashes in final academic copy. Conservation is open by design; reporting it false is a success. The spine may fail productively; report it honestly if it does.*
