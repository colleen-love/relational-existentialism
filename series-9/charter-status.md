# Relational Existentialism, Series 9: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here, the charter stays clean.**

*Initialized at series start (Phase A complete, 2026-07-11). Series 9 is the response to Series 8's hardest finding: the no-god's-eye spine came back PARTIAL because the positionless collapse provably COINCIDED with relational identity (`ws1_symmetric_states_bisimilar`), leaving open whether no-god's-eye is separable from relational identity or the same fact twice named (Series 8 charter-status series-review-3, S1). Series 9 changes the engine from perspective to self-reference: a hold rich enough to range over holds cannot completely hold itself (diagonalization), and that gap, independent of relational identity by construction, is the first difference. Phases A through E (one review→address loop) are complete as of 2026-07-11: the spine is Discharged and certified diagonal-not-bisimulation (independent of relational identity), the three consequences discharged on the mechanized core, monotonicity settled Partial (Refuted-universal); series-review-1's two SERIOUS findings addressed at charter strength (the map strengthened to inspect the whole residue; dynamics forced from the spine) and its relabels applied. A second review pass (D) is the next action.*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** · **Impossibility proved** (sharp negative, first-class success; no-self-total-hold targeted as one, and INDEPENDENT of relational identity where Series 8's coincided) · **Partial** · **Failed** · **Circular** (WS7-only) · **Refuted hypothesis** (a pre-registered open law tested and found false; the monotonicity kill condition can produce this) · **Coincident** (Series 9 addition: a theorem holding only because its proof unfolds to relational identity, so not the independent fact claimed; the specific negative the spine must avoid, and naming it honestly is first-class) · **Not started**.
- The **monotonicity law is NOT a target to prove true.** It is an open law to *settle*. "Refuted" is a success outcome for it. See the kill condition (charter §5.4) and WS5.
- The **spine may fail productively.** If the diagonal re-routes through bisimulation, that is **Coincident** for the spine: Series 8's wall re-confirmed at greater depth, reported honestly, not buried. The whole series exists to test whether the diagonal is genuinely independent of relational identity.

## Program-level snapshot

| Item | Status |
|---|---|
| **Headline target** | The no-self-total-hold theorem (the diagonal spine), targeted as INDEPENDENT of relational identity. **DISCHARGED (2026-07-11) — Impossibility proved, INDEPENDENT of relational identity.** `Series9.WS1.ws1_no_self_total_hold`: on a hold-reflexive carrier the self-total fixed-point equation `insp t = diag insp` has no solution, by the Cantor/Lawvere diagonal `insp t t ↔ ¬ insp t t`. Proof-term verified (protocol §C, `spec/axiom-check-log.md`): a fixed-point contradiction referencing only `insp` and propositional logic, NO bisimulation. The repair of Series 8's Partial LANDS: no-self-total-hold is the separable second fact Series 8's series-review-3 named as the open question. |
| **The three consequences** | Plurality from one position (residue-by-diagonal, `ws2_residue_free`/`ws2_residue_distinct`, no second position in the premise — a corollary of the spine, series-review-1 F-3), forced dynamics (`ws3_dynamics_forced`: no reachable stage is Complete, forced FROM the spine, F-4; on the endogenous `prec`), layering (`ws4_residue_moves`: re-inspection closes the whole prior residue on the strengthened map, F-8; `ws4_depth_is_tower` accumulation). **DISCHARGED on the mechanized core (2026-07-11).** Universal forms floored as defended theses (WS6). |
| **The central open law** | Monotonicity of the residue under re-diagonalization. **SETTLED: PARTIAL (Refuted-universal, Discharged-on-a-fresh-class) (2026-07-11).** The kill condition FIRES from re-diagonalization's OWN mechanism (`ws5_retention_refuted`, `ws5_kill_condition`): holding a blind spot at `h₀` flips the diagonal there, so the very act of re-diagonalizing CLOSES the blind spot it holds. Strict monotonicity is Refuted; the bound is mere non-triviality; the "ever-deepening self" is retracted (`ws6_monotonicity_retracted`). Verdict datum `ws5_monotonicity_verdict = .partialV`, justified by theorems. As predicted (charter §5.4), mirroring Series 8's conservation outcome. |
| **Verdict (WS7)** | **`selfReferenceEstablished` (2026-07-11).** `ws7_verdict = Series9Verdict.selfReferenceEstablished` by `rfl` on the discharged `Audit`, whose flagship field `diagonalNotBisim` carries the spine's independence — so the verdict cannot be hand-set. `ws7_coincidence_check` contrasts the spine (denies a fixed point) with `ws1_symmetric_states_bisimilar` (produces a bisimulation) in one statement. `coincident`/`monismStands`/`Circular` are live but untriggered. |
| **Relation to Series 8** | Response, not continuation. Transcribes (does not import) Series 8's hold `x↾(x,y)` (`Hold`/`afford`), the engine, the recoverable/free-label test, and Series 7's collapse, then ADDS hold-reflexivity (the structural ingredient Series 8 lacked and the reason its spine coincided). Nothing imported across series (to be gate-confirmed at build). |

## Phase status

| Phase | Name | Status |
|---|---|---|
| A | Charter | **Complete (2026-07-11).** `charter.md`, `charter-status.md`, `protocol.md` written. |
| B | Design-all (seven `spec/wsNN-design.md` + `spec/README.md`) | **Complete (2026-07-11).** All seven designs + `spec/README.md` committed as a batch. The two Series-9 design duties settled: the hold-reflexive carrier `(dest, insp)` chosen once in WS1 (`spec/README.md` §2.3, ambient for all); the tower order `≺` derived once in WS3 as `Relation.ReflTransGen ReDiagStep` (`spec/README.md` §2.4, consumed by WS3+WS4). |
| C | Build-all (`formal/Series9/wsNN.lean`, `Series9.lean`, `AxiomCheck.lean`) | **Complete (2026-07-11).** All seven `formal/Series9/wsNN.lean` + `Series9.lean` + `AxiomCheck.lean` built; registered in `lake/lakefile.toml`. Whole package (Series7+8+9) builds clean, **sorry-free, warning-free, axiom-clean** (every headline reduces to `[propext, Classical.choice, Quot.sound]`; see `spec/axiom-check-log.md`). **The single most important check PASSED:** `ws1_no_self_total_hold`'s proof term is a Cantor/Lawvere diagonal (`insp t t ↔ ¬ insp t t`), containing NO `IsBisim`/`BehaviorallyIdentified`/`ws1_symmetric_states_bisimilar` — the spine is INDEPENDENT of relational identity; the coincidence is NOT re-hit. |
| D | Blind series-review → `spec/series-review-1.md` | **Complete (2026-07-11).** Pass 1: 2 SERIOUS (F-1 carrier-strength, F-8 point-edit map), 7 REAL, 2 COSMETIC. Flagship PASSED: the spine is a genuine diagonal, independent of relational identity, NOT Coincident. |
| E | Address `spec/series-review-1.md` | **Complete (2026-07-11).** All findings addressed (see series-review log). F-8 fixed at charter strength (map strengthened to inspect the whole residue); F-4 fixed (dynamics forced FROM the spine); F-1/F-2/F-3/F-5/F-6/F-7 honest relabels; F-10 captured run. Package rebuilds clean, sorry-free, axiom-clean. |
| (loop D→E) | Second review pass → `spec/series-review-2.md` | **Not started.** |
| F | Summaries + root README update | **Not started.** |

The canonical run is **B → C → D → E → D → E** (charter §/protocol §2), with more D→E loops added only if a review pass still returns SERIOUS findings.

## Workstream status

### WS1, The hold-reflexive carrier and the diagonal spine · *blocking, the spine*
**Status: DISCHARGED (2026-07-11) — Impossibility proved, INDEPENDENT of relational identity.** `ws1_no_self_total_hold` (the self-total fixed-point equation has no solution, `insp t t ↔ ¬ insp t t`), `ws1_insp_not_surjective` (Cantor form), `ws1_diagonal_not_bisim` (orthogonal to relational identity — holds on any carrier, no bisimulation hypothesis), `ws1_unrestricted_carrier_inconsistent` (Russell guard), `ws1_holdreflexive_not_selfloop` (§4.4 carrier-strength guard), `ws1_hold_forced` (hygiene). Proof term verified diagonal-not-bisimulation (`spec/axiom-check-log.md`), re-verified unchanged after the WS3 strengthening. **Design defect found and fixed in place (see closed log; sharpened by series-review-1 F-1/F-2):** the pre-build D5 "near-surjective onto all-but-diagonal, the sole gap" framing is both UNREALIZABLE by cardinality AND conceptually confused — the diagonal is not the sole gap but a CONSTRUCTIBLE gap uniformly exhibitable for every `insp` (Cantor's strength), which is why the spine holds for all `insp` (a feature, not a vacuity). The charter-strength guard (content is a predicate over holds, not a point) IS met (`ws1_holdreflexive_not_selfloop`, `ws3_redi_no_leaf`); the near-surjective / almost-formable framing is withdrawn from the design artifacts (charter untouched). Spine stays Discharged/Independent (a relabel, not a downgrade). `ws6_spine_scope` records the honest per-`insp` scope (F-2). Original target below.
> Target: construct a `κ`-bounded hold-reflexive carrier (a hold ranges over the space of holds, §3); define the self-total hold as a fixed-point equation; prove by diagonalization it has no solution; VERIFY (charter §4.1) the proof is Cantor/Lawvere-shaped, not a bisimulation, so no-self-total-hold is independent of relational identity. Success is Discharged (repair of Series 8), Impossibility proved (of the fixed-point kind), Coincident (the diagonal re-hits Series 8's bisimulation wall, reported honestly), or Partial (a specific witness carries it, universal resists). Sharpest risk: the coincidence re-hit (charter §5.5), the diagonal must be a fixed-point contradiction, not a behavioral identity. Twin carrier hazards: too weak (self-loop, no diagonal) and too strong (Russell-paradoxical, no model); the `κ`-bound is the guard. Ambition: *derive* no-self-total-hold as a genuine second fact, separable from relational identity, which is exactly what Series 8 could not do.

### WS2, The residue breaks the collapse from one position · *the payoff*
**Status: DISCHARGED as a corollary of the independent spine (2026-07-11; relabelled series-review-1 F-3).** The plurality-from-one-position payoff is an immediate re-reading of `ws1_no_self_total_hold`; this is the intended repair of Series 8's circularity (no second position in the premise), honest and non-circular, but a corollary of the spine, not a second load-bearing theorem. `ws2_residue_distinct` (residue distinct from every hold, NO second position in the premise — the repair of Series 8's circularity), `ws2_residue_free` (not recoverable), `ws2_residue_is_import` (recoverability ⇒ self-total hold; lands on the free-import horn), `ws2_from_one_position` (headline, tied to the independent spine), `ws2_distributed_special_case` (Series 8's `labelLoop` pair recovers as mutual residues, scoped). Original target below.
> Depends on WS1. Target: prove the residue (the face outside the self-total attempt) is distinct and FREE (not recoverable), derived from ONE position via the diagonal with no second position assumed. This is the direct repair of Series 8's circularity (`x↾(x,y) ≠ y↾(y,x)` needed `x ≠ y` in the premise). Recover Series 8's distributed perspective as a special case (mutual residues), not the source. Load-bearing dependency: the residue must be free, secured by WS1's diagonal.

### WS3, Re-diagonalization and forced dynamics · *the engine of the tower*
**Status: DISCHARGED (2026-07-11; strengthened at charter strength series-review-1 F-8/F-4/F-7).** `ReDiagStep` now `∀ h, diag insp h → insp' h h` — the next stage INSPECTS THE WHOLE PRIOR RESIDUE (was a single-point `Function.update`, which the review rightly flagged as laundering re-inspection through point-edits). `prec = ReflTransGen ReDiagStep` (the ONE endogenous order). `ws3_dynamics_forced` now proves forcing FROM the spine (`prec m m' → ¬ Complete m'`: no reachable stage is self-total), not from `Function.update` (F-4); `ws3_serial` is the honest "successor exists by construction" companion. `ws3_redi_no_leaf` relabelled (F-7): the residue is a face by type (`ws3_residue_is_face`), inhabitation conditional, witnessed full-face non-vacuously (`∃ insp, ∀ h, diag insp h`). `ws3_redi_not_function` (NF, now unconditional, no classical). `ws3_order_endogenous` (`Iff.rfl`), `ws3_imported_index_refuted` (a genuine ⊤/⊥ 2-cycle with complementary diagonals). Monotonicity still NOT built into `ReDiagStep`. Original target below.
> Target: define re-diagonalization (self-total attempt → omitted residue → next-stage hold); prove **(NL)** no leaf / `SHNE` preserved (the residue is a full unheld face, not a bare point) and **(NF)** not-a-function-of-the-prior-hold; prove a self-total hold being impossible forces successive re-inspection, so dynamics is forced FROM ONE POSITION (the diagonal analogue of Series 8's finitude-on-atomlessness). Derive the tower order endogenously (guard against charter §4.2 import). The first Lean file of the series lives here in spirit (build the re-diagonalization map; discharge NL and NF early as the seed). **Monotonicity (MG) is NOT attempted until WS5 and is never built into the re-diagonalization definition.**

### WS4, The tower and depth · *layering*
**Status: DISCHARGED on the mechanized core (2026-07-11; strengthened series-review-1 F-8/F-5).** On the strengthened map: `ws4_residue_moves` (re-inspection CLOSES the whole prior residue — the diagonal escapes its enumeration and does not linger; genuine re-inspection content, replacing the old point-flip `ws4_new_blind_spot`), `ws4_residue_moves_witness` (the residue moves to a fresh hold, tied to `insp` by `ReDiagStep`). `ws4_depth_is_tower` relabelled (F-5) as accumulation (`⊆`), a list-membership fact, tower reading in prose. `ws4_reaches_is_trace` (closure trace). Universal Partial → WS6. Original target below.
> Target: prove depth is accumulated blind spots (each re-diagonalization opens a new face the prior stage could not see, the diagonal always escapes its enumeration); reachability-into-depth as the trace of a re-diagonalization sequence, derived not axiomatic. Universal form ("all depth is diagonal residue across any construction") expected Partial (WS6).

### WS5, The monotonicity fork · *the honest open*
**Status: SETTLED — PARTIAL (Refuted-universal, Discharged-on-a-fresh-class) (2026-07-11; evidence strengthened series-review-1 F-6/F-8).** The kill condition FIRES from re-diagonalization's genuine mechanism: on the strengthened map, `ws5_retention_refuted` + `ws5_kill_condition` show a re-diagonalization INSPECTS the whole prior residue and thereby RESOLVES it (closes the blind spot) — this is the charter's mechanism, not a point-flip (F-6 improved). Strict monotonicity (retention) Refuted; the "ever-deepening self" retracted. `ws5_monotone_on_fresh` discharges strict growth on a freshness-gated chain class (narrow positive horn, honestly a hypothesis on the chain). `ws5_monotonicity_verdict = .partialV`, justified by `ws5_verdict_justified`, not hand-set. `accResidue`/`MonotoneResidue` measured OUTSIDE `ReDiagStep`. As predicted (charter §5.4), mirroring Series 8's conservation. Original target below.
> THE CENTRAL OPEN, TO BE SETTLED BY THE KILL CONDITION, NOT ASSUMED. Target: attempt **(MG)** monotone growth of the residue. `residue` measured OUTSIDE the re-diagonalization map. Run the pre-committed kill condition (charter §5.4):
- exhibit a re-diagonalization that closes a prior blind spot (net residue non-increasing) → monotonicity **Refuted** (a finding; bound downgraded to mere non-triviality; "ever-deepening self" retracted);
- prove strict growth holds and ranges → monotonicity **Discharged**;
- growth on witnesses but universal resists → monotonicity **Partial** (defended thesis floored by witnesses; epistemic/constitutive fork left open).
This is Series 9's atom-or-will door (inheriting Series 7's atom-or-will and Series 8's conservation). The math fixes the residue's shape; the reading (constitutive self-opacity vs. epistemic limit) may be left open.

### WS6, The heuristic ceiling · *the honest boundary*
**Status: DISCHARGED (2026-07-11).** `ws6_provable_core` (the floor: per-map accumulation `⊆` + per-stage residue-existence), `ws6_monotonicity_retracted` (strong monotonicity refuted, tied by `rfl` to `ws5_monotonicity_verdict = .partialV`; mere non-triviality survives), `ws6_spine_scope`, `ws6_stage_has_residue`, `ws6_universal_theses` (defended universals as documentation, not theorems). Original target below.
> Target: report the universal forms of layering (WS4) and monotonicity (WS5), where they exceed what is rangeable, as defended theses floored by the mechanized core, the Series 4/5/7/8 pattern. If the spine is Partial-on-a-witness (§5.3), the universal "every hold-reflexive carrier admits the diagonal" is reported here as a defended thesis floored by the witnessed carrier.

### WS7, The anti-circularity audit · *owns the verdict*
**Status: DISCHARGED — verdict `selfReferenceEstablished` (2026-07-11).** `ws7_audit` (the mechanized `Audit`, flagship field `diagonalNotBisim`), `ws7_verdict`/`ws7_verdict_eq` (`= selfReferenceEstablished` by `rfl`, not hand-set), `ws7_audited_not_coincident`/`_not_monism`/`_not_circular`, `ws7_coincidence_check` (contrasts the spine — denies a fixed point — with `ws1_symmetric_states_bisimilar` — produces a bisimulation — in one statement), the four guards (`ws7_no_coincidence`, `ws7_no_monotonicity_by_fiat`, `ws7_freeness_not_defined_in`, `ws7_carrier_genuine`), `ws7_strip_ledger` (the spine strips to a Cantor fixed-point, NOT a bisimulation). `coincident`/`monismStands`/`Circular` live but untriggered. Original target below.
> Series 9-specific circularity risks: (a) **the-diagonal-is-really-a-bisimulation** (charter §4.1, the coincidence re-hit, the gravest and the reason the series exists); (b) **monotonicity-by-fiat** (smuggling growth into the map); (c) **residue-recoverable-by-definition** (defining the residue trivially free); (d) **hold-reflexivity-too-weak-or-too-strong** (self-loop with no diagonal, or Russell paradox with no model). WS7 certifies the diagonal is a genuine fixed-point contradiction independent of relational identity, the residue's freeness and monotonicity's status are refuted-or-proved not defined-in, and the carrier is consistently hold-reflexive. Owns the final verdict. The **coincidence rule is promoted to a first-class spine check** here, because Series 8's central finding was a coincidence at the spine.

## The result tracker

| Result | WS | Status | Non-circular? |
|---|---|---|---|
| No self-total hold (the diagonal spine) | WS1 | **DISCHARGED — independent** | CERTIFIED: proof term is `insp t t ↔ ¬ insp t t`, a Cantor/Lawvere fixed-point contradiction; contains NO `IsBisim`/`BehaviorallyIdentified`/`ws1_symmetric_states_bisimilar`. NOT a bisimulation (`spec/axiom-check-log.md`, `ws1_diagonal_not_bisim`, `ws7_coincidence_check`). |
| Residue breaks collapse from one position | WS2 | **DISCHARGED** | CERTIFIED: `ws2_residue_free` a theorem (recoverability ⇒ self-total hold, `ws2_residue_is_import`); `ws2_residue_distinct` has no second position in the premise (`ws7_freeness_not_defined_in`). |
| Re-diagonalization: no leaf (NL) | WS3 | **DISCHARGED (relabelled)** | `ws3_residue_is_face` (face by type, no bare relatum) + `ws3_redi_no_leaf` (`∃ insp, ∀ h, diag insp h` — residue CAN be a full face); inhabitation conditional, not universal (F-7). |
| Re-diagonalization: not-a-function (NF) | WS3 | **DISCHARGED** | `ws3_redi_not_function`: two distinct successors both inspecting the residue, differing off-diagonal (unconditional). |
| Dynamics forced by incompleteness | WS3 | **DISCHARGED (from the spine)** | `ws3_dynamics_forced`: no reachable stage is Complete (uses `ws1_no_self_total_hold`, F-4). `ws3_serial` (successor by construction). Order endogenous: `ws3_order_endogenous`, `ws3_imported_index_refuted` (⊤/⊥ 2-cycle). |
| Layering = accumulated blind spots | WS4 | **DISCHARGED (core)** | `ws4_residue_moves`: re-inspection closes the whole prior residue (the diagonal escapes; genuine re-inspection, F-8). `ws4_depth_is_tower` (accumulation `⊆`, a list fact, F-5). Universal → WS6. |
| Monotonicity of the residue | WS5 | **SETTLED — Partial (Refuted-universal)** | CERTIFIED: `accResidue`/`MonotoneResidue` OUTSIDE `ReDiagStep`; `ws5_kill_condition`/`ws5_retention_refuted` fire because re-inspection RESOLVES the whole residue (genuine, F-6/F-8); verdict `.partialV` justified, not assumed. |

## Open obligations register

1. **The diagonal spine**, WS1. No-self-total-hold, proved independent of relational identity (Cantor/Lawvere-shaped, not a bisimulation). The whole repair of Series 8. **DISCHARGED (2026-07-11), independence certified at the proof-term level.**
2. **The hold-reflexive carrier**, WS1. `κ`-bounded, neither self-loop-weak nor Russell-strong. **DISCHARGED (2026-07-11):** `ws1_holdreflexive_not_selfloop`, `ws1_unrestricted_carrier_inconsistent`, κ-bound from `PkObj`.
3. **Residue plurality from one position**, WS2. **DISCHARGED (2026-07-11).**
4. **Re-diagonalization (NL)+(NF)**, WS3. **DISCHARGED (2026-07-11).**
5. **Forced dynamics, endogenous tower order**, WS3. **DISCHARGED (2026-07-11).**
6. **Layering as accumulated blind spots**, WS4. Universal Partial expected. **DISCHARGED on the core (2026-07-11); universal → WS6.**
7. **Monotonicity, settled by kill condition**, WS5. **SETTLED — PARTIAL (Refuted-universal) (2026-07-11); not assumed.**

**Recurring lesson carried from Series 7 and 8:** the sharpest result is a proved impossibility, and an honestly-reported Partial or refutation beats a smuggled success. Series 8 added the sharpest lesson of all: a theorem can hold and still fail to be the fact you claimed, if its proof coincides with a fact you already had. Series 9's spine is built to be tested against exactly that, and reporting the diagonal as Coincident (if it re-hits the wall) is a success outcome, not a failure. Neither the plurality nor the dynamics depends on monotonicity being *true*, only on its status being *settled*; and the whole series depends not on the spine being universal, but on it being non-coincident at least once.

## Closed log

*(no builds run. Phase A complete 2026-07-11: charter, charter-status, protocol written and committed. **Phase B complete 2026-07-11:** seven `spec/wsNN-design.md` + `spec/README.md` written and committed as a batch. Design headlines, per workstream:*
- *WS1 — the spine `ws1_no_self_total_hold` (self-total fixed-point equation has no solution, `insp t t ↔ ¬ insp t t`), targeted Discharged as an Impossibility INDEPENDENT of relational identity, certified by `ws1_diagonal_not_bisim` (no bisimulation/atomlessness hypothesis; orthogonal to `ws1_symmetric_states_bisimilar`). Twin carrier guards: `ws1_holdreflexive_not_selfloop` (§4.4) and `ws1_unrestricted_carrier_inconsistent` (§5.5, Russell).*
- *WS2 — `ws2_residue_free` / `ws2_residue_distinct` (residue free and distinct from ONE position, no `x ≠ y` in the premise — the repair of Series 8's circularity), tied to the semantic import test; distributed perspective recovered as mutual residues (special case, scoped).*
- *WS3 — `ReDiagStep` / `prec` (endogenous tower order = `ReflTransGen ReDiagStep`); (NL) `ws3_redi_no_leaf`, (NF) `ws3_redi_not_function`, `ws3_dynamics_forced` (seriality), `ws3_imported_index_refuted` (2-cycle, §4.2 guard). Monotonicity NOT built into the map.*
- *WS4 — `ws4_new_blind_spot` (the diagonal escapes its enumeration), `ws4_depth_is_tower` (accumulation `⊆`), `ws4_reaches_is_trace`; universal Partial → WS6.*
- *WS5 — the monotonicity fork: PREDICTED **Partial** (Refuted-universal via `ws5_kill_condition`/`ws5_retention_refuted` — re-diagonalization closes the blind spot it holds — Discharged on a fresh-chain class). Kill condition pre-registered; not assumed.*
- *WS6 — floor + defended universals + `ws6_monotonicity_retracted` (strong form retracted, non-triviality survives) + spine-scope ledger.*
- *WS7 — `Series9Verdict`, the `Audit` (flagship field `diagonalNotBisim`), `ws7_coincidence_check`, four guards; predicted verdict `selfReferenceEstablished`.*

**Phase C complete 2026-07-11:** all seven `formal/Series9/wsNN.lean` + `Series9.lean` + `AxiomCheck.lean` built and committed; `Series9` registered in `lake/lakefile.toml`. Whole package (Series7+8+9) builds clean: **sorry-free, warning-free, axiom-clean** (every headline reduces to `[propext, Classical.choice, Quot.sound]`; full record in `spec/axiom-check-log.md`).

- ***THE single most important check PASSED (the reason the series exists).*** `#print ws1_no_self_total_hold` yields the proof term `fun … dest insp a => Exists.casesOn a fun t ht => let h := ht t; let np := fun hp => h.mp hp hp; np (h.mpr np)` — a pure Cantor/Lawvere diagonal (`insp t t ↔ ¬ insp t t → False`), referencing ONLY `insp`, `Iff.mp/mpr`, `Exists.casesOn`. It contains **NO** `IsBisim`/`IsBisimL`/`BehaviorallyIdentified`/`ws1_symmetric_states_bisimilar`/`hneRel`/`SReaches`. **The spine is INDEPENDENT of relational identity; the Series 8 coincidence is NOT re-hit.** Series 9's headline lands: no-self-total-hold is the separable second fact Series 8 could not produce.
- ***Design defect found and fixed in place (WS1 D5), per protocol §C.*** The pre-build `ws1_design.md` D5 proposed an inspection "near-surjective onto every content except the diagonal" as the hold-reflexivity witness. This is **UNREALIZABLE by cardinality**: the complement of a single point in `HoldPred dest = Hold dest → Prop` still has cardinality `2^|Hold| > |Hold|`, so no map from `Hold` covers it. Fixed in place (not retargeted to whatever the proof yielded): D5 (`ws1_holdreflexive_not_selfloop`) now witnesses hold-reflexivity correctly — the carrier expresses a genuine NON-POINT content (`⊤` holding two distinct holds), which a self-loop (point-content, `inspLoop h h' ↔ h' = h`) cannot. This is the faithful §4.4 guard; the design doc `ws1-design.md` D5 and its NB note record the correction. No downstream workstream depended on the near-surjective horn, so no reopening.
- ***Two faithful concretizations (not retargets), each noted in-code.*** (i) WS3 `ws3_imported_index_refuted` is witnessed on the concrete periodic carrier `twoLoop` (as Series 8's analogue was), the design's generic `{X} dest` needing a carrier with holds; the 2-cycle is genuine and a 1-cycle is impossible by the spine. (ii) WS4 `ws4_depth_grows_witness` is likewise on `twoLoop`. Both are honest witness-carrier choices, consistent with the designs' "witness, scoped" framing.

**Phase D + E (first review→address loop) complete 2026-07-11:** `spec/series-review-1.md` written (blind), all findings addressed (see the series-review log above). The two SERIOUS findings were fixed at charter strength: F-8 (the map's steps were single-point edits) by strengthening `ReDiagStep` to inspect the whole prior residue and re-proving WS3/WS4/WS5; F-1 (carrier-strength) resolved as an honest relabel (the design's near-surjective framing was cardinality-confused and is withdrawn; the charter-strength guard is met). F-4 fixed (dynamics forced from the spine); F-2/F-3/F-5/F-6/F-7 honest relabels; F-10 the axiom check re-run and captured. Package rebuilds clean, sorry-free, warning-free, axiom-clean (captured run in `spec/axiom-check-log.md`); the spine proof term is unchanged (still the pure diagonal, no bisimulation). *Next action: Phase D, the second blind review pass → `spec/series-review-2.md`.)*

## Series-review log

### Pass 1 — `spec/series-review-1.md` (2026-07-11, blind, adversarial, batched) → addressed (Phase E)

**Flagship result, confirmed by the review: the spine is a genuine Cantor/Lawvere diagonal, independent
of relational identity — NOT Coincident.** The one thing the series exists to establish holds; Series 8's
wall is not re-hit. Every finding below is a failure of *reach* or *labelling*, not of honesty (nothing
Coincident, Circular, or assumed-in). All addressed; the spine's Discharged/Independent status is
unchanged.

**F-8 (SERIOUS, WS3 owning; WS4/WS5 consuming) — the map's steps were single-point `Function.update`s,
so depth/dynamics/monotonicity laundered through point-edits, not re-inspection. FIXED at charter
strength.** `ReDiagStep` strengthened from `∃ h₀, insp' h₀ = diag insp` (a point-edit) to
`∀ h, diag insp h → insp' h h` — the next stage genuinely INSPECTS THE WHOLE PRIOR RESIDUE (self-holds
every prior blind spot). Consequences re-proved against it and are now genuine: WS4 `ws4_residue_moves`
(re-inspection CLOSES the whole prior residue — the diagonal escapes its enumeration, does not linger);
WS5 `ws5_retention_refuted`/`ws5_kill_condition` now fire because inspecting the residue RESOLVES it
(the charter's mechanism), not by a point-flip. Endogenous order, seriality, imported-index refutation
(now a genuine ⊤/⊥ 2-cycle with complementary diagonals) all re-proved. Monotonicity remains Partial
(Refuted-universal), now on genuine evidence.

**F-1 (SERIOUS, WS1) — carrier-strength witness. Resolved as an honest relabel (design over-specified).**
The design's `ws1_holdreflexive_not_selfloop` "near-surjective onto all-but-diagonal" horn is UNREALIZABLE
by cardinality (the range of any `insp` misses `2^|Hold|`-many contents, not one) AND conceptually
confused: the diagonal is not "the sole gap," it is a CONSTRUCTIBLE gap uniformly exhibitable for every
`insp` (Cantor's strength), which is why the spine holds for all `insp` — a feature, not a vacuity. The
charter-strength guard (charter §3/§5.5: content is a predicate over holds, not a successor point) IS met
(`ws1_holdreflexive_not_selfloop` witnesses non-point content; `ws3_redi_no_leaf` witnesses a full-face
residue). The near-surjective / almost-formable framing is withdrawn from `ws1-design.md` D5, README §2.3,
and the code docstring; charter untouched (the confusion was in the design artifact, not the charter). No
downstream reopening. **This is a relabel, not a spine downgrade:** the spine stays Discharged/Independent.

**F-4 (REAL, WS3) — forced dynamics did not use the impossibility. FIXED.** `ws3_dynamics_forced` now
proves `prec dest m m' → ¬ Complete m'` (no reachable stage is self-total), genuinely using
`ws1_no_self_total_hold` — the forcing is the theorem's content. Seriality (a successor exists by
construction) is split off honestly as `ws3_serial`.

**F-7 (REAL, WS3) — (NL) was `id` on its hypothesis. RELABELLED honestly.** The residue is NOT always
inhabited (e.g. `fun _ _ => True` has empty residue), so (NL) is not an inhabitation theorem; it is
face-shape-by-type (`ws3_residue_is_face`) plus a positive non-vacuous witness (`ws3_redi_no_leaf`:
`∃ insp, ∀ h, diag insp h` — the residue CAN be the full face). The leaf trap is genuinely avoided (the
residue is a `HoldPred`, never a bare relatum).

**F-3 (REAL, WS2) — plurality is a corollary of the spine. RELABELLED.** WS2's row now reads "Discharged
as a corollary of the independent spine (the intended repair of Series 8's circularity)," not an
independent load-bearing payoff. The non-circularity (no second position in the premise) is genuine.

**F-5 (REAL, WS4) — `ws4_depth_is_tower` is a list-subset fact. RELABELLED** as accumulation (`⊆`) of the
accumulated residue, a list-membership fact; the tower reading is prose, flagged. The genuine depth
content is now `ws4_residue_moves` (F-8).

**F-6 (REAL, WS5) — both horns thin. IMPROVED + relabelled.** The Refuted horn is no longer a point-flip:
with the strengthened map it fires because re-inspection resolves the whole residue (genuine, the
charter's mechanism). The Discharged horn remains conditional on chain-freshness (honestly a hypothesis
on the chain, not the map). Verdict stays Partial, now on genuine evidence.

**F-2 (REAL, WS1/WS6) — "independent" is orthogonality-by-universality. RELABELLED.** `ws6_spine_scope`'s
docstring now records the honest scope: the diagonal is a per-`insp` theorem holding uniformly for every
`insp` (Cantor's uniform strength = the orthogonality that repairs Series 8); no rich-carrier witness
exists or is needed.

**F-10 (REAL, build) — axiom check was a static assertion. FIXED.** `lake build Series9.AxiomCheck` was
run and its `#print axioms` stdout captured into `spec/axiom-check-log.md` (every headline reduces to the
standard three); the spine proof term was re-printed and is unchanged after the WS3 strengthening.

**F-11, F-12 (COSMETIC) — noted.** F-11: the `Audit`'s flagship `diagonalNotBisim` is the field that
matters and holds; the others now carry genuine (strengthened) content. F-12: `ws2_distributed_special_case`
uses the all-false inspection (both holds vacuously in the residue); it recovers the `labelLoop` pair as
scoped, explicitly not universal — acceptable, noted.

*Net: the flagship stands; F-8 and F-4 fixed at charter strength (map now genuinely inspects the whole
residue; dynamics forced from the spine); F-1 and the rest are honest relabels. A second review pass (D)
is warranted to confirm the strengthened map closes F-8 cleanly.*

---

*No em dashes in final academic copy. Monotonicity is open by design; reporting it false is a success. The spine may fail productively; if the diagonal re-hits Series 8's coincidence, report it honestly as Coincident. The entire series is the test of one question Series 8 left open: is no-god's-eye separable from relational identity? The diagonal is the candidate answer, and it is not assumed to work.*
