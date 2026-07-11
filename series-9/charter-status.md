# Relational Existentialism, Series 9: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here, the charter stays clean.**

*Initialized at series start (Phase A complete, 2026-07-11). Series 9 is the response to Series 8's hardest finding: the no-god's-eye spine came back PARTIAL because the positionless collapse provably COINCIDED with relational identity (`ws1_symmetric_states_bisimilar`), leaving open whether no-god's-eye is separable from relational identity or the same fact twice named (Series 8 charter-status series-review-3, S1). Series 9 changes the engine from perspective to self-reference: a hold rich enough to range over holds cannot completely hold itself (diagonalization), and that gap, independent of relational identity by construction, is the first difference. Phases B through F have NOT been run. Nothing below is proved. This file is the honest ledger and currently records intentions and pre-registered targets only.*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** · **Impossibility proved** (sharp negative, first-class success; no-self-total-hold targeted as one, and INDEPENDENT of relational identity where Series 8's coincided) · **Partial** · **Failed** · **Circular** (WS7-only) · **Refuted hypothesis** (a pre-registered open law tested and found false; the monotonicity kill condition can produce this) · **Coincident** (Series 9 addition: a theorem holding only because its proof unfolds to relational identity, so not the independent fact claimed; the specific negative the spine must avoid, and naming it honestly is first-class) · **Not started**.
- The **monotonicity law is NOT a target to prove true.** It is an open law to *settle*. "Refuted" is a success outcome for it. See the kill condition (charter §5.4) and WS5.
- The **spine may fail productively.** If the diagonal re-routes through bisimulation, that is **Coincident** for the spine: Series 8's wall re-confirmed at greater depth, reported honestly, not buried. The whole series exists to test whether the diagonal is genuinely independent of relational identity.

## Program-level snapshot

| Item | Status |
|---|---|
| **Headline target** | The no-self-total-hold theorem (the diagonal spine), targeted as INDEPENDENT of relational identity. **NOT STARTED.** The repair Series 9 attempts: prove by diagonalization that the self-total hold has no solution on a hold-reflexive carrier, with the proof verified Cantor/Lawvere-shaped (a fixed-point contradiction) rather than a bisimulation. Success repairs Series 8's Partial by producing the separable second fact Series 8's series-review-3 named as the open question. |
| **The three consequences** | Plurality from one position (residue-by-diagonal), forced dynamics (successive re-inspection), layering (accumulated blind spots). **NOT STARTED.** All targeted as Discharged on the mechanized core; universal forms expected Partial. |
| **The central open law** | Monotonicity of the residue under re-diagonalization. **NOT STARTED. Open by design, settled by the kill condition, never assumed.** Predicted outcome (charter §5.4, not a commitment): strict form likely Refuted or Partial, "ever-deepening self" likely retracted, mirroring Series 8's conservation outcome. |
| **Verdict (WS7)** | **NOT STARTED.** Target: a `selfReferenceEstablished`-style verdict tagged onto a discharged `Audit` whose spine field is the genuine diagonal (independent of relational identity), not a coincidence. |
| **Relation to Series 8** | Response, not continuation. Transcribes (does not import) Series 8's hold `x↾(x,y)` (`Hold`/`afford`), the engine, the recoverable/free-label test, and Series 7's collapse, then ADDS hold-reflexivity (the structural ingredient Series 8 lacked and the reason its spine coincided). Nothing imported across series (to be gate-confirmed at build). |

## Phase status

| Phase | Name | Status |
|---|---|---|
| A | Charter | **Complete (2026-07-11).** `charter.md`, `charter-status.md`, `protocol.md` written. |
| B | Design-all (seven `spec/wsNN-design.md` + `spec/README.md`) | **Complete (2026-07-11).** All seven designs + `spec/README.md` committed as a batch. The two Series-9 design duties settled: the hold-reflexive carrier `(dest, insp)` chosen once in WS1 (`spec/README.md` §2.3, ambient for all); the tower order `≺` derived once in WS3 as `Relation.ReflTransGen ReDiagStep` (`spec/README.md` §2.4, consumed by WS3+WS4). |
| C | Build-all (`formal/Series9/wsNN.lean`, `Series9.lean`, `AxiomCheck.lean`) | **Not started.** |
| D | Blind series-review → `spec/series-review-1.md` | **Not started.** |
| E | Address | **Not started.** |
| (loop D→E) | Second review pass → `spec/series-review-2.md` | **Not started.** |
| F | Summaries + root README update | **Not started.** |

The canonical run is **B → C → D → E → D → E** (charter §/protocol §2), with more D→E loops added only if a review pass still returns SERIOUS findings.

## Workstream status

### WS1, The hold-reflexive carrier and the diagonal spine · *blocking, the spine*
**Status: Not started.** Target: construct a `κ`-bounded hold-reflexive carrier (a hold ranges over the space of holds, §3); define the self-total hold as a fixed-point equation; prove by diagonalization it has no solution; VERIFY (charter §4.1) the proof is Cantor/Lawvere-shaped, not a bisimulation, so no-self-total-hold is independent of relational identity. Success is Discharged (repair of Series 8), Impossibility proved (of the fixed-point kind), Coincident (the diagonal re-hits Series 8's bisimulation wall, reported honestly), or Partial (a specific witness carries it, universal resists). Sharpest risk: the coincidence re-hit (charter §5.5), the diagonal must be a fixed-point contradiction, not a behavioral identity. Twin carrier hazards: too weak (self-loop, no diagonal) and too strong (Russell-paradoxical, no model); the `κ`-bound is the guard. Ambition: *derive* no-self-total-hold as a genuine second fact, separable from relational identity, which is exactly what Series 8 could not do.

### WS2, The residue breaks the collapse from one position · *the payoff*
**Status: Not started.** Depends on WS1. Target: prove the residue (the face outside the self-total attempt) is distinct and FREE (not recoverable), derived from ONE position via the diagonal with no second position assumed. This is the direct repair of Series 8's circularity (`x↾(x,y) ≠ y↾(y,x)` needed `x ≠ y` in the premise). Recover Series 8's distributed perspective as a special case (mutual residues), not the source. Load-bearing dependency: the residue must be free, secured by WS1's diagonal.

### WS3, Re-diagonalization and forced dynamics · *the engine of the tower*
**Status: Not started.** Target: define re-diagonalization (self-total attempt → omitted residue → next-stage hold); prove **(NL)** no leaf / `SHNE` preserved (the residue is a full unheld face, not a bare point) and **(NF)** not-a-function-of-the-prior-hold; prove a self-total hold being impossible forces successive re-inspection, so dynamics is forced FROM ONE POSITION (the diagonal analogue of Series 8's finitude-on-atomlessness). Derive the tower order endogenously (guard against charter §4.2 import). The first Lean file of the series lives here in spirit (build the re-diagonalization map; discharge NL and NF early as the seed). **Monotonicity (MG) is NOT attempted until WS5 and is never built into the re-diagonalization definition.**

### WS4, The tower and depth · *layering*
**Status: Not started.** Target: prove depth is accumulated blind spots (each re-diagonalization opens a new face the prior stage could not see, the diagonal always escapes its enumeration); reachability-into-depth as the trace of a re-diagonalization sequence, derived not axiomatic. Universal form ("all depth is diagonal residue across any construction") expected Partial (WS6).

### WS5, The monotonicity fork · *the honest open*
**Status: Not started. THE CENTRAL OPEN, TO BE SETTLED BY THE KILL CONDITION, NOT ASSUMED.** Target: attempt **(MG)** monotone growth of the residue. `residue` measured OUTSIDE the re-diagonalization map. Run the pre-committed kill condition (charter §5.4):
- exhibit a re-diagonalization that closes a prior blind spot (net residue non-increasing) → monotonicity **Refuted** (a finding; bound downgraded to mere non-triviality; "ever-deepening self" retracted);
- prove strict growth holds and ranges → monotonicity **Discharged**;
- growth on witnesses but universal resists → monotonicity **Partial** (defended thesis floored by witnesses; epistemic/constitutive fork left open).
This is Series 9's atom-or-will door (inheriting Series 7's atom-or-will and Series 8's conservation). The math fixes the residue's shape; the reading (constitutive self-opacity vs. epistemic limit) may be left open.

### WS6, The heuristic ceiling · *the honest boundary*
**Status: Not started.** Target: report the universal forms of layering (WS4) and monotonicity (WS5), where they exceed what is rangeable, as defended theses floored by the mechanized core, the Series 4/5/7/8 pattern. If the spine is Partial-on-a-witness (§5.3), the universal "every hold-reflexive carrier admits the diagonal" is reported here as a defended thesis floored by the witnessed carrier.

### WS7, The anti-circularity audit · *owns the verdict*
**Status: Not started.** Series 9-specific circularity risks: (a) **the-diagonal-is-really-a-bisimulation** (charter §4.1, the coincidence re-hit, the gravest and the reason the series exists); (b) **monotonicity-by-fiat** (smuggling growth into the map); (c) **residue-recoverable-by-definition** (defining the residue trivially free); (d) **hold-reflexivity-too-weak-or-too-strong** (self-loop with no diagonal, or Russell paradox with no model). WS7 certifies the diagonal is a genuine fixed-point contradiction independent of relational identity, the residue's freeness and monotonicity's status are refuted-or-proved not defined-in, and the carrier is consistently hold-reflexive. Owns the final verdict. The **coincidence rule is promoted to a first-class spine check** here, because Series 8's central finding was a coincidence at the spine.

## The result tracker

| Result | WS | Status | Non-circular? |
|---|---|---|---|
| No self-total hold (the diagonal spine) | WS1 | **Not started** | To be certified: the proof must be Cantor/Lawvere-shaped (fixed-point contradiction), verified independent of relational identity by unfolding, NOT a bisimulation (the Series 8 coincidence the series exists to avoid). |
| Residue breaks collapse from one position | WS2 | **Not started** | To be certified: freeness a theorem, not defined-in; no second position in the premise. |
| Re-diagonalization: no leaf (NL) | WS3 | **Not started** | — |
| Re-diagonalization: not-a-function (NF) | WS3 | **Not started** | — |
| Dynamics forced by incompleteness | WS3 | **Not started** | To be certified: tower order endogenous, not an imported index. |
| Layering = accumulated blind spots | WS4 | **Not started** | To be certified: each residue genuinely unseen by the prior stage. |
| Monotonicity of the residue | WS5 | **Not started** | To be certified: `residue` measured OUTSIDE the map; refuted-by-witness-or-proved, never assumed. |

## Open obligations register

1. **The diagonal spine**, WS1. No-self-total-hold, proved independent of relational identity (Cantor/Lawvere-shaped, not a bisimulation). The whole repair of Series 8. **Not started.**
2. **The hold-reflexive carrier**, WS1. `κ`-bounded, neither self-loop-weak nor Russell-strong. **Not started.**
3. **Residue plurality from one position**, WS2. **Not started.**
4. **Re-diagonalization (NL)+(NF)**, WS3. The first build. **Not started.**
5. **Forced dynamics, endogenous tower order**, WS3. **Not started.**
6. **Layering as accumulated blind spots**, WS4. Universal Partial expected. **Not started.**
7. **Monotonicity, settled by kill condition**, WS5. **Open by design; must not be assumed.** **Not started.**

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

*Next action: Phase C, build all seven in `formal/Series9/wsNN.lean`, WS1 first; the single most important build check is `#print`-ing `ws1_no_self_total_hold` to confirm its proof term is a diagonal fixed-point contradiction and does NOT reduce to `ws1_symmetric_states_bisimilar`.)*

## Series-review log

*(empty; no review passes run. Phase D writes `spec/series-review-1.md`.)*

---

*No em dashes in final academic copy. Monotonicity is open by design; reporting it false is a success. The spine may fail productively; if the diagonal re-hits Series 8's coincidence, report it honestly as Coincident. The entire series is the test of one question Series 8 left open: is no-god's-eye separable from relational identity? The diagonal is the candidate answer, and it is not assumed to work.*
