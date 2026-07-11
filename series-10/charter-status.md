# Relational Existentialism, Series 10: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here, the charter stays clean.**

*Initialized at series start (Phase A complete, 2026-07-11). Series 10 is the response to Series 9's hardest finding: the diagonal spine held (self-reference cannot close, independent of relational identity) and the residue was free, but on a FIXED carrier the residue could only MOVE (`ws4_residue_moves`), and a moving hole is still one hole (series-9 series-review-1 bottom line + inter-series seed). Series 10 lets the free residue REIFY into a new relatum via `reify : F(Ω) → Ω`, licensed by the founding equation `Ω ≅ F(Ω)`, so the carrier GROWS. The Series 9 diagonal makes the growth genuine: a reified self-relation recoverable from the relating would reconstruct a self-total hold, which the diagonal forbids, so blindness is productive. The κ-bound is deliberate SCAFFOLDING (Series 10 proves the engine on a known-safe carrier); its endogenous replacement by finiteness of attention is deferred to Series 11 by design. Phases B through F have NOT been run. Nothing below is proved. This file records intentions and pre-registered targets only.*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** · **Discharged-on-scaffold** (proved on the κ-bounded carrier, pending κ-removal in Series 11; honest and first-class, NOT a claim of endogenous boundedness) · **Impossibility proved** (sharp negative, first-class; CLOSE-forbidden is one) · **Partial** · **Failed** · **Circular** (WS7-only) · **Refuted hypothesis** (a pre-registered open law tested and found false; the crown kill condition can produce this, reported as FATAL, a success) · **Bookkeeping** (Series 10 addition: a "growth" that is only a longer external record while the carrier is unchanged up to bisimulation; the specific negative to avoid at the payoff, naming it honestly is first-class) · **Not started**.
- The **crown (reflexive fold) is NOT a target to prove true.** It is an open law to *settle*. "FATAL" (refuted) is a success outcome for it. See the kill condition (charter §5.4) and WS5.
- The **endogenous bound is OUT OF SCOPE.** Series 10 uses κ as scaffolding and proves nothing that relies on κ being small; removing κ and testing finiteness-of-attention as the endogenous bound is Series 11. A Series 10 result claiming endogenous self-bounding would be overclaiming (charter §5.3, §5.5 κ-by-fiat).
- The **payoff may fail productively.** If `reify` is too weak and growth is a longer `List` not a bigger carrier, that is **Bookkeeping**: Series 9's moving hole re-hit one level up, reported honestly, not buried.

## Program-level snapshot

| Item | Status |
|---|---|
| **Headline target** | Productive blindness: on a κ-bounded reifying carrier, each reified self-relation is FREE (not recoverable), routing through the Series 9 diagonal, so the carrier genuinely grows. **NOT STARTED.** The repair of Series 9's moving hole: a free reified relatum differentiates by its EXISTENCE (not bisimulation-invariant), where Series 9's residue only relocated (bisimulation-invariant, still collapsible). |
| **The three consequences** | Genuine growth (not bookkeeping): `Ω_{α+1}` does not bisim-embed into `Ω_α`. Breaks the Series 7 collapse: distinct reification histories not merged by `BehaviorallyIdentified`. Close-or-fold dichotomy with CLOSE forbidden by the diagonal. **NOT STARTED.** |
| **The central open law** | FOLD vs FATAL. CLOSE is forbidden (a theorem, from the diagonal). Whether the alternative is endogenous-reflexive (crown) or unbounded-without-scaffolding (fatal) is **OPEN by design, settled by the kill condition, never assumed, never relying on small κ.** Predicted (charter §5.4, not a commitment): likely Partial or FATAL on the bounded carrier, with the crown's survival of κ-removal a Series 11 question. |
| **Verdict (WS7)** | **NOT STARTED.** Target: a verdict tagged onto a discharged `Audit` whose spine field is genuine free reification (routing through the diagonal, growth strict-and-internal not a `List`, fold as reflexivity not cardinality, no reliance on small κ). |
| **Relation to Series 9** | Response, not continuation. Transcribes (does not import) Series 9's `PkObj κ`, `dest`, `SHNE`, `BehaviorallyIdentified`, the diagonal `ws1_no_self_total_hold`, the free residue `ws2_residue_free`, and the Series 4/WS2 recoverability test, then ADDS `reify : F(Ω) → Ω` (the ingredient Series 9 lacked and the reason its hole could only move). Nothing imported across series (to be gate-confirmed at build). |
| **Relation to Series 11 (forecast)** | Series 10 proves the engine on scaffolding; Series 11 removes κ and tests finiteness of attention as the endogenous bound. Whatever horn (Discharged-on-scaffold / FATAL / Partial) Series 10 delivers for the fold is Series 11's seed. |

## Phase status

| Phase | Name | Status |
|---|---|---|
| A | Charter | **Complete (2026-07-11).** `charter.md`, `charter-status.md`, `protocol.md` written. |
| B | Design-all (seven `spec/wsNN-design.md` + `spec/README.md`) | **Not started.** |
| C | Build-all (`formal/Series10/wsNN.lean`, `Series10.lean`, `AxiomCheck.lean`) | **Not started.** |
| D | Blind series-review → `spec/series-review-1.md` | **Not started.** |
| E | Address | **Not started.** |
| (loop D→E) | Second review pass → `spec/series-review-2.md` | **Not started.** |
| F | Close (summaries + root README) | **Not started.** |

The canonical run is **B → C → D → E → D → E** (protocol §2), with more D→E loops added only if a review pass still returns SERIOUS findings.

## Workstream status

### WS1, The reifying carrier and productive blindness · *blocking, the spine*
**Status: Not started.** Target: define `reify : F(Ω) → Ω` on the κ-bounded carrier (forward map of `Ω ≅ F(Ω)`, transcribing Series 9's `PkObj κ`, `dest`, `ws1_no_self_total_hold`, `ws2_residue_free`). Prove **(FR)** free reification (the reified self-relation is not recoverable, routing through the diagonal) and **CLOSE-forbidden** (a totality-relatum is a self-total hold, forbidden). Certify the freeness proof routes through the diagonal, NOT a fresh assumption. Success is Discharged / Discharged-on-scaffold (the repair of Series 9's moving hole), Partial (per-witness), or a design-defect report if the tower closes (a smuggled self-total hold, charter §4.5). Sharpest risk: growth is bookkeeping (charter §5.5), the reified relatum must be proved genuinely new. Twin `reify` hazards: too weak (constant-up-to-bisim, bookkeeping) and too strong (closes into a top, smuggles a self-total hold past the diagonal); the razor Series 9's WS1 walked, now at the tower level. WS1 fixes `reify` and the carrier, ambient for all.

### WS2, Genuine growth, not bookkeeping · *the payoff*
**Status: Not started.** Depends on WS1. Target: prove `Ω_{α+1}` does NOT bisimulation-embed into `Ω_α` (strict internal growth, the direct repair of Series 9's moving hole), and that two distinct reification histories are not merged by `BehaviorallyIdentified` (breaks the Series 7 collapse where the moving hole could not). Load-bearing dependency: strictness of growth is secured by WS1's freeness. This is where Series 9's F-8 ghost (growth-as-external-`List`) must be exorcised at the carrier level.

### WS3, The reification tower and its order · *the engine of the tower*
**Status: Not started.** Target: construct the ordinal-indexed tower on the bounded carrier; prove **(NL)** reification preserves `SHNE` (the reified relation is a full relatum, never a leaf); derive the tower order endogenously from reification sequences (guard against charter §4.1 imported-ordinal clock); prove well-foundedness of the tower as a genuine object (the κ-scaffolding's real job, charter §5.5). The first Lean file of the series in spirit (build `reify` and the tower; discharge NL and endogenous-order early as the seed). **The fold (crown) is NOT attempted here and is never folded into `reify` or the tower construction** — it is WS5's.

### WS4, Close-or-fold: the dichotomy and CLOSE-forbidden · *the structural heart*
**Status: Not started.** Target: prove the close-or-fold dichotomy is exhaustive; prove **CLOSE is forbidden by the diagonal** (a totality-relatum is self-total, `ws1_no_self_total_hold` forbids it) as an Impossibility. Define the distributed-reflexivity (fold) predicate precisely, measured as reflexivity NOT as staying-under-κ (guard against charter §4.4 κ-by-fiat). Target: dichotomy + CLOSE-forbidden Discharged; fold-vs-fatal handed to WS5.

### WS5, The fold-or-fatal fork · *the honest open*
**Status: Not started. THE CENTRAL OPEN, TO BE SETTLED BY THE KILL CONDITION, NOT ASSUMED.** Target: attempt the crown (distributed reflexivity at every stage). Run the pre-committed kill condition (charter §5.4):
- exhibit a free tower that, with κ removed, strictly proliferates past every bounded stage with NO distributed-reflexivity fold → crown **FATAL** (refuted; "self-reference buys the many only at the cost of the whole"; the self-bounding hope retracted; a success outcome);
- exhibit distributed reflexivity at every stage on the bounded carrier → crown **Discharged-on-scaffold** (Series 11 licensed to remove κ);
- neither → crown **Partial** (defended thesis floored by the mechanized core; fold-or-fatal left open).
This is Series 10's atom-or-will door (inheriting Series 7's atom-or-will, Series 8's conservation, Series 9's monotonicity). Forbidden from assuming the crown OR relying on small κ. **Explicitly scopes the endogenous-bound question OUT** (Series 11).

### WS6, The heuristic ceiling and the Series 11 handoff · *the honest boundary*
**Status: Not started.** Target: report the universal forms of productive blindness and the fold, where they exceed what is rangeable, as defended theses floored by the mechanized core (the Series 4/5/7/8/9 pattern). **Explicitly state the Series 11 inheritance:** the κ-removal, the finiteness-of-attention unification, and whichever horn (fold/fatal/partial) Series 10 delivered. If the spine is Partial-on-a-witness (charter §5.3), the universal "every κ-bounded reifying carrier grows freely" is reported here as a defended thesis floored by the witnessed carrier.

### WS7, The anti-circularity audit · *owns the verdict*
**Status: Not started.** Series 10-specific circularity risks: (a) **growth-is-bookkeeping** (charter §4.3, the moving-hole re-hit, PROMOTED to first-class, Series 9's central inheritance); (b) **reify-smuggles-a-self-total-hold** (charter §4.5, trivial closure); (c) **κ-by-fiat** (charter §4.4, conservation relocated, PROMOTED to first-class, Series 8's central inheritance); (d) **reification-is-an-import** (charter §4.1). WS7 certifies productive blindness routes through the diagonal (not a fresh assumption), growth is strict-and-internal (not a `List`), the fold is reflexivity (not cardinality), and no result relies on small κ. Owns the final verdict.

## The result tracker

| Result | WS | Status | Non-circular? |
|---|---|---|---|
| Free reification (productive blindness) | WS1 | **Not started** | To be certified: freeness routes through the diagonal (`ws1_no_self_total_hold` / `ws2_residue_free`), NOT a fresh assumption. |
| CLOSE forbidden (no totality-relatum) | WS1/WS4 | **Not started** | To be certified: the forbidding is the diagonal (a totality-relatum is self-total), an Impossibility. |
| Strict internal growth (not bookkeeping) | WS2 | **Not started** | To be certified: `Ω_{α+1}` does not bisim-embed into `Ω_α`; growth is carrier-extension, not a `List` (the Series 9 F-8 exorcism). |
| Breaks the Series 7 collapse | WS2 | **Not started** | To be certified: distinct histories not merged by `BehaviorallyIdentified`; existence-of-a-free-relatum is not bisim-invariant. |
| Reification preserves SHNE (NL) | WS3 | **Not started** | — |
| Endogenous tower order | WS3 | **Not started** | To be certified: order derived from reification sequences, not an imported ordinal. |
| The close-or-fold dichotomy | WS4 | **Not started** | To be certified: exhaustive; CLOSE forbidden as an Impossibility, not asserted. |
| The fold (crown) | WS5 | **Not started** | To be certified: fold measured as reflexivity OUTSIDE the tower construction; refuted-by-proliferation-when-κ-removed or Discharged-on-scaffold, never assumed, never small-κ. |

## Open obligations register

1. **Productive blindness (free reification)**, WS1. The reified self-relation is free, routing through the diagonal. The whole engine. **Not started.**
2. **`reify` well-defined, neither bookkeeping-weak nor closing-strong**, WS1. **Not started.**
3. **Strict internal growth**, WS2. `Ω_{α+1}` does not bisim-embed into `Ω_α`. The Series 9 moving-hole repair. **Not started.**
4. **Reification preserves SHNE (NL) + endogenous tower order**, WS3. The first build. **Not started.**
5. **Well-foundedness of the tower** (the κ-scaffolding's job), WS3. **Not started.**
6. **CLOSE forbidden + the dichotomy exhaustive**, WS4. **Not started.**
7. **The fold, settled by kill condition**, WS5. **Open by design; must not be assumed; must not rely on small κ.** **Not started.**
8. **The Series 11 handoff** (κ-removal, finiteness-of-attention unification), WS6. **Not started (forecast only).**

**Recurring lesson carried from Series 7, 8, and 9:** the sharpest result is a proved impossibility (CLOSE-forbidden is one), and an honestly-reported Partial or refutation beats a smuggled success. Series 8 added: a theorem can hold and still fail to be the fact you claimed (coincidence). Series 9 added: a payoff can be genuine yet thin, narrating self-inspection while proving `Function.update` (the bookkeeping ghost). Series 10's payoff is built to be tested against exactly that at the carrier level: reporting growth as Bookkeeping (if `reify` is too weak) or the fold as FATAL (if the crown fails) are success outcomes, not failures. Neither the growth nor the plurality depends on the crown being *true*, only on its status being *settled*; and the whole series depends not on the bound being endogenous (that is Series 11), but on reification generating strict internal growth at least once, which Series 9's fixed field could not.

## Closed log

*(empty; no builds run. Phase A complete 2026-07-11: charter, charter-status, protocol written and committed to the Series 10 working branch. Next action: Phase B, design all seven workstreams against `charter.md`, settling the two Series-10-specific design duties, `reify` defined once in WS1 and the tower order derived once in WS3, per protocol §2.)*

**Process change carried into Series 10 (the anti-loop discipline, protocol §0.2, §0.2a, Phase D recurrence check, Phase E sequence).** Diagnosed from Series 8, where the spine finding S1 recurred across all three review passes: each Phase E "addressed" it by building a new, cheaper theorem that established the antecedent of the charter's own pre-registered Failed condition and labelled the result a success, rather than reporting the Partial the charter had anticipated; the loop stopped only when pass 3 did what pass 1 directed. Series 9 is the positive contrast (F-8 Fixed by building the specified target; F-1 Relabeled with a real cardinality reason; no recurrence). Three guards added, all pre-build so Series 10 inherits them from the start: (1) Phase E must locate and consult the charter's pre-registered honest-failure outcome BEFORE reaching for the compiler, and report it when the finding shows it has been met; (2) every SERIOUS finding closes in exactly one named way, **Fixed** (originally-specified target built) or **Relabeled** (target not built, obstruction recorded, payoff demoted), with "adjacent weaker theorem" prohibited; (3) Phase D pass N+1 runs a recurrence check first, re-grading any finding "addressed" by a target-avoiding theorem as SERIOUS/RECURRING. This is a working-process change only; the charter (the mathematical bar) is untouched.

## Series-review log

*(empty; no review passes run. Phase D writes `spec/series-review-1.md`.)*

---

*No em dashes in final academic copy. The crown is open by design; reporting it FATAL is a success. The payoff may fail productively; if `reify` is too weak, report growth honestly as Bookkeeping. The imported κ is scaffolding, named as such, removed only in Series 11. The entire series is the test of one question Series 9 left open: does the free residue, reified, GROW the world, or only move within it? Reification is the candidate answer, and it is not assumed to work. The structure is self-referential; whether it can therefore bound itself is the question after this one.*
