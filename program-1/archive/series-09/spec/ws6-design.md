# WS6 — The heuristic ceiling

**Design doc. Series 09, the honest boundary. Owns: the universal forms of Consequence 3 (layering-as-accumulated-blind-spots, WS4) and the monotonicity law (WS5), and — if the spine is Discharged-only-on-a-witness — the universal carrier claim (WS1 §5.3), where they exceed what is rangeable, reported as defended theses floored by the mechanized core — the Series 04/05/07/08 pattern.**

*Series 09 is standalone; names transcribed into `series-09/formal/Series09/ws6.lean`, re-namespaced `Series09.WS6` (see `spec/README.md` §6). WS6 **consumes WS1, WS4, and WS5** (protocol §4): it re-exports their mechanized cores as the *floor* of theses whose universal quantifiers are not rangeable, and it names precisely what is proved versus what is defended. It introduces no new object; it draws the line.*

## The object at stake

Charter §5.3, §6 (WS6), §9. Three of Series 09's claims have a universal form that quantifies over *every construction* — un-formalizable in the same way Series 07's trichotomy-exhaustiveness and Series 04/05/08's universals were:

- **Layering-as-accumulated-blind-spots, universal (WS4 C5):** "*all* depth, across *any* construction and *any* notion of deeper, is accumulated diagonal residue." WS4 discharges the per-map form (`ws4_new_blind_spot`, `ws4_depth_is_tower`) and the growth witness; the all-constructions universal is the ceiling.
- **Monotonicity, universal (WS5):** the strong "ever-deepening self" claim is already *Refuted* in general (WS5 D1/D2, the kill condition fires from the map's own mechanism); what remains for WS6 is to state honestly that the *weak* bound (mere non-triviality: the residue is nonempty at every stage) holds universally as a **defended thesis** — every stage has a residue (WS1's `ws1_no_self_total_hold` gives a diagonal at every inspection, WS3's NL makes it a full face) — while monotonicity (the strong form) is refuted, and to floor the "non-trivial" thesis on the per-stage residue-existence that *is* mechanized.
- **The universal carrier, if the spine is on-a-witness (WS1 §5.3):** if WS1's diagonal is Discharged only relative to a specific hold-reflexive `insp` (the near-surjective gap-inspection constructible only on a witness), then "*every* hold-reflexive carrier admits the diagonal" is the ceiling — a defended thesis floored by the witnessed carrier. This still repairs Series 08 (charter §8): ONE non-coincident diagonal is enough.

WS6's discipline: never relabel a defended thesis as a theorem, and never let the refuted strong form (monotonicity) masquerade as the surviving weak one (non-triviality). It reports: **proved core** (per-map new-blind-spot and accumulation; per-stage residue-existence; the witnessed diagonal), **refuted strong form** (monotonicity, from WS5), **defended universal** (all-constructions layering; universal mere-non-triviality; universal carrier if on-a-witness), obstruction precise.

**Ambient theory.** `spec/README.md` §2.3 (`diag`, `SelfTotal`, `ws1_no_self_total_hold`), §2.4–§2.5 (`prec`, `accResidue`, from WS3/WS4); WS4's `ws4_new_blind_spot` / `ws4_depth_is_tower`, WS5's `ws5_kill_condition` / `ws5_monotonicity_verdict`, WS1's `ws1_no_self_total_hold`.

## Candidates

### C1 — The provable core: per-stage residue-existence and per-map accumulation (the floor)

```lean
theorem ws6_stage_has_residue {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t                                    -- every stage's self-total attempt fails
theorem ws6_provable_core {X} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    (∀ h, accResidue chain h → accResidue chain' h) ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t)
```
Everything the mechanization *does* establish about the residue-bound: every inspection's self-total attempt fails (so every stage has a residue — the diagonal), and accumulation is monotone (`⊆`) along the chain (WS4). This is the floor the theses stand on.

- **Success condition:** the terms typecheck — residue-existence is `ws1_no_self_total_hold`, accumulation is `ws4_depth_is_tower`.
- **Failure mode:** none — both are consumed facts.

**Paper triage.** Decidable and immediate: residue-existence is the spine; accumulation is WS4. **Winner (the floor).**

### C2 — The defended universals, stated as theses (not theorems)

```lean
-- ws6_universal_layering (thesis): across ANY construction, deeper ⇒ accumulated diagonal residue. Floored by ws4_new_blind_spot.
-- ws6_universal_nontrivial (thesis): across ANY construction, every stage's residue is nonempty. Floored by ws6_stage_has_residue.
-- ws6_universal_carrier (thesis, IF spine on-a-witness): every hold-reflexive carrier admits the diagonal. Floored by the witnessed WS1 diagonal.
def ws6_universal_theses : Prop := True   -- documentation datum; the Lean content is the floor (C1)
```
The un-rangeable universals, marked as defended theses: WS6 does not claim them as Lean theorems; it names the floor (C1) that supports them and the obstruction (quantifying over all constructions) that keeps them off the machine.

- **Failure mode:** *thesis relabeled as theorem.* The guard: these are `Prop`-level documentation, and the *only* Lean payoff is C1; the design forbids stating them with a real all-constructions quantifier and calling it proved. **Winner (as honestly-flagged theses).**

### C3 — The retraction ledger: monotonicity refuted, non-triviality survives (the sharp line)

```lean
theorem ws6_monotonicity_retracted {X} (dest : X → PkObj κ X) :
    ws5_monotonicity_verdict = MonotonicityVerdict.partial       -- strong form refuted (WS5)
  ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t) -- weak form (non-triviality) survives
```
The one line the whole series' bound-story reduces to: the **strong** monotonicity law is refuted (WS5's verdict is Partial/Refuted-universal), and what survives is **mere non-triviality** (every stage has a residue, the self-total hold never exists). The "ever-deepening self" is retracted; the "incompletable but not necessarily deepening self" is floored on the spine.

- **Failure mode:** *the retraction is cosmetic.* Guard: `ws5_monotonicity_verdict = .partial` is `rfl` on WS5's justified verdict, so the retraction is tied to the actual refutation, not asserted. **Winner (the sharp line WS7 consumes).**

### C4 — The spine-scope ledger: what the diagonal proves and where the universal resists (charter §5.3)

```lean
theorem ws6_spine_scope {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)                                   -- proved for THIS carrier/inspection
  ∧ True  /- the universal "every hold-reflexive carrier diagonalizes" is the defended thesis -/
```
The honest scope of the repair: the diagonal is proved for the ambient `(dest, insp)`; whether *every* hold-reflexive carrier admits it (especially the near-surjective gap-inspection of WS1 D5) is the defended universal. Recorded here so WS7's verdict distinguishes "Discharged" from "Discharged-on-a-witness with a defended universal."

- **Failure mode:** *over-claiming universality.* If WS1 D5 delivered only a witness, WS7 must not read `selfReferenceEstablished` as a universal claim. C4 keeps the line visible. **Winner (the spine-scope ledger).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | per-stage residue-existence + per-map accumulation | `ws1_no_self_total_hold`, `ws4_depth_is_tower` | yes | **win (the floor)** |
| C2 | the defended universals as theses | documentation over C1 | yes (as theses, not theorems) | **win (honest theses)** |
| C3 | monotonicity refuted, non-triviality survives | `ws5_monotonicity_verdict`, spine | yes — `rfl` + spine | **win (the sharp line)** |
| C4 | spine proved on carrier; universal defended | `ws1_no_self_total_hold` | yes | **win (spine-scope ledger)** |

## Winning candidates: C1 (floor) + C2 (defended theses) + C3 (retraction ledger) + C4 (spine-scope ledger)

### Definitions and obligations (cite `spec/README.md` §2; consume WS1, WS4, WS5)

```lean
namespace Series09.WS6
-- carrier, HoldPred, diag, SelfTotal, ws1_no_self_total_hold from WS1 (README §6);
-- prec, ReDiagStep from WS3; accResidue, ws4_new_blind_spot, ws4_depth_is_tower from WS4;
-- MonotonicityVerdict, ws5_monotonicity_verdict from WS5.

/-- **D1 — per-stage residue-existence (C1).** Every inspection's self-total attempt fails, so every
    stage has a residue. The floor of the "non-triviality" thesis. -/
theorem ws6_stage_has_residue {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t := ws1_no_self_total_hold dest insp

/-- **D2 — the provable core (C1).** Accumulation is monotone (`⊆`) along the chain and every stage has
    a residue. -/
theorem ws6_provable_core {X} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    (∀ h, accResidue chain h → accResidue chain' h)
  ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t) :=
  ⟨ws4_depth_is_tower dest chain chain' hsub, fun insp => ws6_stage_has_residue dest insp⟩

/-- **D3 — the retraction ledger (C3).** The STRONG monotonicity law is refuted (WS5); the WEAK bound
    (mere non-triviality: every stage has a residue) survives. The "ever-deepening self" is retracted. -/
theorem ws6_monotonicity_retracted {X} (dest : X → PkObj κ X) :
    ws5_monotonicity_verdict = MonotonicityVerdict.partial
  ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t) :=
  ⟨rfl, fun insp => ws6_stage_has_residue dest insp⟩

/-- **D4 — the spine-scope ledger (C4).** The diagonal is proved for the ambient carrier; the universal
    "every hold-reflexive carrier diagonalizes" is the defended thesis (charter §5.3). One non-coincident
    diagonal repairs Series 08 regardless (charter §8). -/
theorem ws6_spine_scope {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t := ws1_no_self_total_hold dest insp

/-- **D5 — the defended universals (C2), NOT theorems.** Documentation of what is defended above the
    floor and why it is off the machine (the all-constructions quantifier). -/
def ws6_universal_theses : Prop := True   -- the Lean payoff is D1–D4; these are the flagged theses.
```

**D1/D2 (floor)** re-export the mechanized core. **D3 (retraction ledger)** is the sharp line: monotonicity's strong form refuted (tied by `rfl` to WS5's verdict), mere non-triviality surviving on the spine. **D4 (spine-scope ledger)** keeps the on-a-witness / universal line visible. **D5** names the defended universals as theses, floored on D1–D4, obstruction precise — never relabeled as proved.

## Outcome classes (per charter §7)

- **Discharged:** D1 (per-stage residue-existence), D2 (provable core), D3 (retraction ledger), D4 (spine-scope ledger).
- **Partial (the honest ceiling, pre-registered):** the universal forms of layering-as-accumulated-blind-spots, universal mere-non-triviality, and (if the spine is on-a-witness) the universal carrier (D5) — defended theses floored by the mechanized core, the all-constructions quantifier the obstruction (charter §5.3, the Series 04/05/07/08 pattern).
- **Refuted (carried from WS5, reported here):** the strong monotonicity law — WS6 records the retraction, it does not re-litigate it.
- **Strip test.** Delete **"layering / ever-deepening"** from D2/D3 and what remains is the bare **spine (`¬ ∃ t, SelfTotal insp t`) + `accResidue` monotone** — a fixed-point-and-accumulation fact. The floor **survives the strip** (it is honest residue-existence plus set-monotonicity); the *defended universals* are explicitly *not* stripped because they are *not* claimed as theorems — WS6's whole function is to keep that line visible. The retraction (D3) is the anti-laundering payoff: it forbids the refuted strong monotonicity from being reported as the surviving weak non-triviality.

## Deliverable

`series-09/formal/Series09/ws6.lean`: transcribed carrier (README §6); `ws6_stage_has_residue` (D1), `ws6_provable_core` (D2), `ws6_monotonicity_retracted` (D3), `ws6_spine_scope` (D4), `ws6_universal_theses` (D5, documentation). **Consumes WS1's `ws1_no_self_total_hold`, WS4's `ws4_depth_is_tower`, WS5's `ws5_monotonicity_verdict`.** Axiom check: `#print axioms ws6_provable_core` reduces through `ws1_no_self_total_hold` and `ws4_depth_is_tower` to the standard three.
