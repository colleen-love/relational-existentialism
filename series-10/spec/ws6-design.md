# WS6 — The heuristic ceiling and the Series 11 handoff

**Design doc. Series 10, the honest boundary. Owns: the universal forms of productive blindness (WS1) and the fold (WS5), where they exceed what is rangeable, reported as defended theses floored by the mechanized core (the Series 04/05/07/08/09 pattern); and the explicit Series 11 inheritance — the κ-removal, the finiteness-of-attention unification, and whichever horn (fold/fatal/partial) Series 10 delivered.**

*Series 10 is standalone; the payoffs it ceilings are transcribed / consumed into `series-10/formal/Series10/ws6.lean`, re-namespaced `Series10.WS6` (see `spec/README.md` §6). WS6 introduces no new object; it draws the line between the proved core and the defended theses, and states the pre-declared handoff. It **consumes WS1/WS4/WS5** and cannot report until they have. This is the Series 04/05/07/08/09 discipline: name what is a theorem, name what is a thesis floored by a theorem, and never let the second wear the first's clothes.*

## The object at stake

Charter §5.3 (scope stated honestly), §6 (WS6), §10 (the Series 11 deferral). Two duties:

- **The heuristic ceiling.** Series 10's mechanized core is per-witness / per-step: productive blindness (WS1) is Discharged for the ambient `reify` (and, if the carrier witness is on-a-witness, for that carrier); the fold (WS5) is Discharged-on-scaffold at the step level. The UNIVERSAL forms — "every κ-bounded reifying carrier grows freely," "the whole tower folds at every limit and survives κ-removal" — exceed what is rangeable on the bounded formalism (the un-rangeable quantifier, the same ceiling Series 04/05/07/08/09 hit). WS6 reports them as defended theses floored by the mechanized core, NOT as theorems.
- **The Series 11 handoff.** Series 10 proves the engine on a κ-scaffold BY DESIGN; the endogenous bound (removing κ, testing finiteness of attention) is Series 11's, a pre-declared inheritance (charter §10, not a discovered pushback). WS6 states explicitly what Series 11 inherits: the κ-removal, the finiteness-of-attention unification, and whichever horn (Discharged-on-scaffold / FATAL / Partial) Series 10 delivered for the fold.

**Ambient theory.** `spec/README.md` §2 (all payoffs); WS1's `ws1_free_reification`, WS4's `ws4_close_forbidden`, WS5's `ws5_fold_verdict`. No new object.

## Candidates

### C1 — The provable core: productive blindness + CLOSE-forbidden + per-step fold (the floor)

```lean
theorem ws6_provable_core {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (¬ ∃ hh, insp hh = residue insp)                                   -- productive blindness (WS1)
  ∧ (¬ Closes dest reify insp Ω₀)                                      -- CLOSE forbidden (WS4)
  ∧ (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ →
       reify s ∈ tower dest reify Ω₀ (α + 1)) :=                       -- per-step fold on scaffold (WS5)
  ⟨ws2_residue_free dest insp, ws4_close_forbidden dest reify insp Ω₀,
   ws5_fold_on_scaffold dest reify h Ω₀⟩
```
The mechanized floor: productive blindness (the reified self-relation is free), CLOSE forbidden (no totality-relatum), and the per-step fold (every residue reified at the next stage on scaffolding). These are theorems; everything above them is a defended thesis.

- **Ambient:** `ws2_residue_free`, `ws4_close_forbidden`, `ws5_fold_on_scaffold`.
- **Success condition (Discharged):** the core is a conjunction of built theorems — the floor the theses rest on.
- **Failure mode:** *bookkeeping / κ-by-fiat inherited.* The floor is genuine only if WS2's growth is strict (not bookkeeping) and WS5's fold is reflexivity (not κ-by-fiat). C1 states the floor; WS7 certifies the two disciplines. **Winner (the floor).**

### C2 — The universal-blindness thesis, NOT a theorem (the un-rangeable quantifier)

```lean
def ws6_universal_blindness_thesis : Prop := True   -- documentation; the Lean floor is C1's per-`insp` blindness
theorem ws6_blindness_scope {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    -- the honest scope: productive blindness is per-`insp`, holding uniformly for EVERY `insp` (the
    -- diagonal's uniform strength, `ws1_no_self_total_hold`). That per-`insp` uniformity IS the floor; the
    -- only genuine thesis (not theorem) is that a reifying carrier's inspections range over the intended
    -- semantic contents — interpretation, not machine-checkable.
    ¬ ∃ t, SelfTotal insp t := ws1_no_self_total_hold dest insp
```
Following Series 09's `ws6_spine_scope` (F-2 correction): productive blindness is a per-`insp` theorem, holding uniformly for every `insp` (Cantor's uniform strength). That per-`insp` uniformity is the floor. What is NOT a theorem is the interpretive claim that a carrier's inspections range over the *intended* semantic contents (that the free residue is the-self-relation-I-cannot-hold rather than a bare un-hit predicate) — that is the thesis, defended above the floor.

- **Ambient:** `ws1_no_self_total_hold`.
- **Success condition:** the scope is honestly drawn — the per-`insp` blindness is the theorem, the semantic-intendedness the thesis.
- **Failure mode:** *the thesis wears the theorem's clothes.* If the interpretive claim (the residue IS the self-relation) were reported as a theorem, WS6 would launder interpretation as proof. C2 pins the per-`insp` blindness as the floor and names the interpretive surplus. **Winner (the blindness scope, honestly drawn).**

### C3 — The universal-fold thesis and the κ-removal, NOT theorems (the fold ceiling)

```lean
theorem ws6_fold_scope {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (Ω₀ : Set X) :
    -- the floor: the per-step fold on scaffolding (WS5 D2). The universal fold (across limits, surviving
    -- κ-removal) is NOT proved here — it is the thesis handed to Series 11.
    (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1))
  ∧ (ws5_fold_verdict = FoldVerdict.partialV) :=
  ⟨ws5_fold_on_scaffold dest reify h Ω₀, rfl⟩
```
The fold ceiling: the per-step fold on scaffolding is the theorem (WS5 D2); the universal fold (across limits) and its survival of κ-removal are theses, handed to Series 11. The verdict is Partial (`ws5_fold_verdict = .partialV`), so the fold is honestly Discharged-on-scaffold-at-the-step, open in the universal — never claimed endogenous (charter §5.3, §5.5).

- **Ambient:** `ws5_fold_on_scaffold`, `ws5_fold_verdict`.
- **Success condition:** the fold floor and its Partial verdict are stated; the universal/κ-removal fold is named as thesis, not theorem.
- **Failure mode:** *the universal fold claimed on scaffolding (overclaim / κ-by-fiat).* If the per-step fold were reported as the full endogenous crown, it would overclaim on the scaffolding — exactly the κ-by-fiat sin. C3 states only the per-step floor and the Partial verdict. **Winner (the fold ceiling).**

### C4 — The Series 11 handoff, stated explicitly (the pre-declared inheritance)

```lean
structure Series11Handoff : Prop where
  kappaIsScaffolding : True   -- κ is scaffolding (charter §1); every Series 10 theorem holds for all large κ
  foldVerdict : FoldVerdict   -- whichever horn Series 10 delivered (expected .partialV)
  endogenousBoundDeferred : True   -- removing κ, testing finiteness-of-attention as the endogenous bound: Series 11
theorem ws6_series11_handoff : Series11Handoff :=
  { kappaIsScaffolding := trivial, foldVerdict := ws5_fold_verdict, endogenousBoundDeferred := trivial }
```
The pre-declared handoff (charter §10, protocol §6): Series 11 inherits the κ-removal, the finiteness-of-attention unification (whether finiteness of attention is the endogenous bound the structure imposes on itself), and Series 10's fold verdict. If the fold came back Discharged-on-scaffold, Series 11's central task is the κ-removal (does the fold survive?); if FATAL, Series 11 inherits the tragic horn (can the many be had without an imported bound?); if Partial, both. WS6 states the handoff as a datum carrying the fold verdict.

- **Ambient:** `ws5_fold_verdict`, `FoldVerdict`.
- **Success condition:** the handoff carries the fold verdict and names the three Series 11 inheritances; the endogenous bound is explicitly OUT of Series 10's scope.
- **Failure mode:** *the deferral faked as a result.* If Series 10 claimed the endogenous bound (that the structure bounds itself), it would overclaim on the scaffolding — the very sin the deferral avoids (charter §10). C4 states the deferral explicitly: Series 10 proves the engine, Series 11 removes the wall. **Winner (the pre-declared handoff).**

### C5 — The retraction ledger: what is proved, what is thesis, what is deferred (the honest bottom line)

```lean
theorem ws6_retraction_ledger {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    -- PROVED (theorems): productive blindness, CLOSE forbidden, per-step fold on scaffold.
    (¬ ∃ hh, insp hh = residue insp) ∧ (¬ Closes dest reify insp Ω₀)
    -- THESIS (defended, not theorems): universal blindness, universal fold, endogenous bound.
    -- DEFERRED (Series 11): κ-removal, finiteness-of-attention. (Documented; the Lean payoff is the proved core.)
  := ⟨ws2_residue_free dest insp, ws4_close_forbidden dest reify insp Ω₀⟩
```
The honest bottom line: PROVED (productive blindness, CLOSE-forbidden, per-step fold), THESIS (the universal forms, defended above the floor), DEFERRED (κ-removal, finiteness of attention, Series 11). The ledger is what keeps the second and third from wearing the first's clothes — the Series 04/05/07/08/09 discipline.

- **Ambient:** the proved core (C1), the theses (C2/C3), the deferral (C4).
- **Success condition:** the ledger separates proved / thesis / deferred cleanly.
- **Failure mode:** *the boundary blurred.* If the ledger let a thesis read as proved, WS6 would launder ambition as result. C5 pins the three tiers. **Winner (the honest bottom line).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the provable core (blindness + CLOSE + per-step fold) | WS1/WS4/WS5 payoffs | yes | **win (the floor)** |
| C2 | universal blindness is thesis; per-`insp` is theorem | `ws1_no_self_total_hold` | yes | **win (blindness scope)** |
| C3 | universal fold + κ-removal are thesis; per-step is theorem | `ws5_fold_on_scaffold` | yes | **win (fold ceiling)** |
| C4 | the Series 11 handoff (carries the fold verdict) | `ws5_fold_verdict` | yes | **win (pre-declared handoff)** |
| C5 | the retraction ledger (proved/thesis/deferred) | C1–C4 | yes | **win (honest bottom line)** |

## Winning candidates: C1 (floor) + C2 (blindness scope) + C3 (fold ceiling) + C4 (handoff) + C5 (ledger)

### Definitions and obligations (cite `spec/README.md` §2; consume WS1/WS4/WS5)

```lean
namespace Series10.WS6
-- all WS1/WS4/WS5 payoffs; ws5_fold_verdict, FoldVerdict — transcribed / consumed (README §6).

/-- **D1 — the provable core (C1, the floor).** Productive blindness, CLOSE forbidden, per-step fold on
    scaffold — the theorems everything above rests on. -/
theorem ws6_provable_core {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (¬ ∃ hh, insp hh = residue insp) ∧ (¬ Closes dest reify insp Ω₀)
  ∧ (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1)) :=
  ⟨ws2_residue_free dest insp, ws4_close_forbidden dest reify insp Ω₀, ws5_fold_on_scaffold dest reify h Ω₀⟩

/-- **D2 — the blindness scope (C2).** Productive blindness is per-`insp`, uniform (the floor); the
    semantic-intendedness of the residue is the thesis, defended not proved. -/
theorem ws6_blindness_scope {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t := ws1_no_self_total_hold dest insp

/-- **D3 — the fold ceiling (C3).** The per-step fold on scaffold is the theorem; the universal fold and
    κ-removal are theses (Series 11). The verdict is Partial — never claimed endogenous. -/
theorem ws6_fold_scope {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (Ω₀ : Set X) :
    (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1))
  ∧ (ws5_fold_verdict = FoldVerdict.partialV) :=
  ⟨ws5_fold_on_scaffold dest reify h Ω₀, rfl⟩

/-- **D4 — the Series 11 handoff (C4, the pre-declared inheritance).** κ is scaffolding; Series 11
    inherits the κ-removal, the finiteness-of-attention unification, and Series 10's fold verdict. -/
structure Series11Handoff : Prop where
  foldVerdict : FoldVerdict
theorem ws6_series11_handoff : Series11Handoff := { foldVerdict := ws5_fold_verdict }

/-- **D5 — the defended universals, NOT theorems (the retraction ledger, C5).** Documentation of what is
    defended above the floor (universal blindness, universal fold) and deferred (κ-removal). The Lean
    payoff is D1–D4. -/
def ws6_universal_theses : Prop := True
```

**D1 (the floor)** conjoins the built theorems. **D2 (blindness scope)** pins per-`insp` blindness as theorem, semantic-intendedness as thesis (the Series 09 F-2 discipline). **D3 (fold ceiling)** pins the per-step fold as theorem, the universal/κ-removal fold as thesis, the verdict Partial. **D4 (handoff)** carries the fold verdict into the pre-declared Series 11 inheritance. **D5 (ledger)** is the documentation tier — the universals are theses, floored by D1, deferred where they exceed the machine.

## Outcome classes (per charter §7)

- **Discharged (the provable core):** D1, D2, D3 — productive blindness, CLOSE-forbidden, per-step fold, all built theorems.
- **Partial (the defended theses, the ceiling):** D5 — the universal forms of productive blindness ("every reifying carrier grows freely") and the fold ("the whole tower folds, surviving κ-removal") are defended theses floored by the mechanized core, NOT theorems (charter §5.3). The un-rangeable quantifier, the Series 04/05/07/08/09 ceiling.
- **Discharged-on-scaffold (inherited from WS5):** the fold floor (D3) is on the κ-scaffold; the handoff (D4) carries this to Series 11.
- **The Series 11 inheritance (pre-declared, not a Series 10 result):** D4 — the κ-removal, the finiteness-of-attention unification, and the fold verdict. Stating the deferral is honest scaffolding management (charter §10); claiming the endogenous bound would be the overclaim WS6 exists to avoid.
- **Strip test.** WS6 introduces no payoff of its own to strip; it aggregates the strips of WS1 (productive blindness → the diagonal freeness fact), WS4 (CLOSE-forbidden → the diagonal), and WS5 (the fold → a reification-reachability fact). The honest bottom line WS6 reports: **Series 10's mechanized core is the Series 09 diagonal (`ws1_no_self_total_hold`) plus a section `reify` that turns the free residue into a fresh carrier element; its universal forms (every carrier grows, the whole tower folds) and its endogenous bound are defended theses / deferred to Series 11, marked not hidden.** The load-bearing, non-stripped gains: productive blindness routes through the diagonal (WS1), CLOSE-forbidden IS the diagonal (WS4), and the fold is reflexivity not cardinality (WS5) — those three are structural, and WS6 reports them as the floor, the theses as the surplus, the κ-removal as Series 11's.

## Deliverable

`series-10/formal/Series10/ws6.lean`: consumed payoffs (README §6); `ws6_provable_core` (D1), `ws6_blindness_scope` (D2), `ws6_fold_scope` (D3), `Series11Handoff` + `ws6_series11_handoff` (D4), `ws6_universal_theses` (D5). Axiom check: `#print axioms ws6_provable_core` reduces through WS1/WS4/WS5 to the standard three. **Consumes WS1/WS4/WS5; introduces no new object; states the pre-declared Series 11 handoff (κ-removal, finiteness-of-attention, the fold verdict) explicitly. The endogenous bound is OUT of Series 10's scope by design; WS6 names it deferred, never claimed.**
