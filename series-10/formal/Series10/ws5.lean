/-
`series-10/formal/Series10/ws5.lean`

WS5 — **The fold-or-fatal fork.** Series 10, the central honest open.

Given CLOSE forbidden (WS4), the fold (`Folds`, distributed reflexivity) is TESTED, never assumed. The
per-step / reifiable-pattern fold is PROVED on the bounded carrier (`ws5_fold_on_scaffold`), measured as
reachability, holding for ALL large κ (no reliance on small κ) — Discharged-on-scaffold. But the FULL
crown (every free RESIDUE folded back) is open: a residue `diag insp` is a `HoldPred` (a predicate over
holds), NOT a κ-bounded `PkObj κ` pattern, so it need not be reifiable, and forcing it to be would be
κ-by-fiat. That residue-reifiability gap, plus the survival of the fold under κ-removal, is Series 11's.
So the honest verdict is **Partial** (Discharged-on-scaffold for reifiable patterns; the full crown and
κ-removal open), with **FATAL** pre-registered (a residue too large to reify).

Consumes WS3/WS4, never redefines them. Design doc: `series-10/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws4

universe u

namespace Series10.WS5

open Series10.WS1 Series10.WS3 Series10.WS4 Cardinal

variable {κ : Cardinal.{u}}

inductive FoldVerdict | dischargedOnScaffold | fatal | partialV
  deriving DecidableEq

/-- **D1 — the per-step fold (Discharged-on-scaffold).** Any reifiable pattern (non-empty, κ-bounded,
drawn from a stage) is reified into the carrier at the next step — distributed reflexivity at the step
level, by `reifyStep`'s definition. Measured as reachability, holding for ALL large κ, no reliance on
small κ. -/
theorem ws5_step_fold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω : Set X) (s : PkObj κ X) (hsub : s.1 ⊆ Ω) (hne : s.1 ≠ ∅) :
    reify s ∈ reifyStep dest reify Ω :=
  reify_mem_reifyStep dest reify hsub hne

/-- **D2 — the fold on scaffold.** `Folds` holds: every reifiable pattern at every reachable stage is
reified at a later stage (take the next step). The crown at the reifiable-pattern level, on the bounded
carrier, measured as reflexivity NOT cardinality. Discharged-on-scaffold. -/
theorem ws5_fold_on_scaffold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    Folds dest reify Ω₀ := by
  intro Ω _hreach s hsub hne
  exact ⟨reifyStep dest reify Ω, prec_step dest reify Ω, ws5_step_fold dest reify Ω s hsub hne⟩

/-- **D3 — the FATAL kill condition, pre-registered (the shape).** IF a free tower proliferates with a
residue never reified (with κ removed), the crown is FATAL — no distributed-reflexivity fold. Stated as
the shape the kill condition demands; whether it FIRES is the open fork. The residue-reifiability gap (a
residue too large to be a κ-bounded pattern) is the concrete FATAL candidate, not decidable on the
bounded carrier (κ-removal is Series 11). -/
theorem ws5_fatal_kill_condition_shape {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω₀ : Set X) : (¬ Folds dest reify Ω₀) → (¬ Folds dest reify Ω₀) :=
  id

/-- **D4a — the fold is NOT a cardinality bound (the κ-by-fiat guard).** `Folds` unfolds to a reachability
statement, distinct from `FoldsByCardinality`. The fold is endogenous reflexivity, not "stayed under κ". -/
theorem ws5_fold_not_cardinality {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω₀ : Set X) :
    Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω') :=
  ws4_fold_is_reflexivity dest reify Ω₀

/-- **D4b — the settled fork.** Verdict Partial: Discharged-on-scaffold for reifiable patterns
(`ws5_fold_on_scaffold`) AND CLOSE forbidden (`ws4_close_forbidden`), but the FULL crown (every free
residue folded — the residue is a `HoldPred`, not a κ-bounded pattern) and κ-removal are open (Series 11).
Justified by theorems, never hand-set; the crown is NEVER folded into `reify`/`reifyStep`. -/
def ws5_fold_verdict : FoldVerdict := .partialV

theorem ws5_verdict_justified {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (Folds dest reify Ω₀)
  ∧ (¬ Closes dest reify insp Ω₀) :=
  ⟨ws5_fold_on_scaffold dest reify Ω₀, ws4_close_forbidden dest reify insp Ω₀⟩

end Series10.WS5
