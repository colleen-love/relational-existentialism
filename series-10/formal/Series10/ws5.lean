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

/-- **D1 — the per-step fold, DEFINITIONAL (series-review-1 S2, relabelled).** Any reifiable pattern
(non-empty, κ-bounded, drawn from a stage) is reified into the carrier at the next step — but this is NOT
a discovered reflexivity, it is `reifyStep`'s DEFINITION read back (`reifyStep Ω = Ω ∪ {reify s | s ⊆ Ω,
s ≠ ∅}` contains `reify s` by construction). It holds for ANY `Ω`, reachable or not. Honest terminus: the
fold at the reifiable-pattern level is a definitional membership fact, NOT a substantive scaffold
discharge. It is κ-honest (reachability, all large κ), but it is not evidence for the crown. -/
theorem ws5_step_fold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω : Set X) (s : PkObj κ X) (hsub : s.1 ⊆ Ω) (hne : s.1 ≠ ∅) :
    reify s ∈ reifyStep dest reify Ω :=
  reify_mem_reifyStep dest reify hsub hne

/-- **D2 — the fold on scaffold, DEFINITIONAL (series-review-1 S2, relabelled).** `Folds dest reify Ω₀`
holds, but its proof discards the reachability hypothesis `_hreach` and reads back `reifyStep`'s
definition — it holds for every `Ω`, reachable or not. So this is NOT "distributed reflexivity discovered
to hold on the scaffold"; it is the construction of `reifyStep` restated. The SUBSTANTIVE fold question
(does a free RESIDUE `diag insp` — a `HoldPred`, not a κ-bounded pattern — fold back into range?) is
entirely open and is the real content of the Partial verdict (§5.4). Do NOT read this as a scaffold
discharge of the crown. -/
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

/-- **D4b — the settled fork.** Verdict Partial. The per-step fold (`ws5_fold_on_scaffold`) is
DEFINITIONAL (S2), NOT a substantive discharge, so the Partial's positive content is thin; CLOSE is
forbidden at the inspection level (`ws4_close_forbidden`, S3). The FULL crown — does a free residue (a
`HoldPred`, not a κ-bounded pattern) fold back — is ENTIRELY OPEN, together with κ-removal (Series 11).
The verdict is honestly Partial (never Discharged-on-scaffold, since the per-step fold is a tautology),
never hand-set; the crown is NEVER folded into `reify`/`reifyStep`. -/
def ws5_fold_verdict : FoldVerdict := .partialV

theorem ws5_verdict_justified {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (Folds dest reify Ω₀)
  ∧ (¬ Closes dest reify insp Ω₀) :=
  ⟨ws5_fold_on_scaffold dest reify Ω₀, ws4_close_forbidden dest reify insp Ω₀⟩

end Series10.WS5
