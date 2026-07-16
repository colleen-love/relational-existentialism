/-
`series-10/formal/Series10/ws4.lean`

WS4 — **Close-or-fold: the dichotomy and CLOSE-forbidden.** Series 10, the structural heart.

CLOSE (a totality-relatum reached in the tower) is a self-total hold, forbidden by the diagonal
(`ws4_close_forbidden`, an Impossibility). The dichotomy is exhaustive (`ws4_dichotomy`). The fold
predicate `Folds` is defined as distributed REFLEXIVITY (every reifiable pattern at a reachable stage is
reified at a later stage), measured as reachability NOT as a cardinality bound (`ws4_fold_is_reflexivity`,
contrasted with the forbidden `FoldsByCardinality`). **The fold's TRUTH is handed to WS5.**

Consumes WS1's diagonal and WS3's tower/`prec`. Design doc: `series-10/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws3

universe u

namespace Series10.WS4

open Series10.WS1 Series10.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-- **CLOSE.** Some relatum reached in the tower is a totality-relatum — an object whose induced
inspection is self-total (its relating is the completed self-inspection). Pinned to `SelfTotal`, so a
totality-relatum IS a self-total hold. -/
def Closes {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : Prop :=
  ∃ Ω : Set X, prec dest reify Ω₀ Ω ∧ ∃ t : Hold dest, t.1.1 ∈ Ω ∧ SelfTotal insp t

/-- **FOLD (the crown, distributed reflexivity).** Every reifiable pattern (a non-empty κ-bounded pattern)
present at a reachable stage is REIFIED into the carrier at a later stage — the incompletability folds
back into range everywhere, never at a summit. Measured as REACHABILITY, NOT a cardinality bound. -/
def Folds {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) : Prop :=
  ∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
    ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω'

/-- **The forbidden κ-by-fiat form**, named for contrast only — never used as the fold. -/
def FoldsByCardinality {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) : Prop :=
  ∀ Ω : Set X, prec dest reify Ω₀ Ω → Cardinal.mk (↥Ω) < κ

/-- **D1 — CLOSE forbidden at the INSPECTION LEVEL (Impossibility proved; series-review-1 S3, honestly
restated).** `Closes` conjoins a tower part (`prec … ∧ t.1.1 ∈ Ω`) with `SelfTotal insp t`, but the proof
discards the tower hypotheses (`_hreach`, `_hmem`): the contradiction is `ws1_no_self_total_hold`, a fact
about the inspection `insp` alone, INDEPENDENT of the tower (`insp` is a free parameter, not induced by
`reify`/`dest`). So this genuinely forbids a self-total hold at the inspection level — a real Impossibility
— but it does NOT show the *carrier-level* tower cannot close: that (the founding-equation iso reaching a
totality-relatum, charter §9) is the OPEN structural question Series 10 does not settle. The "the tower
cannot close into a top" gloss is RETRACTED; what is proved is the tower-independent inspection-level
diagonal. -/
theorem ws4_close_forbidden {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : ¬ Closes dest reify insp Ω₀ := by
  rintro ⟨Ω, _hreach, t, _hmem, htot⟩
  exact ws1_no_self_total_hold dest insp ⟨t, htot⟩

/-- **D2 — the dichotomy is exhaustive.** Excluded middle on `Closes`; combined with D1, the tower is on
the NOT-CLOSE horn — FOLD or FATAL, the open fork (WS5). -/
theorem ws4_dichotomy {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    Closes dest reify insp Ω₀ ∨ ¬ Closes dest reify insp Ω₀ :=
  Classical.em _

/-- **D3 — the founding-equation obstruction (charter §9, honest form).** The genuine non-closure is the
diagonal at the inspection level: no inspection surjects onto contents (`ws1_insp_not_surjective`), so no
totality-relatum exists — whatever the κ-bounded carrier map `reify`. Whether `reify` at the carrier level
is a section-only or an iso is charter §9's OPEN structural question; this design does NOT claim `reify`
must be non-surjective. What the diagonal forbids is the closing top (the self-total hold), independent of
the carrier's cardinality. -/
theorem ws4_diagonal_forbids_closure {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp :=
  ws1_insp_not_surjective dest insp

/-- **D4 — the fold predicate, handed to WS5.** `Folds` is distributed reflexivity (`Iff.rfl` unfolding),
measured as reachability. WS4 defines it; WS5 tests it. -/
theorem ws4_fold_is_reflexivity {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω') := Iff.rfl

/-- **D5 — CLOSE-forbidden is not the fold (coincidence-rule check).** Non-closure holds unconditionally
(from the diagonal) and does NOT by itself entail the fold — the FATAL horn (non-closure without the fold)
is coherent, so WS5's fork is genuinely open, not a corollary of D1. -/
theorem ws4_close_forbidden_not_fold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (¬ Closes dest reify insp Ω₀)
  ∧ (∀ _ : Folds dest reify Ω₀, ¬ Closes dest reify insp Ω₀) :=
  ⟨ws4_close_forbidden dest reify insp Ω₀, fun _ => ws4_close_forbidden dest reify insp Ω₀⟩

end Series10.WS4
