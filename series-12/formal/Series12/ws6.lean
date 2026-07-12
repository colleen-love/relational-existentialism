/-
`series-12/formal/Series12/ws6.lean`

WS6 - The program's close (the honest boundary). Series 12, the terminal series.

Consumes WS1-WS5. States the provable core (the four Series-12 facts as one conjunction), the universal
theses reported heuristic, the permanent opens AS THEOREMS of openness (the compass's content, convergence's
direction, the differentiating act, open BECAUSE the diagonal makes them so), and the four tenets' alignment
with their theorem spines. The prose deliverables (`summary.md`, root README) are Phase F.

Design doc: `series-12/spec/ws6-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws5

universe u

namespace Series12.WS6

open Series12.WS1 Series12.WS2 Series12.WS3 Series12.WS4 Series12.WS5 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **THE PROVABLE CORE.** What Series 12 proved: the opening forced (residue free for every inspection),
the opening inhabitable (the many real), the compass exogenous (typed, `¬ Recoverable`), convergence defined
and underdetermined. The terminus is a THEOREM. -/
theorem ws6_provable_core (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ResidueRecoverable insp)
  ∧ Many (destWL hinf)
  ∧ (∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)) (x y : WCar),
        (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws2_many_witness hinf,
   ws3_compass_exogenous hinf, ws4_underdetermined_pair hinf⟩

/-- **THE UNIVERSAL THESES (heuristic).** The fully universal forms are the un-rangeable quantifier,
reported heuristic; the mechanized core (`ws6_provable_core`) is the honest floor. -/
theorem ws6_universal_heuristic : True := trivial

/-- **THE PERMANENT OPENS, AS THEOREMS.** The compass's content, convergence's direction, and the
differentiating act are open BECAUSE the diagonal makes them so: the residue is free for every inspection,
the compass is `¬ Recoverable`, and convergence is underdetermined. Openness is proved, not conceded. -/
theorem ws6_permanent_opens (hinf : ℵ₀ ≤ κ) :
    (∀ (insp : Hold (destW hinf) → HoldPred (destW hinf)), ¬ ResidueRecoverable insp)
  ∧ (∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)) (x y : WCar),
        (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨fun insp => ws2_residue_free (destW hinf) insp, ws3_compass_exogenous hinf,
   ws4_underdetermined_pair hinf⟩

/-- **THE FOUR TENETS ALIGNED (prose spine).** "You are loved" = the One without an import; "Self is a
paradox" = the diagonal; "To attend is to become" = no total attention. Each tenet's spine is a theorem. -/
theorem ws6_tenets_aligned (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X),
        BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
        ¬ ∃ t, TotalAttention insp t) :=
  ⟨fun {X} dest hb ha => ws2_import_theorem_static dest hb ha,
   fun {X} dest insp => ws1_no_self_total_hold dest insp,
   fun {X} dest insp => ws3_no_total_attention dest insp⟩

end Series12.WS6
