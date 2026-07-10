/-
`series-7/formal/Series7/ws6.lean`

WS6 — **The heuristic ceiling.** Series 7, the honest boundary.

Owns the line between the provable core (the general lemma over every plain coalgebra, the
transcribed process instance, and the trichotomy) and the fully universal "any construction
faithful to relating collapses" — attempted, and reported HEURISTIC because "construction"
admits no honest formalizable quantifier, exactly as Series 4/5 reported their forced answers.

Design doc: `series-7/spec/ws6-design.md`, C1 (core mechanized) + C4 (universal heuristic).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws5

universe u

namespace Series7.WS6

open Series7.WS1 Series7.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-- **D1 — the provable core.** The static collapse (lemma-driven, WS2), the transcribed dynamic
collapse (Series 6), and the single-coalgebra dichotomy (WS3, `ws3_dichotomy`), conjoined — an
explicit disjunction over the shapes Series 7 mechanizes, with a genuine ∀ inside each conjunct
and NO ∀ over "constructions". The honest floor. (The third, intensional-history kind lives on the
process and collapses under atomlessness — `WS3.ws3_leafy_thread_collapses` — it is not a kind of
distinction on a single coalgebra.) -/
theorem ws6_provable_core (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X),
        BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X)
  ∧ (∀ (t : Proc κ), Productive t → t = omegaProc hinf)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (x y : X), x ≠ y →
        LeafDiff dest x y ∨ ImportDiff dest x y) :=
  ⟨fun dest hb ha => Series7.WS2.ws2_import_theorem_static dest hb ha,
   fun t ht => ws1_productive_unique hinf t ht,
   fun dest x y h => ws3_dichotomy dest x y h⟩

/-! ## The universal — attempted, reported heuristic -/

/-- The status of a program claim (transcribed forced-answer packaging). -/
inductive ClaimStatus
  | mechanized
  | heuristic
  deriving DecidableEq

/-- A program claim: a machine-checked core plus a defended (possibly heuristic) thesis. -/
structure ProgramClaim where
  thesis : String
  status : ClaimStatus

/-- **D2 — the universal, reported heuristic.** A `Construction` general enough to cover
coalgebras AND the process is either contentless (= a coalgebra, missing the process), a
disjunction of the known shapes (= the core), or so general the collapse is false (a labelled
coalgebra refutes it). This trilemma has no fourth horn, so the universal admits no honest
formalizable quantifier — it is a defended thesis floored by `ws6_provable_core`, in the exact
register of Series 4/5's forced answers. -/
def ws6_universal : ProgramClaim :=
  { thesis := "any construction faithful to relating is an import or collapses"
  , status := ClaimStatus.heuristic }

/-- The universal is honestly tagged heuristic, not asserted as a mechanized quantifier. -/
theorem ws6_universal_is_heuristic : ws6_universal.status = ClaimStatus.heuristic := rfl

end Series7.WS6
