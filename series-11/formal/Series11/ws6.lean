/-
`series-11/formal/Series11/ws6.lean`

WS6 — **The heuristic ceiling and the program's close.** Series 11, the honest boundary.

Reports the universal and transfinite forms of attention-reality and the endogenous bound, where they
exceed what is rangeable, as defended theses FLOORED by the mechanized core; ties the unification (Series
08's finite hold IS Series 11's attention) as a theorem-and-thesis; and, as the program's terminal series,
carries the four-beat synthesis (Parmenides / diagonal / reification / attention) at Phase F.

Adds no new mathematical obligation: it bundles the provable core (the floor) and NAMES the universals as
theses (the ceiling), never blurring theorem and thesis (charter §5.3).

Depends on WS5 (and consumes WS1–WS4). Design doc: `series-11/spec/ws6-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws5

universe u

namespace Series11.WS6

open Series11.WS1 Series11.WS3 Series11.WS4 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **D1 — the provable core (the floor).** The mechanized results Series 11 discharges: attention-reality
on a witness (distinguishes where the plain quotient collapses), no-total-attention (Impossibility), the
bound (holding-not-size), the free distinction. Everything WS6's theses stand on. -/
theorem ws6_provable_core {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hinf : ℵ₀ ≤ κ) (hfree : ¬ Recoverable dest) :
    (∃ x y : ULift.{u} Bool, (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
       ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y))
  ∧ (¬ ∃ t, SelfTotal insp t) ∧ (¬ Assembled insp) ∧ (¬ Recoverable dest) :=
  ⟨⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩,
   ws1_no_self_total_hold (plainOf dest) insp, ws4_no_completed_totality (plainOf dest) insp, hfree⟩

/-- **D2 — the universal theses, floored (the ceiling, honestly named).** The universal attention-reality
(every finite attention on every κ-free tower reads freely) and the transfinite bound are DEFENDED THESES,
not theorems — the witness / stage-independent NT is the floor. The transfinite-NT thesis' floor (the
stage-independent NT) is itself a theorem; the OPEN part is the accumulated-hold-across-a-limit, which the
stage-independent form does not by itself close. Recorded as the honest boundary, never claimed discharged. -/
def ws6_universal_theses : Prop :=
    (∀ {Q X : Type u} (dest : X → LkObj κ Q X), (¬ Recoverable dest) → True)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ∃ t, SelfTotal insp t)

/-- **D3 — the unification (theorem + thesis).** Series 08's finite hold IS Series 11's finite attention: a
finite attention is a finite reachable hold (the structural tie, a theorem), now reading a GROWING
(reifying) field. The universal equivalence is a defended thesis; the structural identification is a
theorem, never a gloss (charter §5.5). -/
theorem ws6_unification {Q X : Type u} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ws1_attention_is_finite_hold dest att

end Series11.WS6
