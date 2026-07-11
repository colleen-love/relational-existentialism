/-
`series-8/formal/Series8/ws5.lean`

WS5 — **The conservation fork.** Series 8, the central open law.

Attempts conservation of breadth under narrowing **(CB)**, runs the pre-committed kill condition
(charter §5.4), and reports the verdict. `breadth` is measured OUTSIDE the re-restriction map
(consumed from WS3, never redefined), so conservation is a TESTED FACT — refuted by witness — not a
clause baked into the map (protocol §0.4). The verdict is Partial: strict conservation is Refuted in
general (the kill condition fires on the atomless self-loop), weakly Discharged on a non-increasing
class. This workstream is forbidden from assuming its answer, and does not.

Design doc: `series-8/spec/ws5-design.md`. Consumes WS3.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series8.ws3

universe u

namespace Series8.WS5

open Series8.WS1 Series8.WS3 Cardinal

variable {κ : Cardinal.{u}} {X : Type u}

/-- **Breadth AT a hold**: the alternatives for the next re-restriction — the successors of the
target. Defined OUTSIDE `ReReStep`, so conservation stays testable (README §2.5). -/
def breadth (dest : X → PkObj κ X) (h : Hold dest) : Cardinal := Cardinal.mk (↥(dest h.1.2).1)

/-- Conservation (weak): breadth does not increase along a re-restriction. A claim to TEST. -/
def Conserves (dest : X → PkObj κ X) : Prop :=
  ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' ≤ breadth dest h

/-- Conservation (strict): each narrowing strictly forecloses breadth (the zero-sum reading). -/
def ConservesStrict (dest : X → PkObj κ X) : Prop :=
  ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' < breadth dest h

inductive ConservationVerdict | discharged | refuted | partialV
  deriving DecidableEq

/-- **D1 — strict conservation is refuted.** The atomless self-loop has breadth 1 at every hold, so
no step strictly forecloses: `ConservesStrict (twoLoop)` is false. -/
theorem ws5_strict_refuted (hinf : ℵ₀ ≤ κ) : ¬ ConservesStrict (twoLoop hinf) := by
  intro hcs
  have hmem : (⟨true⟩ : ULift.{u} Bool) ∈ (twoLoop hinf ⟨true⟩).1 := by
    rw [twoLoop_val]; exact rfl
  let h : Hold (twoLoop hinf) := ⟨(⟨true⟩, ⟨true⟩), hmem⟩
  exact lt_irrefl _ (hcs h h ⟨rfl, hmem⟩)

/-- **D2 — the kill condition fires.** A depth-opening re-restriction on a GENUINELY ATOMLESS field
(`twoLoop_HNE`) that forecloses no breadth. Conservation is Refuted; the bound is mere boundedness;
the "self-limiting universe" is retracted (charter §5.4). -/
theorem ws5_kill_condition (hinf : ℵ₀ ≤ κ) :
    ∃ (h h' : Hold (twoLoop hinf)),
      ReReStep (twoLoop hinf) h h'
      ∧ ¬ (breadth (twoLoop hinf) h' < breadth (twoLoop hinf) h)
      ∧ SHNE (twoLoop hinf) h.1.1 := by
  have hmem : (⟨true⟩ : ULift.{u} Bool) ∈ (twoLoop hinf ⟨true⟩).1 := by
    rw [twoLoop_val]; exact rfl
  let h : Hold (twoLoop hinf) := ⟨(⟨true⟩, ⟨true⟩), hmem⟩
  exact ⟨h, h, ⟨rfl, hmem⟩, lt_irrefl _, twoLoop_HNE hinf _⟩

/-- **D3 — conservation on a non-increasing atomless class (honestly weak).** Where successor sets do
not grow along edges, breadth is weakly conserved. Stated as a hypothesis on `dest`, NOT on the map. -/
theorem ws5_conserves_if_nonincreasing (dest : X → PkObj κ X)
    (hmono : ∀ x y, y ∈ (dest x).1 → Cardinal.mk (↥(dest y).1) ≤ Cardinal.mk (↥(dest x).1)) :
    Conserves dest := by
  intro h h' hstep
  have hy : h'.1.2 ∈ (dest h.1.2).1 := by rw [← hstep.1]; exact h'.2
  exact hmono h.1.2 h'.1.2 hy

/-- **D4 — the settled fork.** The verdict is Partial: Refuted in general (D2), weakly Discharged on
the non-increasing class (D3). Justified by theorems — not hand-set. -/
def ws5_conservation_verdict : ConservationVerdict := .partialV

theorem ws5_verdict_justified (hinf : ℵ₀ ≤ κ) :
    (∃ (h h' : Hold (twoLoop hinf)), ReReStep (twoLoop hinf) h h'
        ∧ ¬ breadth (twoLoop hinf) h' < breadth (twoLoop hinf) h)
  ∧ ¬ ConservesStrict (twoLoop hinf) := by
  refine ⟨?_, ws5_strict_refuted hinf⟩
  obtain ⟨h, h', hr, hnf, _⟩ := ws5_kill_condition hinf
  exact ⟨h, h', hr, hnf⟩

end Series8.WS5
