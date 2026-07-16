/-
`series-08/formal/Series08/ws5.lean`

WS5 — **The conservation fork.** Series 08, the central open law.

Attempts conservation of breadth under narrowing **(CB)**, runs the pre-committed kill condition
(charter §5.4), and reports the verdict. `breadth` is measured OUTSIDE the re-restriction map
(consumed from WS3, never redefined), so conservation is a TESTED FACT — refuted by witness — not a
clause baked into the map (protocol §0.4). The verdict is Partial: strict conservation is Refuted in
general (the kill condition fires on the atomless self-loop), weakly Discharged on a non-increasing
class. This workstream is forbidden from assuming its answer, and does not.

Design doc: `series-08/spec/ws5-design.md`. Consumes WS3.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series08.ws3

universe u

namespace Series08.WS5

open Series08.WS1 Series08.WS3 Cardinal

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

/-! ## The ping-pong carrier — constant breadth, DEPTH-ADVANCING (series-review-1 R1)

The self-loop `twoLoop` forecloses no breadth but its re-restriction returns the same hold (depth
does not advance). The charter's kill condition (§5.4) demands a re-restriction that *opens depth*
without foreclosing breadth. `pingPong` supplies it: two states `⟨true⟩ ↔ ⟨false⟩`, each with a single
successor (constant breadth 1), so a re-restriction `h → h'` moves to a genuinely DIFFERENT hold
(`h ≠ h'`, depth advances) while breadth is preserved — depth opens, nothing foreclosed. -/

noncomputable def pingPong (hinf : ℵ₀ ≤ κ) : ULift.{u} Bool → PkObj κ (ULift.{u} Bool) :=
  fun i => toPk hinf {(⟨!i.down⟩ : ULift.{u} Bool)}

@[simp] lemma pingPong_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (pingPong hinf i).1 = {(⟨!i.down⟩ : ULift.{u} Bool)} := rfl

lemma pingPong_HNE (hinf : ℵ₀ ≤ κ) : ∀ i, SHNE (pingPong hinf) i := by
  intro i v _
  rw [pingPong_val]; exact Set.singleton_ne_empty _

lemma pingPong_breadth (hinf : ℵ₀ ≤ κ) (g : Hold (pingPong hinf)) :
    breadth (pingPong hinf) g = 1 := by
  show Cardinal.mk (↥(pingPong hinf g.1.2).1) = 1
  rw [pingPong_val, Cardinal.mk_singleton]

/-- **D2 — the kill condition fires, DEPTH-ADVANCING (R1).** A re-restriction on a genuinely atomless
field (`pingPong_HNE`) that OPENS depth — `h ≠ h'`, the hold genuinely descends from resolving one
node to resolving the other — while foreclosing no breadth (`breadth h' = breadth h`). This is the
charter §5.4 kill condition in full: depth opens, nothing foreclosed. Conservation is Refuted; the
bound is mere boundedness; the "self-limiting universe" is retracted. -/
theorem ws5_kill_condition (hinf : ℵ₀ ≤ κ) :
    ∃ (h h' : Hold (pingPong hinf)),
      ReReStep (pingPong hinf) h h' ∧ h ≠ h'
      ∧ breadth (pingPong hinf) h' = breadth (pingPong hinf) h
      ∧ (∀ z, SHNE (pingPong hinf) z) := by
  have hmT : (⟨false⟩ : ULift.{u} Bool) ∈ (pingPong hinf ⟨true⟩).1 := by
    rw [pingPong_val]; exact rfl
  have hmF : (⟨true⟩ : ULift.{u} Bool) ∈ (pingPong hinf ⟨false⟩).1 := by
    rw [pingPong_val]; exact rfl
  let h : Hold (pingPong hinf) := ⟨(⟨true⟩, ⟨false⟩), hmT⟩
  let h' : Hold (pingPong hinf) := ⟨(⟨false⟩, ⟨true⟩), hmF⟩
  refine ⟨h, h', ⟨rfl, hmF⟩, ?_, ?_, pingPong_HNE hinf⟩
  · intro he
    have hp : ((⟨true⟩, ⟨false⟩) : ULift.{u} Bool × ULift.{u} Bool) = (⟨false⟩, ⟨true⟩) :=
      congrArg Subtype.val he
    exact absurd ((Prod.mk.injEq _ _ _ _).mp hp).1 (by decide)
  · rw [pingPong_breadth hinf h', pingPong_breadth hinf h]

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
    (∃ (h h' : Hold (pingPong hinf)), ReReStep (pingPong hinf) h h' ∧ h ≠ h'
        ∧ breadth (pingPong hinf) h' = breadth (pingPong hinf) h)
  ∧ ¬ ConservesStrict (twoLoop hinf) := by
  refine ⟨?_, ws5_strict_refuted hinf⟩
  obtain ⟨h, h', hr, hne, heq, _⟩ := ws5_kill_condition hinf
  exact ⟨h, h', hr, hne, heq⟩

end Series08.WS5
