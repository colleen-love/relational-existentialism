/-
`series-8/formal/Series8/ws4.lean`

WS4 — **Narrowing and depth.** Series 8, layering.

Reaching-deeper is holding-more-narrowly (the afforded field is antitone along `≺`), and
reachability is the trace of a narrowing sequence, derived not axiomatic. Discharged on witnesses;
the universal ("all depth is narrowing across any construction") is a pre-registered Partial (WS6).
Consumes WS3's `ReReStep`/`prec`; does not redefine the order. Stays at `⊆` (WS5 owns strict
foreclosure / conservation).

Design doc: `series-8/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series8.ws3

universe u

namespace Series8.WS4

open Series8.WS1 Series8.WS3 Cardinal

variable {κ : Cardinal.{u}} {X : Type u}

/-- **D1 — a step narrows.** Every re-restriction affords a sub-field: reaching deeper is holding
more narrowly. Stated at `⊆` (honest); strictness is WS5's conservation question. -/
theorem ws4_step_narrows (dest : X → PkObj κ X) (h h' : Hold dest)
    (r : ReReStep dest h h') : afford dest h' ⊆ afford dest h := by
  intro w hw
  have hw' : SReaches dest h'.1.2 w := hw
  have hedge : h'.1.2 ∈ (dest h.1.2).1 := by rw [← r.1]; exact r.2
  exact Relation.ReflTransGen.head hedge hw'

/-- **D2 — depth is narrowing along the whole chain.** `afford` is antitone along `≺`. -/
theorem ws4_depth_is_narrowing (dest : X → PkObj κ X) (h h' : Hold dest)
    (hp : prec dest h h') : afford dest h' ⊆ afford dest h := by
  induction hp with
  | refl => exact subset_rfl
  | @tail b c _ hstep ih => exact (ws4_step_narrows dest b c hstep).trans ih

/-- **D3 — reachability is the trace of a narrowing sequence.** Reaching is DERIVED from holding
(cited from WS3). -/
theorem ws4_reaches_is_trace (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    SReaches dest h.1.1 h'.1.1 := ws3_prec_is_reach dest h h' hp

/-! ## The foreclosure witness (D4) — strict narrowing is inhabited, scoped away from conservation -/

/-- A two-level branching step: `⟨true⟩` relates to both states; `⟨false⟩` is a sink. -/
noncomputable def treeStep (hinf : ℵ₀ ≤ κ) : Bool → PkObj κ (ULift.{u} Bool)
  | true  => toPk hinf {(⟨true⟩ : ULift.{u} Bool), (⟨false⟩ : ULift.{u} Bool)}
  | false => toPk hinf {(⟨false⟩ : ULift.{u} Bool)}

noncomputable def treeDest (hinf : ℵ₀ ≤ κ) : ULift.{u} Bool → PkObj κ (ULift.{u} Bool) :=
  fun i => treeStep hinf i.down

@[simp] lemma treeDest_true (hinf : ℵ₀ ≤ κ) :
    (treeDest hinf ⟨true⟩).1 = {(⟨true⟩ : ULift.{u} Bool), ⟨false⟩} := rfl
@[simp] lemma treeDest_false (hinf : ℵ₀ ≤ κ) :
    (treeDest hinf ⟨false⟩).1 = {(⟨false⟩ : ULift.{u} Bool)} := rfl

lemma treeDest_false_reaches (hinf : ℵ₀ ≤ κ) (j : ULift.{u} Bool) :
    SReaches (treeDest hinf) ⟨false⟩ j → j = ⟨false⟩ := by
  intro h
  induction h with
  | refl => rfl
  | @tail b c _ hstep ih =>
      rw [ih, treeDest_false, Set.mem_singleton_iff] at hstep
      exact hstep

/-- **D4 — foreclosure is inhabited, scoped away from conservation.** SOME re-restriction strictly
narrows: the empirical signature is real. This does NOT claim every step forecloses (that is WS5). -/
theorem ws4_depth_forecloses_witness (hinf : ℵ₀ ≤ κ) :
    ∃ (dest : ULift.{u} Bool → PkObj κ (ULift.{u} Bool)) (h h' : Hold dest),
      ReReStep dest h h' ∧ afford dest h' ⊂ afford dest h := by
  have hmemT : (⟨true⟩ : ULift.{u} Bool) ∈ (treeDest hinf ⟨true⟩).1 := by
    rw [treeDest_true]; exact Set.mem_insert _ _
  have hmemF : (⟨false⟩ : ULift.{u} Bool) ∈ (treeDest hinf ⟨true⟩).1 := by
    rw [treeDest_true]; exact Set.mem_insert_of_mem _ rfl
  let h : Hold (treeDest hinf) := ⟨(⟨true⟩, ⟨true⟩), hmemT⟩
  let h' : Hold (treeDest hinf) := ⟨(⟨true⟩, ⟨false⟩), hmemF⟩
  have hstep : ReReStep (treeDest hinf) h h' := ⟨rfl, hmemF⟩
  refine ⟨treeDest hinf, h, h', hstep, ?_⟩
  have hsub : afford (treeDest hinf) h' ⊆ afford (treeDest hinf) h :=
    ws4_step_narrows (treeDest hinf) h h' hstep
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨⟨true⟩, Relation.ReflTransGen.refl, ?_⟩
  intro hcontra
  have hreach : SReaches (treeDest hinf) ⟨false⟩ ⟨true⟩ := hcontra
  exact absurd (treeDest_false_reaches hinf ⟨true⟩ hreach) (by decide)

end Series8.WS4
