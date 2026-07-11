/-
`series-9/formal/Series9/ws3.lean`

WS3 — **Re-diagonalization and forced dynamics.** Series 9, the engine of the tower.

Genuinely new Lean: `ReDiagStep`, `prec` (the ONE endogenous tower order), the two cheap obligations
(NL) no leaf and (NF) not-a-function, the forcing of dynamics from the impossibility of self-totality,
and the imported-index refutation (a 2-cycle, so no strict monotone stage-index fits).
**Monotonicity (MG) is NOT attempted here and is never folded into `ReDiagStep`** — it is WS5's.

Depends on WS1. Design doc: `series-9/spec/ws3-design.md`; shared objects `spec/README.md` §2.4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws1

universe u

namespace Series9.WS3

open Series9.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-- **Re-diagonalization step**: `insp ↝ insp'` — the next inspection HOLDS the prior residue at some
hold (incorporates the blind spot as new content) while, by WS1, carrying a fresh residue of its own.
NF: `insp'` is NOT determined by `insp` — many inspections hold a given residue. Growth is NOT baked in:
the step says nothing about retaining prior blind spots (that is WS5's open monotonicity test). -/
def ReDiagStep {X : Type u} (dest : X → PkObj κ X)
    (insp insp' : Hold dest → HoldPred dest) : Prop :=
  ∃ h₀, insp' h₀ = diag insp

/-- **THE TOWER ORDER, derived once.** `m ≺ m'` iff `m'` is reached by a re-diagonalization sequence
from `m`. Endogenous: the reflexive-transitive closure of `ReDiagStep`, from the diagonal operator
alone — no external stage index. WS3 (forced dynamics) and WS4 (tower/depth) both consume `prec`. -/
def prec {X : Type u} (dest : X → PkObj κ X) :
    (Hold dest → HoldPred dest) → (Hold dest → HoldPred dest) → Prop :=
  Relation.ReflTransGen (ReDiagStep dest)

/-- **D1a — (NL) no leaf.** The residue is a full face: on a hold-reflexive carrier some hold is not
self-held, so `diag insp` is inhabited — there is a genuine face to hold next, never a bare point. -/
theorem ws3_redi_no_leaf {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hne : ∃ h, ¬ insp h h) : ∃ h, diag insp h := by
  obtain ⟨h, hh⟩ := hne
  exact ⟨h, hh⟩

/-- **D1b — (NF) not-a-function.** From one inspection, two DISTINCT next inspections both realise the
residue (each at a different hold): the re-diagonalization is a free facing, not a function of the prior
inspection. Distinctness uses the spine: no hold's content equals the residue (`ws1_no_self_total_hold`),
so `update insp h₀ (diag insp)` and `update insp h₁ (diag insp)` differ at `h₀`. -/
theorem ws3_redi_not_function {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ h₁ : Hold dest) (hne : h₀ ≠ h₁) :
    ∃ insp₁ insp₂, ReDiagStep dest insp insp₁ ∧ ReDiagStep dest insp insp₂ ∧ insp₁ ≠ insp₂ := by
  classical
  refine ⟨Function.update insp h₀ (diag insp), Function.update insp h₁ (diag insp),
    ⟨h₀, ?_⟩, ⟨h₁, ?_⟩, ?_⟩
  · simp
  · simp
  · intro he
    have h0 := congrFun he h₀
    simp only [Function.update_self, Function.update_of_ne hne] at h0
    -- h0 : diag insp = insp h₀ ; but no hold's content is the residue (the spine)
    exact ws1_no_self_total_hold dest insp ⟨h₀, fun h' => Iff.of_eq (congrFun h0.symm h')⟩

/-- **D2 — forced dynamics.** No inspection is terminal: from any inspection there is a further
re-diagonalization (`Function.update` realises the residue), so `ReDiagStep` is serial — the self must
be unfolded over succession. Dynamics is forced by the incompletability of self-reference. -/
theorem ws3_dynamics_forced {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) : ∃ insp', ReDiagStep dest insp insp' := by
  classical
  exact ⟨Function.update insp h₀ (diag insp), h₀, by simp⟩

/-- **D3 — the ONE endogenous order.** `≺` is the closure of re-diagonalization (`Iff.rfl`), defined
from the diagonal operator alone — no imported index. -/
theorem ws3_order_endogenous {X : Type u} (dest : X → PkObj κ X)
    (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' := Iff.rfl

/-- **D4 — the imported-index branch refuted (§4.2 guard).** On the periodic carrier `twoLoop` the order
CYCLES: a genuine 2-cycle `m₀ ↝ m₁ ↝ m₀` between distinct inspections (each holds the other's residue),
so `prec m₀ m₀` is a cycle and no strict monotone stage-index represents `≺` (a strict index forbids
`stage m₀ < stage m₁ < stage m₀`). A 1-cycle is impossible (`ws1_no_self_total_hold`), so the witness is
a genuine 2-cycle. The order is endogenous, not a disguised counter. -/
theorem ws3_imported_index_refuted (hinf : ℵ₀ ≤ κ) :
    ∃ m₀ m₁ : Hold (twoLoop hinf) → HoldPred (twoLoop hinf),
      ReDiagStep (twoLoop hinf) m₀ m₁ ∧ ReDiagStep (twoLoop hinf) m₁ m₀ ∧ m₀ ≠ m₁ := by
  have hT : Hold (twoLoop hinf) := ⟨(⟨true⟩, ⟨true⟩), by rw [twoLoop_val]; exact rfl⟩
  refine ⟨fun _ => (fun _ => True), fun _ => (fun _ => ¬ True), ⟨hT, ?_⟩, ⟨hT, ?_⟩, ?_⟩
  · funext _; simp [diag]
  · funext _; simp [diag]
  · intro he
    have hcontra := congrFun (congrFun he hT) hT
    simp at hcontra

end Series9.WS3
