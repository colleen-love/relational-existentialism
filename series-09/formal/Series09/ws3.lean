/-
`series-09/formal/Series09/ws3.lean`

WS3 — **Re-diagonalization and forced dynamics.** Series 09, the engine of the tower.

Genuinely new Lean. **Addresses series-review-1 F-8 (SERIOUS) and F-4/F-7 (REAL):** `ReDiagStep` is
strengthened so the next stage genuinely INSPECTS THE WHOLE PRIOR RESIDUE (`∀ h, diag insp h → insp' h
h`), not a single point. Forced dynamics is proved FROM the spine (no reachable stage is complete),
not from `Function.update`. (NL) is relabelled honestly (the residue is a face by type; inhabitation is
conditional, witnessed non-vacuously). **Monotonicity (MG) is NOT attempted here and is never folded
into `ReDiagStep`** — it is WS5's.

Depends on WS1. Design doc: `series-09/spec/ws3-design.md`; shared objects `spec/README.md` §2.4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series09.ws1

universe u

namespace Series09.WS3

open Series09.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-- **Re-diagonalization step** (strengthened, series-review-1 F-8): the next inspection INSPECTS the
prior residue — it self-holds every hold the prior stage left blind (`diag insp`), turning toward the
whole blind-spot face, not a single point. It is free on holds outside the residue (this is (NF)).
Growth is NOT baked in: the step says "inspect the residue," and that inspection *closes* the residue is
a THEOREM (WS4 `ws4_residue_moves`), not a clause; monotonicity stays WS5's open test. -/
def ReDiagStep {X : Type u} (dest : X → PkObj κ X)
    (insp insp' : Hold dest → HoldPred dest) : Prop :=
  ∀ h, diag insp h → insp' h h

/-- **THE TOWER ORDER, derived once.** `m ≺ m'` iff `m'` is reached by a re-diagonalization sequence
from `m`. Endogenous: the reflexive-transitive closure of `ReDiagStep`, from the diagonal operator
alone — no external stage index. WS3 (forced dynamics) and WS4 (tower/depth) both consume `prec`. -/
def prec {X : Type u} (dest : X → PkObj κ X) :
    (Hold dest → HoldPred dest) → (Hold dest → HoldPred dest) → Prop :=
  Relation.ReflTransGen (ReDiagStep dest)

/-- A stage is **complete** if some hold captures its complete content (is self-total). -/
def Complete {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ t, SelfTotal insp t

/-- **D1a — (NL), relabelled honestly (series-review-1 F-7).** The residue is a FACE (a `HoldPred`,
a predicate over holds), never a bare relatum — the leaf trap is avoided by TYPE. Inhabitation is NOT
universal (e.g. `fun _ _ => True` self-holds everything, so its residue is empty), so (NL) is not an
inhabitation theorem for every `insp`; it is face-shape-by-type plus this positive, non-vacuous witness:
the all-unheld inspection has the FULL residue (every hold is a blind spot). -/
theorem ws3_redi_no_leaf {X : Type u} (dest : X → PkObj κ X) :
    ∃ insp : Hold dest → HoldPred dest, ∀ h, diag insp h :=
  ⟨fun _ _ => False, fun _ => not_false⟩

/-- **D1a' — the residue is literally a face-shaped object** (the leaf trap avoided by type). -/
theorem ws3_residue_is_face {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    diag insp = fun h => ¬ insp h h := rfl

/-- **D1b — (NF) not-a-function.** From one inspection, two DISTINCT next inspections both inspect the
prior residue (`⊤` self-holds everything; `(· = ·)` self-holds every diagonal `h h`), differing
off-diagonal. Unconditional (needs only two distinct holds); no `Function.update`, no `classical`. -/
theorem ws3_redi_not_function {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ h₁ : Hold dest) (hne : h₀ ≠ h₁) :
    ∃ insp₁ insp₂, ReDiagStep dest insp insp₁ ∧ ReDiagStep dest insp insp₂ ∧ insp₁ ≠ insp₂ := by
  refine ⟨fun _ _ => True, fun a b => a = b, fun _ _ => trivial, fun _ _ => rfl, ?_⟩
  intro he
  have h2 : True = (h₀ = h₁) := congrFun (congrFun he h₀) h₁
  exact hne (cast h2 trivial)

/-- **D2 — forced dynamics FROM incompleteness (series-review-1 F-4).** No stage reachable by
re-diagonalization is COMPLETE (self-total): the succession never terminates in a complete self-image,
BECAUSE self-totality is impossible. This genuinely uses the spine `ws1_no_self_total_hold` — the
forcing is the content of the theorem, not an intuition asserted between definitions. -/
theorem ws3_dynamics_forced {X : Type u} (dest : X → PkObj κ X)
    (m m' : Hold dest → HoldPred dest) (_hp : prec dest m m') : ¬ Complete m' :=
  ws1_no_self_total_hold dest m'

/-- **D2' — seriality (a successor always exists BY CONSTRUCTION).** The honest companion to D2: from
any stage there is a next re-diagonalization (`⊤` inspects any residue). Labelled as construction, NOT
as the forcing (D2 is the forcing). -/
theorem ws3_serial {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ∃ insp', ReDiagStep dest insp insp' :=
  ⟨fun _ _ => True, fun _ _ => trivial⟩

/-- **D3 — the ONE endogenous order.** `≺` is the closure of re-diagonalization (`Iff.rfl`), defined
from the diagonal operator alone — no imported index. -/
theorem ws3_order_endogenous {X : Type u} (dest : X → PkObj κ X)
    (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' := Iff.rfl

/-- **D4 — the imported-index branch refuted (§4.2 guard).** The order has a genuine 2-cycle between the
maximally-distinct inspections `⊤` and `⊥` (complementary diagonals, so each inspects the other's
residue): `⊤ ↝ ⊥ ↝ ⊤`, `⊤ ≠ ⊥`. So `≺` cycles and no strict monotone stage-index represents it. The
order is endogenous, not a disguised counter. -/
theorem ws3_imported_index_refuted {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    ∃ m₀ m₁ : Hold dest → HoldPred dest,
      ReDiagStep dest m₀ m₁ ∧ ReDiagStep dest m₁ m₀ ∧ m₀ ≠ m₁ := by
  refine ⟨fun _ _ => True, fun _ _ => False, fun h hd => hd trivial, fun _ _ => trivial, ?_⟩
  intro he
  have h2 : True = False := congrFun (congrFun he h₀) h₀
  exact h2 ▸ trivial

end Series09.WS3
