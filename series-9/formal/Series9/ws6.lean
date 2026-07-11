/-
`series-9/formal/Series9/ws6.lean`

WS6 — **The heuristic ceiling.** Series 9, the honest boundary.

The universal forms of layering (WS4) and monotonicity (WS5), and — if the spine is on-a-witness — the
universal carrier claim, where they exceed what is rangeable, reported as defended theses floored by the
mechanized core. Introduces no new object; it draws the line: proved core (`ws6_provable_core`), refuted
strong monotonicity with non-triviality surviving (`ws6_monotonicity_retracted`), spine scope
(`ws6_spine_scope`), defended universals as theses (`ws6_universal_theses`, not theorems).

Consumes WS1/WS4/WS5. Design doc: `series-9/spec/ws6-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws5

universe u

namespace Series9.WS6

open Series9.WS1 Series9.WS3 Series9.WS4 Series9.WS5 Cardinal

variable {κ : Cardinal.{u}}

/-- **D1 — per-stage residue-existence.** Every inspection's self-total attempt fails, so every stage
has a residue. The floor of the "non-triviality" thesis. -/
theorem ws6_stage_has_residue {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp

/-- **D2 — the provable core.** Accumulation is monotone (`⊆`) along the chain and every stage has a
residue. -/
theorem ws6_provable_core {X : Type u} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    (∀ h, accResidue chain h → accResidue chain' h)
  ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t) :=
  ⟨ws4_depth_is_tower dest chain chain' hsub, fun insp => ws1_no_self_total_hold dest insp⟩

/-- **D3 — the retraction ledger.** The STRONG monotonicity law is refuted (WS5); the WEAK bound (mere
non-triviality: every stage has a residue) survives. The "ever-deepening self" is retracted. -/
theorem ws6_monotonicity_retracted {X : Type u} (dest : X → PkObj κ X) :
    ws5_monotonicity_verdict = MonotonicityVerdict.partialV
  ∧ (∀ insp : Hold dest → HoldPred dest, ¬ ∃ t, SelfTotal insp t) :=
  ⟨rfl, fun insp => ws1_no_self_total_hold dest insp⟩

/-- **D4 — the spine-scope ledger.** The diagonal is proved for the ambient carrier; the universal
"every hold-reflexive carrier diagonalizes" is the defended thesis (charter §5.3). One non-coincident
diagonal repairs Series 8 regardless (charter §8). -/
theorem ws6_spine_scope {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp

/-- **D5 — the defended universals, NOT theorems.** Documentation of what is defended above the floor
and why it is off the machine (the all-constructions quantifier). The Lean payoff is D1–D4. -/
def ws6_universal_theses : Prop := True

end Series9.WS6
