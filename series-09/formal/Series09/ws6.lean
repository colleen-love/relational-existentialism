/-
`series-09/formal/Series09/ws6.lean`

WS6 — **The heuristic ceiling.** Series 09, the honest boundary.

The universal forms of layering (WS4) and monotonicity (WS5), and — if the spine is on-a-witness — the
universal carrier claim, where they exceed what is rangeable, reported as defended theses floored by the
mechanized core. Introduces no new object; it draws the line: proved core (`ws6_provable_core`), refuted
strong monotonicity with non-triviality surviving (`ws6_monotonicity_retracted`), spine scope
(`ws6_spine_scope`), defended universals as theses (`ws6_universal_theses`, not theorems).

Consumes WS1/WS4/WS5. Design doc: `series-09/spec/ws6-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series09.ws5

universe u

namespace Series09.WS6

open Series09.WS1 Series09.WS3 Series09.WS4 Series09.WS5 Cardinal

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

/-- **D4 — the spine-scope ledger (series-review-1 F-2).** The honest scope of the repair: the diagonal
is a PER-`insp` theorem, holding uniformly for EVERY `insp` on every carrier (Cantor's uniform strength;
`ws1_diagonal_not_bisim`). That IS the orthogonality-to-relational-identity that repairs Series 08 — one
non-coincident diagonal suffices (charter §8). What is NOT proved (and is withdrawn as cardinality-
confused, series-review-1 F-1): a "rich / near-surjective" carrier on which the totality is almost-
formable; there is no such witness, and none is needed — the diagonal is constructible for every `insp`.
The universal "every hold-reflexive carrier diagonalizes" holds by this per-`insp` uniformity; the only
genuine thesis (not theorem) is that a carrier's inspections range over the intended semantic contents,
which is interpretation. -/
theorem ws6_spine_scope {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp

/-- **D5 — the defended universals, NOT theorems.** Documentation of what is defended above the floor
and why it is off the machine (the all-constructions quantifier). The Lean payoff is D1–D4. -/
def ws6_universal_theses : Prop := True

end Series09.WS6
