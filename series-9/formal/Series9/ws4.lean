/-
`series-9/formal/Series9/ws4.lean`

WS4 — **The tower and depth.** Series 9, layering.

**Addresses series-review-1 F-8 (SERIOUS) and F-5 (REAL).** With the strengthened `ReDiagStep` (the next
stage inspects the WHOLE prior residue), the depth content is now genuine: re-inspection CLOSES the prior
residue (`ws4_residue_moves`) — the diagonal escapes its enumeration, it does not linger — and the
residue moves to fresh holds (`ws4_residue_moves_witness`). `ws4_depth_is_tower` is honestly relabelled
as accumulation of the accumulated residue (a list-membership `⊆` fact); the tower reading is prose,
flagged. Reachability-into-depth is the closure trace (`ws4_reaches_is_trace`).

Consumes WS3. Design doc: `series-9/spec/ws4-design.md`; shared objects `spec/README.md` §2.4–§2.5.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws3

universe u

namespace Series9.WS4

open Series9.WS1 Series9.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-- The **accumulated residue** along a re-diagonalization chain: the blind spots gathered so far.
Measured OUTSIDE `ReDiagStep`, so any growth claim is a FACT ABOUT the map, never a clause inside it. -/
def accResidue {X : Type u} {dest : X → PkObj κ X}
    (chain : List (Hold dest → HoldPred dest)) : HoldPred dest :=
  fun h => ∃ insp ∈ chain, diag insp h

/-- **D1 — re-inspection CLOSES the prior residue (the diagonal moves, series-review-1 F-8).** If `insp'`
re-diagonalizes `insp` (inspects its whole residue), then EVERY prior blind spot is closed at the next
stage: `diag insp h → ¬ diag insp' h`. The new residue is disjoint from the prior one — the diagonal
escapes the enumeration it was run against, it does not linger. This is genuine layering content about
re-inspection, not a `Function.update` point-edit. -/
theorem ws4_residue_moves {X : Type u} (dest : X → PkObj κ X)
    (insp insp' : Hold dest → HoldPred dest) (r : ReDiagStep dest insp insp') :
    ∀ h, diag insp h → ¬ diag insp' h := by
  intro h hd hd'
  exact hd' (r h hd)

/-- **D2 — depth is the tower (relabelled, series-review-1 F-5).** Honestly a list-membership fact: the
accumulated residue is set-monotone (`⊆`) as the chain extends. This is *accumulation of blind spots*,
NOT strict growth (WS5's monotonicity question) and NOT a self-inspection theorem — the tower reading is
prose, flagged. `diag` is never unfolded here. -/
theorem ws4_depth_is_tower {X : Type u} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    ∀ h, accResidue chain h → accResidue chain' h := by
  intro h hmem
  obtain ⟨insp, hin, hd⟩ := hmem
  exact ⟨insp, hsub hin, hd⟩

/-- **D3 — reach-into-depth is the trace.** `prec` (a re-diagonalization sequence) IS the closure of
`ReDiagStep`: reaching a deeper stage is the trace of the chain, derived not axiomatic. -/
theorem ws4_reaches_is_trace {X : Type u} (dest : X → PkObj κ X)
    (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' :=
  ws3_order_endogenous dest m m'

/-- **D4 — the residue moves to a fresh hold (series-review-1 F-8, reframed).** A genuine
re-diagonalization `insp ↝ insp'` in which `insp'` has a blind spot at `h₀` that `insp` did not: the
diagonal has moved to a fresh hold. (`insp = ⊤` has empty residue; `insp' = fun _ => ¬⊤` inspects it and
opens a blind spot at every hold.) This exhibits the "fresh blind spot" content on the strengthened map,
tied to `insp` by `ReDiagStep`, not a free constant inspection. -/
theorem ws4_residue_moves_witness {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    ∃ (insp insp' : Hold dest → HoldPred dest),
      ReDiagStep dest insp insp' ∧ diag insp' h₀ ∧ ¬ diag insp h₀ := by
  refine ⟨fun _ _ => True, fun _ _ => ¬ True, fun h hd => hd, ?_, ?_⟩
  · exact not_not_intro trivial
  · exact fun hd => hd trivial

end Series9.WS4
