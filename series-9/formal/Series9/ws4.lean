/-
`series-9/formal/Series9/ws4.lean`

WS4 — **The tower and depth.** Series 9, layering.

Depth is the accumulation of blind spots: each re-diagonalization opens a new face the prior stage
could not see (`ws4_new_blind_spot`), the accumulated residue is set-monotone along the chain
(`ws4_depth_is_tower`), and reachability-into-depth is the trace of the re-diagonalization sequence
(`ws4_reaches_is_trace`). Accumulation is stated at `⊆` (NOT strict growth — that is WS5's
monotonicity question, and WS4 is scoped explicitly away from it).

Consumes WS3. Design doc: `series-9/spec/ws4-design.md`; shared objects `spec/README.md` §2.4–§2.5.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws3

universe u

namespace Series9.WS4

open Series9.WS1 Series9.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-- The **accumulated residue** along a re-diagonalization chain: the blind spots gathered so far.
Measured OUTSIDE `ReDiagStep`, so growth is a FACT ABOUT the map, never a clause inside it. -/
def accResidue {X : Type u} {dest : X → PkObj κ X}
    (chain : List (Hold dest → HoldPred dest)) : HoldPred dest :=
  fun h => ∃ insp ∈ chain, diag insp h

/-- **D1 — a step opens a fresh blind spot.** Holding the prior residue at `h₀` flips the diagonal
there: `diag insp'` sees a hold `diag insp` could not. Layering as PROLIFERATION, not narrowing. -/
theorem ws4_new_blind_spot {X : Type u} (dest : X → PkObj κ X)
    (insp insp' : Hold dest → HoldPred dest) (h₀ : Hold dest) (h₀eq : insp' h₀ = diag insp) :
    diag insp' h₀ ↔ ¬ diag insp h₀ :=
  Iff.of_eq (congrArg Not (congrFun h₀eq h₀))

/-- **D2 — depth is the tower.** The accumulated residue is set-monotone (`⊆`) as the chain extends:
the tower of "the truth this stage cannot see," gathered. Stated at `⊆` (accumulation); strictness is
WS5's monotonicity question, NOT claimed here. -/
theorem ws4_depth_is_tower {X : Type u} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    ∀ h, accResidue chain h → accResidue chain' h := by
  intro h hmem
  obtain ⟨insp, hin, hd⟩ := hmem
  exact ⟨insp, hsub hin, hd⟩

/-- **D3 — reach-into-depth is the trace.** `prec` (a re-diagonalization sequence) IS the closure of
`ReDiagStep`: reaching a deeper blind spot is the trace of the chain, derived not axiomatic. -/
theorem ws4_reaches_is_trace {X : Type u} (dest : X → PkObj κ X)
    (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' :=
  ws3_order_endogenous dest m m'

/-- **D4 — depth-growth is inhabited, scoped away from monotonicity.** SOME re-diagonalization chain
strictly accumulates: on `twoLoop`, from `m₀` (self-holds everything, residue empty at `hT`) a single
re-diagonalization reaches `m'` whose residue contains `hT` — a fresh blind spot beyond the accumulated
residue of `[m₀]`. This does NOT claim every step grows (that is WS5). -/
theorem ws4_depth_grows_witness (hinf : ℵ₀ ≤ κ) :
    ∃ (chain : List (Hold (twoLoop hinf) → HoldPred (twoLoop hinf)))
      (m m' : Hold (twoLoop hinf) → HoldPred (twoLoop hinf)),
      prec (twoLoop hinf) m m' ∧ (∃ h, ¬ accResidue chain h ∧ diag m' h) := by
  have hT : Hold (twoLoop hinf) := ⟨(⟨true⟩, ⟨true⟩), by rw [twoLoop_val]; exact rfl⟩
  refine ⟨[fun _ => (fun _ => True)], (fun _ => (fun _ => True)),
    (fun _ => diag (fun _ => (fun _ => True))),
    Relation.ReflTransGen.single ⟨hT, rfl⟩, hT, ?_, ?_⟩
  · rintro ⟨insp, hin, hd⟩
    rw [List.mem_singleton] at hin
    subst hin
    exact hd trivial
  · exact not_not_intro trivial

end Series9.WS4
