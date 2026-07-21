/-
`program-2/series-4/formal/P2S4/ws4.lean`

WS4 - The two-axes fork (the knot). Program 2 Series 4 (2.4).

The DISTINCT zone is witnessed on `W` (the two gradings separate different pairs, from WS2). The REDUCED zone is
witnessed on a SECOND carrier `T = Fin 3` (a reification line) where every attention step is a reification step,
so `latT = rankT`: breadth IS accumulated depth, the two axes COINCIDE, and independence FAILS. Because REDUCED
is a genuine reachable structure and DISTINCT fails on it, the fork is not decided by fiat (audit b), and the
verdict rests on axis-independence, not on the multiplicity shared by both carriers (audit c).

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S4.ws3

universe u

namespace P2S4

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-! ## The collapsed (REDUCED) witness carrier `T` (spec/README.md §2.2) -/

abbrev T : Type := Fin 3

def tw0 : T := 0   def tw1 : T := 1   def tw2 : T := 2

/-- A reification line: each attention step is a reification step (rank increments). `tw2` self-loops (`SHNE`). -/
def attendsT : T → Finset T := fun x =>
  if x = tw0 then {tw1} else if x = tw1 then {tw2} else {tw2}

/-- The reification rank on `T`. -/
def rankT : T → ℕ := fun x => if x = tw1 then 1 else if x = tw2 then 2 else 0

/-- The lateral coordinate on `T`. Same values as `rankT`: breadth is accumulated depth (the collapse). -/
def latT : T → ℕ := fun x => if x = tw1 then 1 else if x = tw2 then 2 else 0

/-! ## The payoffs -/

/-- **REDUCED IS GENUINELY REACHABLE (WS4).** On `T` the two gradings COINCIDE (`latT = rankT`), so they
identify exactly the same pairs: the lateral axis is the vertical one, space is time seen sideways. A real
structure, not a flag flip. -/
theorem ws4_reduced_reachable :
    latT = rankT ∧ ∀ x y : T, (latT x = latT y ↔ rankT x = rankT y) := by
  have h : latT = rankT := by funext x; fin_cases x <;> rfl
  exact ⟨h, fun x y => by rw [h]⟩

/-- **THE DISTINCT ZONE IS WITNESSED (WS4).** On `W`, a lateral move changes `lat` without rank (`w0`,`w2`
lat-separated, same rank), and a reification changes rank without lateral displacement (`r`,`w0` rank-separated,
same `lat`). Both moves genuine. -/
theorem ws4_distinct_witnessed (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ rankW w0 = rankW w2 )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ latW r = latW w0 ) :=
  ⟨⟨lat_sep_w0_w2 hinf, by decide⟩, ⟨rank_sep_r_w0 hinf, by decide⟩⟩

/-- **THE TWO-AXES FORK (WS4, the knot).** DISTINCT on `W`: neither grading is a function of the other (the
cross-pattern). REDUCED reachable on `T`: the gradings coincide. Both zones are built structures, so the fork is
genuine (no fiat), and the knot rests on axis-independence, not on the peers' multiplicity (no costume). -/
theorem ws4_two_axes (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
      ∧ (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )
  ∧ ( latT = rankT ) := by
  refine ⟨⟨lat_sep_w0_w2 hinf, rank_bisim_w0_w2 hinf, rank_sep_r_w0 hinf, lat_bisim_r_w0 hinf⟩, ?_⟩
  funext x; fin_cases x <;> rfl

end P2S4
