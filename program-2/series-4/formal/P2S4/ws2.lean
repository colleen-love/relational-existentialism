/-
`program-2/series-4/formal/P2S4/ws2.lean`

WS2 - The axes come apart (independence). Program 2 Series 4 (2.4).

The two gradings `rankW` (vertical) and `latW` (lateral) separate DIFFERENT pairs under `IsBisimL`, so neither
is a function of the other. `latW` separates `(w0,w2)` where `rankW` does not; `rankW` separates `(r,w0)` where
`latW` does not. This cross-pattern is the axis-independence, the new content on which the verdict rests (audit c),
NOT the multiplicity of peers (which is the imported Series 07 ground).

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S4.ws1

universe u

namespace P2S4

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-! ## The negative separation: `rankW` separates `(r,w0)` -/

/-- **THE RANK LABEL SEPARATES `r` and `w0`.** No rank-bisimulation relates them (labels 1 vs 0). -/
lemma rank_sep_r_w0 (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0 := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR r w0 hRel
  have hedge : ((⟨rankW r⟩ : ULift.{0} ℕ), w1) ∈ (rankLiftW hinf r).1 := by
    rw [rankLiftW, liftW_val]; exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr (by decide))
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [rankLiftW, liftW_val] at hq
  obtain ⟨wt, hw, rfl⟩ := hq
  have : rankW r = rankW w0 := congrArg ULift.down hfst
  exact absurd this (by decide)

/-! ## The positive bisimulations -/

/-- Rank-0 nodes only attend rank-0 nodes (the peer cycle is closed at rank 0). -/
lemma rank0_closed : ∀ x : W, rankW x = 0 → ∀ z ∈ attendsW x, rankW z = 0 := by decide

/-- **RANK DOES NOT SEPARATE `(w0,w2)`.** The "both rank 0" relation is a rank-bisimulation: every rank-0 node
broadcasts label `0` and steps only to rank-0 nodes, so labels match and successors stay related. -/
lemma rank_bisim_w0_w2 (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2 := by
  refine ⟨fun x y => rankW x = 0 ∧ rankW y = 0, ?_, by decide, by decide⟩
  rintro x y ⟨hx, hy⟩
  constructor
  · intro p hp
    rw [rankLiftW, liftW_val] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨w, hw⟩ := attendsW_nonempty y
    refine ⟨(⟨rankW y⟩, w), ?_, ?_, ?_⟩
    · rw [rankLiftW, liftW_val]; exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hw)
    · show (⟨rankW x⟩ : ULift.{0} ℕ) = ⟨rankW y⟩; rw [hx, hy]
    · exact ⟨rank0_closed x hx z (Finset.mem_coe.mp hz), rank0_closed y hy w hw⟩
  · intro q hq
    rw [rankLiftW, liftW_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    obtain ⟨z, hz⟩ := attendsW_nonempty x
    refine ⟨(⟨rankW x⟩, z), ?_, ?_, ?_⟩
    · rw [rankLiftW, liftW_val]; exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hz)
    · show (⟨rankW x⟩ : ULift.{0} ℕ) = ⟨rankW y⟩; rw [hx, hy]
    · exact ⟨rank0_closed x hx z hz, rank0_closed y hy w (Finset.mem_coe.mp hw)⟩

/-- **LAT DOES NOT SEPARATE `(r,w0)`.** `r` and `w0` both carry `latW`-label `0` and both step to `w1`, so the
relation `id ∪ {(r,w0),(w0,r)}` is a lat-bisimulation. -/
lemma lat_bisim_r_w0 (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0 := by
  refine ⟨fun x y => x = y ∨ (x = r ∧ y = w0) ∨ (x = w0 ∧ y = r), ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have key : ∀ a b : W, latW a = latW b → attendsW a = attendsW b →
      (∀ p ∈ (latLiftW hinf a).1, ∃ q ∈ (latLiftW hinf b).1,
        p.1 = q.1 ∧ (p.2 = q.2 ∨ (p.2 = r ∧ q.2 = w0) ∨ (p.2 = w0 ∧ q.2 = r))) := by
    intro a b hlab hatt p hp
    rw [latLiftW, liftW_val] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    refine ⟨(⟨latW b⟩, z), ?_, ?_, Or.inl rfl⟩
    · rw [latLiftW, liftW_val]; exact Set.mem_image_of_mem _ (by rw [← hatt]; exact hz)
    · show (⟨latW a⟩ : ULift.{0} ℕ) = ⟨latW b⟩; rw [hlab]
  have hrw0 : latW r = latW w0 := by decide
  have hattrw0 : attendsW r = attendsW w0 := by decide
  rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact ⟨fun p hp => ⟨p, hp, rfl, Or.inl rfl⟩, fun q hq => ⟨q, hq, rfl, Or.inl rfl⟩⟩
  · exact ⟨key r w0 hrw0 hattrw0, fun q hq => by
      obtain ⟨p, hp, hfst, hR⟩ := key w0 r hrw0.symm hattrw0.symm q hq
      exact ⟨p, hp, hfst.symm ▸ rfl, hR.elim (fun h => Or.inl h.symm)
        (fun h => h.elim (fun h => Or.inr (Or.inr ⟨h.2, h.1⟩)) (fun h => Or.inr (Or.inl ⟨h.2, h.1⟩)))⟩⟩
  · exact ⟨key w0 r hrw0.symm hattrw0.symm, fun q hq => by
      obtain ⟨p, hp, hfst, hR⟩ := key r w0 hrw0 hattrw0 q hq
      exact ⟨p, hp, hfst.symm ▸ rfl, hR.elim (fun h => Or.inl h.symm)
        (fun h => h.elim (fun h => Or.inr (Or.inr ⟨h.2, h.1⟩)) (fun h => Or.inr (Or.inl ⟨h.2, h.1⟩)))⟩⟩

/-! ## The payoffs -/

/-- **A LATERAL STEP CHANGES `lat`, KEEPS `rank` (WS2).** `w0`,`w2` are lat-separated but rank-identified. -/
theorem ws2_lateral_step_no_rank (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2)
  ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
  ∧ rankW w0 = rankW w2 :=
  ⟨lat_sep_w0_w2 hinf, rank_bisim_w0_w2 hinf, by decide⟩

/-- **A REIFICATION STEP CHANGES `rank`, NO LATERAL DISPLACEMENT (WS2).** `r`,`w0` are rank-separated but
lat-identified. -/
theorem ws2_reify_no_lateral (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0)
  ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0)
  ∧ latW r = latW w0 :=
  ⟨rank_sep_r_w0 hinf, lat_bisim_r_w0 hinf, by decide⟩

/-- **THE AXES ARE INDEPENDENT (WS2).** Neither grading is a function of the other: `latW` separates a pair
`rankW` identifies, and `rankW` separates a pair `latW` identifies. The cross-pattern, not the multiplicity. -/
theorem ws2_axes_independent (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2) )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) ) :=
  ⟨⟨lat_sep_w0_w2 hinf, rank_bisim_w0_w2 hinf⟩, ⟨rank_sep_r_w0 hinf, lat_bisim_r_w0 hinf⟩⟩

end P2S4
