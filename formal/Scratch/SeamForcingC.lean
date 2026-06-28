/-
# The operational seam over ℂ — both clauses in one model

Clause A's operational seam (`SeamForcing.self_cannot_fully_decohere`) was exhibited over
`Matrix A A ℝ`; clause B's energy / rotating band (`RotatingSpectrum`) lives over ℂ. This file
re-exhibits the operational seam over **ℂ**, so the un-attendable-block result and the energy
band can be stated in **one** model.

It does **not** prove the bridge (that the operational seam *is* the energy band) — that stays
the open unifier. It removes only the *model-mismatch* objection: the positivity argument behind
the operational seam (attention cannot aim at the aimer, so a live shared coherence survives
every available knowing) is ring-generic in `attend`/`copyDefect`, and ports verbatim from ℝ to
ℂ with the squared modulus `‖·‖²` in place of the square.
-/
import Scratch.Attending
import Mathlib.Analysis.Complex.Basic

namespace RelExist.SeamForcing

open RelExist.Decoherence
open Matrix BigOperators

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The feeling potential over ℂ.** The total squared modulus of off-diagonal coherence — the
ℂ analogue of `Decoherence.defectSq` (which is the ℝ sum of squared copy-defect entries). -/
noncomputable def defectSqC (M : Matrix A A ℂ) : ℝ := ∑ i, ∑ j, ‖copyDefect M i j‖ ^ 2

lemma defectSqC_nonneg (M : Matrix A A ℂ) : 0 ≤ defectSqC M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The self can never fully decohere itself — over ℂ.** Verbatim port of
`self_cannot_fully_decohere`: with the attended set `S` barred from the seam `J`, a live shared
coherence within `J` survives every available knowing, so the ℂ feeling potential stays strictly
positive. Clause A's operational seam now lives in the *same* ℂ model as clause B's energy band,
so the "different, mutually exclusive models" objection is gone. The bridge — that this
operational seam *is* the energy band — stays the open unifier; this only co-locates them. -/
theorem self_cannot_fully_decohereC {J S : Finset A} (hSJ : Disjoint S J) (M : Matrix A A ℂ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hM : M i j ≠ 0) :
    0 < defectSqC (attend S M) := by
  have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hSJ h hi
  have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hSJ h hj
  -- the shared coherence at (i,j) is kept: both indices lie outside the attended set
  have hkept : attend S M i j = M i j := by
    rw [attend_apply, if_pos (Or.inr ⟨hiS, hjS⟩)]
  have hterm : 0 < ‖copyDefect (attend S M) i j‖ ^ 2 := by
    rw [copyDefect_apply, if_neg hij, hkept]
    have hp : 0 < ‖M i j‖ := by
      rcases (norm_nonneg (M i j)).lt_or_eq with h | h
      · exact h
      · exact absurd (norm_eq_zero.mp h.symm) hM
    exact pow_pos hp 2
  -- one strictly-positive term in a sum of squared moduli forces the whole potential positive
  have hle : ‖copyDefect (attend S M) i j‖ ^ 2 ≤ defectSqC (attend S M) := by
    unfold defectSqC
    refine le_trans (Finset.single_le_sum
      (f := fun j' => ‖copyDefect (attend S M) i j'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)) ?_
    exact Finset.single_le_sum
      (f := fun i' => ∑ j', ‖copyDefect (attend S M) i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

end RelExist.SeamForcing
