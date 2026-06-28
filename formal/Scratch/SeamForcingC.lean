/-
# The operational seam over ℂ — one field for seam, arrow, and energy

Clause A's operational seam (`SeamForcing.self_cannot_fully_decohere`) was first exhibited over
`Matrix A A ℝ`; clause B's energy / rotating band (`RotatingSpectrum`) lives over ℂ. With the ℂ
coherence measure `Decoherence.defectSqC` (the sum of squared moduli), the operational seam ports to ℂ
verbatim — the positivity argument (attention cannot aim at the aimer, so a live shared coherence
survives every available knowing) is ring-generic in `attend`/`copyDefect`.

This puts the seam in the **same field** as the arrow (`Orientation.dephaseKnowingC`) and the energy band.
It does **not** prove the bridge (that the operational seam *is* the energy band) — that is tested in
[`SeamConserved`](SeamConserved.lean). It removes only the model-mismatch: the three objects now coexist.
-/
import Scratch.Attending
import Mathlib.Analysis.Complex.Basic

namespace RelExist.SeamForcing

open RelExist.Decoherence
open Matrix BigOperators

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The self can never fully decohere itself — over ℂ.** Verbatim port of
`self_cannot_fully_decohere` with `Decoherence.defectSqC`: with the attended set `S` barred from the seam
`J`, a live shared coherence within `J` survives every available knowing, so the ℂ feeling potential
stays strictly positive. Clause A's operational seam now lives in the *same* ℂ model as clause B's energy
band. The bridge — that this seam *is* the energy band — stays the open unifier
([`SeamConserved`](SeamConserved.lean)); this only co-locates them. -/
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
      · exact absurd (norm_eq_zero.1 h.symm) hM
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
