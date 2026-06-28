/-
# Step two — testing the bridge: is the operational seam the conserved band?

The reviews isolated the open unifier: is the **operational seam** (the un-attendable, self-inclusion
block `J`, `SeamForcing.self_cannot_fully_decohere`) the same object as the **conserved band**? Two gaps
were named — *different models* (closed: everything is over ℂ now) and *floor ≠ exact*
(`self_cannot_fully_decohere` gives only `0 < defectSqC`, the band needs entrywise conservation).

This file runs the test **honestly**, under the governing rule: *the seam is characterized from the
attention structure alone, never from `‖μ‖`.* The result is a genuine theorem plus a precise obstruction.

## What is proved — the operational seam is the *operationally* conserved band, exactly and structurally

The dynamics a self can actually perform is directed attention `attend S` (`Attending`), and the
available knowings are exactly those with `S` disjoint from the un-attendable block `J`. An off-diagonal
edge `(i,j)` is **operationally conserved** when *every* available knowing fixes it. The theorem
(`offdiag_conserved_iff_seam`): for `i ≠ j`,

  `(∀ S, Disjoint S J → ∀ M, attend S M i j = M i j)  ↔  (i ∈ J ∧ j ∈ J).`

So the operationally-conserved off-diagonal edges are **exactly** the seam `J`. The seam side `J` is
characterized purely by membership (un-attendability / self-inclusion) — **no `‖μ‖` appears** — so this
is not the tautology the reviews flagged. And the conservation is **exact** (`attend S M i j = M i j`,
equality), upgrading the aggregate floor of `self_cannot_fully_decohere` to entrywise identity. The two
gaps the reviews named are both addressed: one model (ℂ), and exact (not merely a floor).

## The obstruction — why this is still not "energy"

This conservation is conservation under the **0/1 attention gates** `attend S` (`attendMask ∈ {0,1}`).
Such a channel has **no rotating spectrum**: a conserved edge is *fixed* (`mask = 1`, real), never a
rotating `‖μ‖ = 1, μ ≠ 1`. So the operationally-conserved band is the **fixed/known** kind of conserved,
not the **rotating/energy** kind. Energy lives in the *continuous phase channel* `schur μ`
(`RotatingSpectrum`), a different dynamics whose modulus-one set is an independent datum. Identifying the
operational seam with `schur μ`'s rotating band — i.e. that the genuine phase-damping physics damps
*exactly* the attendable edges (`Align`) — links two different channels and is **not** forced by the
attention structure (and forcing it by defining `J` spectrally is exactly the barred tautology).

**Verdict.** `seam = operationally-conserved band` is a **theorem** (structural, exact). `seam = energy
band` stays **`[open]`**, now with a sharp obstruction: the operational (`attend`) conservation is
fixed-not-rotating, so the energy identification needs the cross-channel `Align` posit relating `schur μ`'s
spectrum to attendability — the residual unifier, neither proved here nor definable away.
-/
import Scratch.Attending

namespace RelExist.SeamConserved

open RelExist.Decoherence
open Matrix BigOperators

variable {A : Type} [DecidableEq A]

/-- The all-ones state — a witness carrying a live coherence on every edge. -/
def allOnes (A : Type) : Matrix A A ℂ := fun _ _ => 1

omit [DecidableEq A] in
@[simp] lemma allOnes_apply (i j : A) : allOnes A i j = 1 := rfl

/-- **The operational seam is exactly the operationally-conserved off-diagonal band — structurally.**
For an off-diagonal edge `i ≠ j`: *every available knowing fixes `(i,j)`* (for all states) **iff**
`(i,j)` lies in the seam `J`. The seam side is pinned by membership in `J` alone — the un-attendable,
self-inclusion block — with **no reference to any spectral modulus `‖μ‖`**. Forward: an attendable edge
(`i ∉ J` or `j ∉ J`) is zeroed by the available knowing that attends its loose index, so it is not
conserved. Backward: a `J`-internal edge is untouched by every `S` disjoint from `J`. This upgrades the
aggregate floor `0 < defectSqC` (`self_cannot_fully_decohere`) to **entrywise exact** conservation. -/
theorem offdiag_conserved_iff_seam {J : Finset A} {i j : A} (hij : i ≠ j) :
    (∀ S : Finset A, Disjoint S J → ∀ M : Matrix A A ℂ, attend S M i j = M i j)
      ↔ (i ∈ J ∧ j ∈ J) := by
  constructor
  · intro H
    -- forward: if the edge is conserved by every available knowing, both indices are in J
    refine ⟨?_, ?_⟩
    · by_contra hi
      have hdisj : Disjoint ({i} : Finset A) J := Finset.disjoint_singleton_left.mpr hi
      have hzero : attend ({i} : Finset A) (allOnes A) i j = 0 := by
        rw [attend_apply, if_neg]
        rintro (h | ⟨hi', _⟩)
        · exact hij h
        · exact hi' (Finset.mem_singleton_self i)
      have := H {i} hdisj (allOnes A)
      rw [hzero, allOnes_apply] at this
      exact one_ne_zero this.symm
    · by_contra hj
      have hdisj : Disjoint ({j} : Finset A) J := Finset.disjoint_singleton_left.mpr hj
      have hzero : attend ({j} : Finset A) (allOnes A) i j = 0 := by
        rw [attend_apply, if_neg]
        rintro (h | ⟨_, hj'⟩)
        · exact hij h
        · exact hj' (Finset.mem_singleton_self j)
      have := H {j} hdisj (allOnes A)
      rw [hzero, allOnes_apply] at this
      exact one_ne_zero this.symm
  · rintro ⟨hi, hj⟩ S hSJ M
    -- backward: a J-internal edge is kept by every available knowing
    have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hSJ h hi
    have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hSJ h hj
    rw [attend_apply, if_pos (Or.inr ⟨hiS, hjS⟩)]

/-- **The seam-internal coherence is conserved exactly (not merely floored).** Specializing the
backward direction: for `i, j ∈ J` and any available knowing `S` (disjoint from `J`), the coherence at
`(i,j)` is preserved on the nose — `attend S M i j = M i j`. The aggregate `0 < defectSqC` of
`self_cannot_fully_decohere` is the sum-level shadow of this entrywise equality. -/
theorem seam_edge_exact {J S : Finset A} (hSJ : Disjoint S J) (M : Matrix A A ℂ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) : attend S M i j = M i j := by
  have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hSJ h hi
  have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hSJ h hj
  rw [attend_apply, if_pos (Or.inr ⟨hiS, hjS⟩)]

/-- **The obstruction, in one line: the attention channel has no rotating coherence.** Every available
knowing `attend S` acts on each entry by the mask `{0,1}` — it either keeps a coherence unchanged or
zeroes it; it never multiplies by a phase. So an edge conserved under `attend` is **fixed** (kept with
its exact value), never rotating. Concretely: if `attend S` fixes `(i,j)` then it equals the identity
there (value unchanged) — there is no `μ ≠ 1, ‖μ‖ = 1` action available. This is why the operational
seam is conserved-as-*known*, not conserved-as-*energy*: the rotating/energy band requires the continuous
phase channel `schur μ`, a different dynamics (`RotatingSpectrum`). -/
theorem attend_fixes_are_identity {S : Finset A} (M : Matrix A A ℂ) {i j : A}
    (h : attend S M i j ≠ 0) : attend S M i j = M i j := by
  rw [attend_apply] at h ⊢
  by_cases hc : i = j ∨ (i ∉ S ∧ j ∉ S)
  · rw [if_pos hc]
  · rw [if_neg hc] at h; exact absurd rfl h

end RelExist.SeamConserved
