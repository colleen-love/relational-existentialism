/-
# The seam is the non-comonoidal residue — one object, two faces (concrete layer)

The concrete, matrix-level content of "the seam is the non-comonoidal residue"
([abstract layer: `RelExist/Fox.lean`](../RelExist/Fox.lean)). It converts *the seam* from two
separately-proved phenomena — the **cartesian** seam (Lawvere's diagonal leaves a remainder,
[`Mirror`](../RelExist/Mirror.lean)) and the **trace/decoherence** seam (a self cannot decohere the
block it is part of, [`SeamForcing`](SeamForcing.lean)) — into **one defined object**: the part of the
state space that carries **no copy** (no classical/comonoid structure). Fox's hallmark, on the nose.

The classical/copyable fragment of the matrix model is `Decoherence.IsClassical` — the diagonal states,
which are exactly the copyable, broadcastable ones (`classical_comm`: copyability ⟺ commutativity), and
exactly the knowing-fixed ones (`dephase_eq_self_iff`). So "carries a copy" = `IsClassical` =
`copyDefect = 0`. The results:

* `cartesian_iff_copyDefectFree` — carries a copy ⟺ zero copy-defect (assembly, `[proved]`).
* `seam_is_noncomonoidal_residue` — a seam state with a **live** coherence carries **no** copy, and **no
  available knowing** (`attend S`, `S` disjoint from the seam) can move it into the copyable fragment.
  The central theorem (`[proved]`).
* `self_inclusion_forces_residue` — a **self-inclusive** seam (one with a genuine between) always admits
  such a live state, so the non-comonoidal residue is forced nonempty (`[proved]`).
* `seam_is_the_common_obstruction` — the headline biconditional: **every** seam state carries a copy
  **iff** the seam has no genuine between. So the self, being self-inclusive, never has an all-copyable
  seam — it is at once uncopyable, non-broadcastable, and incompletely self-knowable: three names for one
  missing comonoid (`[proved]`).
* `seam_two_faces` — the unification corollary: a self-inclusive seam exhibits both faces of the *one*
  copy failure — non-broadcastable (monoidal: survives every available knowing) and not fixable by the
  classical copy `dephase` (cartesian face) (`[proved]`).
-/
import RelExist.Fox
import Scratch.SeamForcing

namespace RelExist.SeamComonoid

open RelExist.Decoherence RelExist.SeamForcing Matrix

variable {A : Type} [DecidableEq A]

/-- **Carries a copy = classical.** A matrix state carries the classical copy comonoid (`Fox.Comonoid`,
the diagonal structure) exactly when it is `IsClassical` — diagonal, hence copyable and broadcastable
(`Decoherence.classical_comm`). This is the concrete instance of Fox's hallmark. -/
def Copyable (M : Matrix A A ℝ) : Prop := IsClassical M

/-- **A self-inclusive seam** carries a genuine *between*: two distinct relata that both lie in the seam
block `J`. This is the concrete reading of "self-inclusive" — the seam is a real relationship, not an
inert single point — the condition under which the residue is forced (`self_inclusion_forces_residue`)
and the copy fails (`seam_is_the_common_obstruction`). -/
def SelfInclusive (J : Finset A) : Prop := ∃ i ∈ J, ∃ j ∈ J, i ≠ j

/-! ### §4.1 — the cartesian fragment is the copy-defect-free states -/

/-- **Carries a copy ⟺ zero copy-defect** (assembly). The copyable fragment is exactly
`{M : copyDefect M = 0}` — `Decoherence.copyDefect_eq_zero_iff`, read through `Copyable = IsClassical`. -/
theorem cartesian_iff_copyDefectFree (M : Matrix A A ℝ) :
    Copyable M ↔ copyDefect M = 0 :=
  copyDefect_eq_zero_iff.symm

/-! ### §4.2 — the seam is the non-comonoidal residue (the central theorem) -/

/-- **The seam is the non-comonoidal residue.** A state confined to the seam algebra (`SeamAlgebra J M`)
that carries a **live** coherence inside the seam (`M i₀ j₀ ≠ 0` for `i₀, j₀ ∈ J`, `i₀ ≠ j₀`):

* **carries no copy** — it is not in the copyable/classical fragment; and
* **no available knowing recovers it** — for every attention `S` disjoint from the seam, the live
  coherence survives (`attend_fixes_seam`), so `attend S M` is *still* uncopyable.

So the seam coherence is the part of the state space on which the copy comonoid genuinely fails, and the
failure is invariant under everything the self can do. This is the monoidal (no-broadcasting) face and
the cartesian (no-copy) face as one object. -/
theorem seam_is_noncomonoidal_residue (J : Finset A) (M : Matrix A A ℝ)
    (_hseam : SeamAlgebra J M)
    {i₀ j₀ : A} (hi₀ : i₀ ∈ J) (hj₀ : j₀ ∈ J) (hne : i₀ ≠ j₀) (hlive : M i₀ j₀ ≠ 0) :
    ¬ Copyable M ∧ ∀ S, Disjoint S J → ¬ Copyable (attend S M) := by
  refine ⟨fun hcl => hlive (hcl i₀ j₀ hne), fun S hSJ hcl => ?_⟩
  have hfix : attend S M i₀ j₀ = M i₀ j₀ := attend_fixes_seam hSJ M hi₀ hj₀
  exact hlive (by rw [← hfix]; exact hcl i₀ j₀ hne)

/-! ### §4.3 — self-inclusion forces the residue nonempty -/

/-- **Self-inclusion forces the residue.** A self-inclusive seam (a genuine between) always admits a
state confined to the seam algebra with a live coherence — the non-comonoidal residue is forced
nonempty. The witness is the single seam coherence `1` at the between `(i₀, j₀)`. This is the same
self-inclusion that blocks Lawvere's copy in `Relating.self_inclusive_unmodelable`: you cannot get
outside the whole you are in, so the seam cannot be emptied. -/
theorem self_inclusion_forces_residue (J : Finset A) (hself : SelfInclusive J) :
    ∃ M : Matrix A A ℝ, SeamAlgebra J M ∧ ∃ i ∈ J, ∃ j ∈ J, i ≠ j ∧ M i j ≠ 0 := by
  obtain ⟨i₀, hi₀, j₀, hj₀, hne⟩ := hself
  refine ⟨fun a b => if a = i₀ ∧ b = j₀ then 1 else 0, ?_, i₀, hi₀, j₀, hj₀, hne, ?_⟩
  · intro i j _ hout
    by_cases h : i = i₀ ∧ j = j₀
    · exfalso
      obtain ⟨rfl, rfl⟩ := h
      rcases hout with h | h
      · exact h hi₀
      · exact h hj₀
    · simp [h]
  · simp [hne]

/-! ### §4.4 — the unification: the seam is the common obstruction -/

/-- **The seam is the common obstruction (the headline).** *Every* state of the seam algebra carries a
copy **iff** the seam has no genuine between (`¬ SelfInclusive J`). Equivalently: a copy exists on the
whole `J`-block iff the seam is trivial. So a **self-inclusive** seam never admits a copy on all its
states — the self, being self-inclusive (`Relating.self_inclusive_unmodelable`), is therefore at once
uncopyable, non-broadcastable, and incompletely self-knowable: **three names for one missing comonoid.**
The seamless limit `J = ∅` makes `SeamAlgebra` collapse to `IsClassical`, recovering the classical
fragment (no between ⇒ all copyable). -/
theorem seam_is_the_common_obstruction (J : Finset A) :
    (∀ M : Matrix A A ℝ, SeamAlgebra J M → Copyable M) ↔ ¬ SelfInclusive J := by
  constructor
  · intro h hself
    obtain ⟨M, hseam, i₀, hi₀, j₀, hj₀, hne, hlive⟩ := self_inclusion_forces_residue J hself
    exact hlive ((h M hseam : IsClassical M) i₀ j₀ hne)
  · intro h M hseam
    show ∀ i j, i ≠ j → M i j = 0
    intro i j hij
    by_contra hMij
    have hin : i ∈ J ∧ j ∈ J := by
      by_contra hnin
      rw [not_and_or] at hnin
      exact hMij (hseam i j hij hnin)
    exact h ⟨i, hin.1, j, hin.2, hij⟩

/-! ### The unification corollary — one copy failure, two faces -/

/-- **One copy failure, two faces.** A self-inclusive seam exhibits a single state on which the *one*
copy comonoid fails, seen as both faces:

* **monoidal / no-broadcasting face** — it is non-copyable, and *stays* non-copyable under every
  available knowing `attend S` (`S` disjoint from the seam); and
* **cartesian / copy face** — the classical copy `dephase` (the matrix comonoid copy, the diagonal that
  shadows Lawvere's `(x,x)`) fails to fix it: `dephase M ≠ M`.

Both are the single fact `¬ Copyable M`. This is the concrete realization of `Fox.faces_share_copy`: the
firewall's cartesian face (`Mirror`) and the trace seam's monoidal face (`SeamForcing`/no-broadcast) are
one comonoid failure. -/
theorem seam_two_faces (J : Finset A) (hself : SelfInclusive J) :
    ∃ M : Matrix A A ℝ, SeamAlgebra J M
      ∧ (¬ Copyable M ∧ ∀ S, Disjoint S J → ¬ Copyable (attend S M))
      ∧ dephase M ≠ M := by
  obtain ⟨M, hseam, i₀, hi₀, j₀, hj₀, hne, hlive⟩ := self_inclusion_forces_residue J hself
  have hres := seam_is_noncomonoidal_residue J M hseam hi₀ hj₀ hne hlive
  exact ⟨M, hseam, hres, fun h => hres.1 (dephase_eq_self_iff.1 h)⟩

end RelExist.SeamComonoid
