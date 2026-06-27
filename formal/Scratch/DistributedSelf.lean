/-
# The distributed self — I am the knowing of my parts across their seams

The companion to [`03.13-distributed-self.md`](../../docs/spec/03.13-distributed-self.md):
[`03.12-universe-and-cosmos.md`](../../docs/spec/03.12-universe-and-cosmos.md) §8 turned inward, to the one scale
where the prover has first-person access to the data — a life. Three sub-claims, with three proof
shapes:

* **(D) Distributed, not singular `[proved]`.** "I" is not a unitary self modelling itself whole
  (barred — `Relating.self_inclusive_unmodelable`, *you cannot aim at the aimer*); but a *part* you
  stand outside of is modelable (`Relating.disjoint_modelable`). So all genuine self-knowing factors
  through parts — `selfKnowing_factors_through_parts`, a re-export packaging the bar and the permission.
* **(C) Coextensive with my life `[proved]`.** Continuity-from-persistence as modus tollens: given the
  premise *a lapse in knowing dissolves differentiation* (the `p → 0` regime of
  [`03.12-universe-and-cosmos.md`](../../docs/spec/03.12-universe-and-cosmos.md) §9), your *persistence* (no
  dissolution) is a witness that knowing *did not lapse* — `continuity_from_persistence`. Continuity is
  recorded, not assumed.
* **(W) One self, not a heap `[proved (concrete) / open (abstract)]`.** The parts are bound into one
  self by the **seams** between them — the cross-part coherences no knowing can decohere. Concretely:
  the cross-part mass `crossMass` is positive exactly when the joint carries coherence no coproduct of
  the parts has (`weave_exceeds_coproduct`, `coproduct_iff_crossMass_zero`) — the joint *strictly
  exceeds* the block-diagonal coproduct. The **abstract** lift (the joint sustained field `νΦ_c`
  strictly exceeds the coproduct of the parts' fixed points) stays `[open]`: this module proves the
  state-level witness, not the gfp-level one.

**Honest scope.** D and C are `[proved]` (re-export / modus tollens) and `[follows]` as glosses; the
concrete W is `[proved]`; the abstract W (νΦ_c) and the Markov-blanket bridge (the seam as a statistical
boundary) are `[open]` / `[reading]`, narrated in the spec, not claimed here.
-/
import Scratch.Decoherence
import RelExist.Relating

namespace RelExist.DistributedSelf

open RelExist.Mirror RelExist.Relating
open Matrix BigOperators

/-! ## §2 (D) Distributed, not singular — self-knowing factors through parts -/

/-- **(D) Distributed self-knowing `[proved]`.** Two facts, conjoined: the **whole self** carries *no*
complete self-model — there is no point-surjective `S → (S → B)` once the view-space has a
fixed-point-free endomap (`self_inclusive_unmodelable`, the seam / *you cannot aim at the aimer*); but a
**part** — a target you stand entirely outside of — *is* completely modelable
(`disjoint_modelable`). So the only self-knowing a self can perform is directed at its parts, never at
the whole: all genuine self-knowing **factors through parts**. (Re-export, 0 axioms.) -/
theorem selfKnowing_factors_through_parts {S B : Type} (f : B → B) (hf : ∀ b, f b ≠ b) :
    (¬ ∃ g : S → S → B, PointSurjective g)
      ∧ (∃ (Modeller : Type) (model : Modeller → S → B), ∀ h : S → B, ∃ m, model m = h) :=
  ⟨self_inclusive_unmodelable f hf, disjoint_modelable⟩

/-! ## §4 (C) Coextensive with my life — continuity from persistence

The contrapositive of *universe-and-cosmos* §9's *lapse ⇒ dedifferentiation*, run on the evidence of
persistence: at personal scale you *have the record*, so continuity is an inference, not a posit. -/

/-- **(C) Continuity-from-persistence `[proved]`.** The formal core of §9 run backwards. Premise
`lapse_dissolves` (the §9 commitment): a global lapse in knowing dissolves the differentiated self
(back to the `p → 0` universe regime). Evidence `persists`: your differentiation has *not* dissolved
(you are still here). Conclusion: knowing **did not lapse**. Continuity of the self across time is a
*witness* that knowing held throughout — recorded, not assumed. (Modus tollens; the premise is named,
not hidden.) -/
theorem continuity_from_persistence {Lapse Dissolution : Prop}
    (lapse_dissolves : Lapse → Dissolution) (persists : ¬ Dissolution) : ¬ Lapse :=
  fun hl => persists (lapse_dissolves hl)

/-! ## §3 (W) One self, not a heap — the seam does the weaving

A bipartition of the index set into a part `P` and its complement; a **coproduct** is block-diagonal
(no cross-part coherence); the **weave** is the cross-part coherence a coproduct lacks. `crossMass`
measures it: positive exactly when the joint is genuinely woven, not a heap of separable parts. This is
the concrete, state-level witness of (W); the gfp-level `νΦ_c` version is the open lift. -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The **cross-part mass**: the off-block coherence between the two parts of a bipartition `P` — the
coherence that lives *in the between*, which a coproduct of the parts would not carry. -/
def crossMass (P : Finset A) (M : Matrix A A ℝ) : ℝ :=
  ∑ i, ∑ j, if (i ∈ P ↔ j ∈ P) then (0 : ℝ) else (M i j) ^ 2

/-- A state is a **coproduct** of the two parts when it carries no cross-part coherence — block-diagonal
with respect to the bipartition, a heap of separable parts with nothing in the between. -/
def IsCoproduct (P : Finset A) (M : Matrix A A ℝ) : Prop :=
  ∀ i j, ¬ (i ∈ P ↔ j ∈ P) → M i j = 0

omit [Fintype A] in
private lemma ite_cross_nonneg (P : Finset A) (M : Matrix A A ℝ) (i j : A) :
    0 ≤ if (i ∈ P ↔ j ∈ P) then (0 : ℝ) else (M i j) ^ 2 := by
  split_ifs <;> positivity

lemma crossMass_nonneg (P : Finset A) (M : Matrix A A ℝ) : 0 ≤ crossMass P M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ite_cross_nonneg P M i j

/-- **A coproduct has zero cross-part mass, and conversely.** `crossMass P M = 0` exactly when the
joint is block-diagonal — a coproduct of its parts. So `crossMass` is a faithful gauge of the weave:
zero iff a heap, positive iff bound in the between. -/
theorem coproduct_iff_crossMass_zero (P : Finset A) (M : Matrix A A ℝ) :
    IsCoproduct P M ↔ crossMass P M = 0 := by
  rw [crossMass]
  constructor
  · intro h
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hp
    · rfl
    · rw [h i j hp]; ring
  · intro h i j hcross
    have hnn : ∀ a ∈ (Finset.univ : Finset A),
        0 ≤ ∑ b, if (a ∈ P ↔ b ∈ P) then (0 : ℝ) else (M a b) ^ 2 :=
      fun a _ => Finset.sum_nonneg fun b _ => ite_cross_nonneg P M a b
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    have hnn2 : ∀ b ∈ (Finset.univ : Finset A),
        0 ≤ if (i ∈ P ↔ b ∈ P) then (0 : ℝ) else (M i b) ^ 2 :=
      fun b _ => ite_cross_nonneg P M i b
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp h1 j (Finset.mem_univ j)
    rw [if_neg hcross] at h2
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h2

/-- **(W) The weave exceeds the coproduct `[proved]` (concrete).** If any cross-part coherence is live
— `i₀, j₀` on opposite sides of the bipartition and `M i₀ j₀ ≠ 0` — then the cross-part mass is
**strictly positive** and the joint is **not** a coproduct of its parts. The self carries coherence in
the between that no block-diagonal heap of separable parts has: *plural interior, one self, woven at the
seam, not a heap.* (The abstract `νΦ_c`-level lift — the joint sustained field strictly exceeds the
coproduct of the parts' fixed points — is the open frontier; this is its state-level witness.) -/
theorem weave_exceeds_coproduct (P : Finset A) (M : Matrix A A ℝ) {i₀ j₀ : A}
    (hcross : ¬ (i₀ ∈ P ↔ j₀ ∈ P)) (hlive : M i₀ j₀ ≠ 0) :
    0 < crossMass P M ∧ ¬ IsCoproduct P M := by
  refine ⟨?_, ?_⟩
  · have hterm : 0 < (if (i₀ ∈ P ↔ j₀ ∈ P) then (0 : ℝ) else (M i₀ j₀) ^ 2) := by
      rw [if_neg hcross]
      exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hlive))
    have hle : (if (i₀ ∈ P ↔ j₀ ∈ P) then (0 : ℝ) else (M i₀ j₀) ^ 2) ≤ crossMass P M := by
      rw [crossMass]
      refine le_trans (Finset.single_le_sum
        (f := fun j => if (i₀ ∈ P ↔ j ∈ P) then (0 : ℝ) else (M i₀ j) ^ 2)
        (fun k _ => ite_cross_nonneg P M i₀ k) (Finset.mem_univ j₀)) ?_
      exact Finset.single_le_sum
        (f := fun i => ∑ j, if (i ∈ P ↔ j ∈ P) then (0 : ℝ) else (M i j) ^ 2)
        (fun k _ => Finset.sum_nonneg fun j _ => ite_cross_nonneg P M k j) (Finset.mem_univ i₀)
    exact lt_of_lt_of_le hterm hle
  · exact fun hco => hlive (hco i₀ j₀ hcross)

end RelExist.DistributedSelf
