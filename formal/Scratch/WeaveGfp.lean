/-
# The weave at the greatest fixed point — the unity of the self where νΦ lives

Closes the keystone left open by [`03.13-distributed-self.md`](../../docs/spec/03.13-distributed-self.md)
§(W) and [`03.14-cosmos-knowing-itself.md`](../../docs/spec/03.14-cosmos-knowing-itself.md) §(K): that
the joint self **strictly exceeds** the coproduct of its parts' selves — *one self, woven at the seam,
not a heap*.

The correction that makes it provable: the state-level witness `DistributedSelf.weave_exceeds_coproduct`
lives in the **matrix model**, while `νΦ` lives in the **lattice/attention model**
([`Attention.lean`](Attention.lean)). Rather than bridge the two models, prove the weave **natively in
the lattice**, where the self actually is — over `couplingOp`/`sustainedField` and the proved
`relating_absorbs`. The matrix model then drops to a satisfiability *witness* (a coupling whose
`seamFlow` keeps a live cross coherence realizes the non-redundant-seam hypothesis), and the
matrix↔lattice bridge becomes optional, not load-bearing.

The route, all over the proved `Attention.lean` API:
* **M1** `gfp_mono_in_coupling` — fewer edges ⇒ smaller self, so each part-self and their join lie below
  the joint self (`couplingOp_le_of_sub` + `sustainedField_greatest`);
* **M2** `sustainedField_foreign_bot` — at a vertex inside `P`, the foreign (`Pᶜ`) part-self is `⊥`
  (the foreign operator's sup ranges over an empty condition);
* **M3** `weave_gfp_exceeds_coproduct` — a live, non-redundant cross seam forces strictness at that
  vertex, via `relating_absorbs` (the seam lifts the cross relatum's standing into the joint self),
  which the coproduct (pinned to the part value by M2) cannot match.
-/
import Scratch.Attention

namespace RelExist.WeaveGfp

open RelExist.Attention

variable {V : Type*} {α : Type*} [CompleteLattice α]

/-! ## Bipartition: the part coupling, the foreign coupling, the coproduct -/

/-- The **part's own coupling** — only relations with both endpoints inside the part `P`. -/
def cP (c : V → V → Prop) (P : V → Prop) (i j : V) : Prop := c i j ∧ P i ∧ P j

/-- The **foreign coupling** — only relations with both endpoints outside `P`. -/
def cPc (c : V → V → Prop) (P : V → Prop) (i j : V) : Prop := c i j ∧ ¬ P i ∧ ¬ P j

/-- The **coproduct** (the heap): the two parts each sustaining themselves in isolation, joined with
nothing in the between. -/
def coproduct (c : V → V → Prop) (P : V → Prop) : Field V α :=
  sustainedField (cP c P) ⊔ sustainedField (cPc c P)

/-! ## M1 — fewer edges, smaller self -/

/-- **The attention operator is monotone in the coupling.** Dropping relations (a sub-coupling) can
only lower sustained standing, pointwise. -/
theorem couplingOp_le_of_sub {c₁ c₂ : V → V → Prop} (h : ∀ i j, c₁ i j → c₂ i j)
    (att : Field V α) : couplingOp c₁ att ≤ couplingOp c₂ att := by
  intro i
  simp only [couplingOp_apply]
  exact iSup_mono fun j => iSup_le fun hc => le_iSup_of_le (h i j hc) le_rfl

/-- **M1 — the self is monotone in the coupling.** A sub-coupling sustains a smaller self: `c₁ ⊆ c₂ ⇒
sustainedField c₁ ≤ sustainedField c₂`. (Via `sustainedField_greatest`: the smaller self is
self-upholding under the larger operator.) -/
theorem gfp_mono_in_coupling {c₁ c₂ : V → V → Prop} (h : ∀ i j, c₁ i j → c₂ i j) :
    sustainedField (α := α) c₁ ≤ sustainedField c₂ := by
  apply sustainedField_greatest
  calc sustainedField (α := α) c₁
      = couplingOp c₁ (sustainedField c₁) := (sustainedField_fixed c₁).symm
    _ ≤ couplingOp c₂ (sustainedField c₁) := couplingOp_le_of_sub h _

/-- The coproduct lies below the joint self — the easy `≤` direction. -/
theorem coproduct_le_joint (c : V → V → Prop) (P : V → Prop) :
    coproduct (α := α) c P ≤ sustainedField c :=
  sup_le (gfp_mono_in_coupling fun _ _ h => h.1) (gfp_mono_in_coupling fun _ _ h => h.1)

/-! ## M2 — the foreign part-self vanishes inside `P` -/

/-- **M2 — foreign vertex is `⊥`.** At a vertex `i₀` *inside* `P`, the foreign (`Pᶜ`) part-self is
`⊥`: the foreign operator's sup at `i₀` ranges over `cPc i₀ j`, which demands `i₀ ∉ P` — false — so the
sup is empty. -/
theorem sustainedField_foreign_bot (c : V → V → Prop) (P : V → Prop) {i₀ : V} (hP : P i₀) :
    sustainedField (α := α) (cPc c P) i₀ = ⊥ := by
  have hfix := congrFun (sustainedField_fixed (α := α) (cPc c P)) i₀
  rw [← hfix, couplingOp_apply]
  apply le_antisymm _ bot_le
  exact iSup_le fun j => iSup_le fun hc => absurd hP hc.2.1

/-! ## M3 — the keystone: a live seam forces strictness -/

/-- **The weave at the gfp.** Given a live, **non-redundant** cross seam — `c i₀ j₀` with `i₀ ∈ P`,
`j₀ ∈ Pᶜ`, and `sustainedField c j₀ ≰ sustainedField (cP) i₀` (the cross neighbour's standing is not
already supplied to `i₀` from within `P`) — the joint self **strictly exceeds** the coproduct of the
part-selves:

    coproduct c P  <  sustainedField c.

The joint self is **not** the sum of its parts' selves: *one self, woven at the seam.* The proof: by M2
the coproduct at `i₀` is exactly the part value `sustainedField (cP) i₀`; by `relating_absorbs` the
joint self at `i₀` absorbs the cross neighbour `j₀`'s joint standing; if the coproduct equalled the
joint self there, the part value would already supply that standing — contradicting non-redundancy. -/
theorem weave_gfp_exceeds_coproduct (c : V → V → Prop) (P : V → Prop) {i₀ j₀ : V}
    (hP : P i₀) (_hPc : ¬ P j₀) (hcross : c i₀ j₀)
    (hnonred : ¬ sustainedField (α := α) c j₀ ≤ sustainedField (cP c P) i₀) :
    coproduct (α := α) c P < sustainedField c := by
  refine lt_of_le_of_ne (coproduct_le_joint c P) ?_
  intro heq
  -- the coproduct at i₀ collapses to the part value (M2)
  have hcop : coproduct (α := α) c P i₀ = sustainedField (cP c P) i₀ := by
    simp only [coproduct, Pi.sup_apply, sustainedField_foreign_bot c P hP, sup_bot_eq]
  -- but coproduct = joint, so the part value = joint value at i₀
  have hpart : sustainedField (α := α) (cP c P) i₀ = sustainedField c i₀ := by
    rw [← hcop, heq]
  -- and the seam absorbs j₀'s joint standing into i₀'s
  have habsorb : sustainedField (α := α) c j₀ ≤ sustainedField c i₀ := relating_absorbs c hcross
  -- so the cross neighbour's standing *is* supplied from within P — contradiction
  apply hnonred
  rw [hpart]
  exact habsorb

/-! ## The matrix model demoted to a satisfiability witness

`DistributedSelf.weave_exceeds_coproduct` (matrix) is no longer load-bearing: it certifies the
non-redundant-seam hypothesis is satisfiable (a concrete coupling whose `seamFlow` keeps a live cross
coherence), exactly as `partialDephase` witnesses the `Flow` interface. The matrix↔lattice bridge — that
the two pictures are one under a functor — is genuinely open and now *optional*: this keystone does not
consume it. -/

end RelExist.WeaveGfp
