/-
Spec 2.04g — the C1 landing over the corrected functor, and P3h's positive half
(2-04-mechanization-c Stages 2–3 = order b Stages 3–4).

Normative source: `scratch/spec/2-04.md`, `2-02.md` §4 (the C1 conditional), and the work order
`2-04-mechanization-c.md`. Continues `Spec204f.lean` (`destEquivC`) and the whole chain
(`WindowlessC`/`InternalC`/`EndpointContainedC` from Spec204b, `CoherentC`/`coprodC` from Spec204,
`T16_ω` from Spec204e). Specs win. No declaration consults §8.
-/
import Spec204f

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 2 — the C1 landing (2-04-mechanization-c §2; FP-B4, FP-B5 — the star)

*We are born as bridges.* The corrected analogue of Spec202's `no_windowless_of_connected_of_no_total`:
a windowless object, in a coherent universe where it is grounded-connected to every relation,
would have to be total — contradicting no-total (`T16_ω` at the ω-tier). -/

/-- One step of object-connectivity in a corrected coalgebra: `y` is an object endpoint of some
relation in `x`'s pattern (the corrected `StepR`). -/
def StepRC (A : RawC) (x y : A.O) : Prop := ∃ r ∈ A.pat x, Sum.inl y ∈ A.endpoints r

/-- A corrected coalgebra is (object-)connected when every object reaches every object. -/
def ConnectedC (A : RawC) : Prop := ∀ x y : A.O, Relation.ReflTransGen (StepRC A) x y

/-- The C1 mechanism: a windowless object's pattern contains the pattern of every object it reaches
(the containment invariant propagates along connection), and if it is grounded-connected to every
relation (each relation has a reachable object endpoint), it is TOTAL. `K1` (coherence) turns a
reachable object endpoint into pattern-membership. -/
theorem windowlessC_total (A : RawC) (hCoh : CoherentC A) (x : A.O)
    (hw : WindowlessC A x)
    (hgr : ∀ s : A.R, ∃ w : A.O, Sum.inl w ∈ A.endpoints s ∧
      Relation.ReflTransGen (StepRC A) x w) :
    A.pat x = Set.univ := by
  have hweq : InternalC A x = A.pat x := hw
  have inv : ∀ y, Relation.ReflTransGen (StepRC A) x y → A.pat y ⊆ A.pat x := by
    intro y hy
    induction hy with
    | refl => exact subset_rfl
    | tail _ hstep ih =>
        obtain ⟨r', hp, hq⟩ := hstep
        have hr'int : r' ∈ InternalC A x := by rw [hweq]; exact ih hp
        exact hr'int.2 _ hq
  refine Set.eq_univ_of_forall (fun s => ?_)
  obtain ⟨w, hws, hreach⟩ := hgr s
  exact inv w hreach (hCoh.1 s w hws)

/-- FP-B5 — CONFIRMED: **no windowless object on the grounded-connected part** of a coherent
universe with no total object. *We are born as bridges*, machine-checked. Both prices are on the
record: the **ω-scaffold** enters through the no-total hypothesis (discharged over Ω_C by `T16_ω`,
itself scaffold-assisted — the D4 κ-loan's ω-instance, owing T11); **hostedness/grounding** enters
through `hgr` (grounded-connectivity), the §5 doctrine's relativization — which FP-B4 shows fails
globally. Cf. 2-02 §4's original conjecture route. -/
theorem no_windowlessC_of_connected_no_total (A : RawC) (hCoh : CoherentC A) (x : A.O)
    (hgr : ∀ s : A.R, ∃ w : A.O, Sum.inl w ∈ A.endpoints s ∧
      Relation.ReflTransGen (StepRC A) x w)
    (hnt : A.pat x ≠ Set.univ) :
    ¬ WindowlessC A x :=
  fun hw => hnt (windowlessC_total A hCoh x hw hgr)

/-! ### FP-B4 — Ω_C is not globally connected (hostile; the disconnection witness) -/

/-- Reachability out of an `inl`-object in a coproduct stays among `inl`-objects: the two
components never connect. -/
theorem reach_coprodC_inl (A B : RawC) (a : A.O) :
    ∀ y, Relation.ReflTransGen (StepRC (coprodC A B)) (Sum.inl a) y → ∃ a', y = Sum.inl a' := by
  intro y hy
  induction hy with
  | refl => exact ⟨a, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨a', rfl⟩ := ih
      obtain ⟨r, hp, hq⟩ := hstep
      simp only [coprodC, Sum.elim_inl, Set.mem_image] at hp
      obtain ⟨r0, _, rfl⟩ := hp
      simp only [coprodC, Sum.elim_inl, Sym2.mem_map] at hq
      obtain ⟨e, _, hmap⟩ := hq
      rcases e with o | rr
      · rw [Sum.map_inl] at hmap; exact ⟨o, (Sum.inl.inj hmap).symm⟩
      · rw [Sum.map_inr] at hmap; exact absurd hmap (by simp)

/-- The coproduct of two universes is disconnected: no object of the left component reaches any
object of the right. The corrected analogue of Spec201b's `coprod_disconnected`. -/
theorem coprodC_disconnected (A B : RawC) (a : A.O) (b : B.O) :
    ¬ Relation.ReflTransGen (StepRC (coprodC A B)) (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨a', ha'⟩ := reach_coprodC_inl A B a (Sum.inr b) h
  exact absurd ha' (by simp)

/-- FP-B4 — CONFIRMED: a COHERENT universe can be globally disconnected. The coproduct of two
copies of the coherent higher seed is coherent (`coherentC_sum`) yet not connected — unhosted
chaff and disjoint behaviours are the norm, so the C1 landing is honestly relativized to the
connected part (FP-B5's `hgr`), not unrelativized. -/
theorem FP_B4_disconnection : ∃ A : RawC, CoherentC A ∧ ¬ ConnectedC A :=
  ⟨coprodC seed3 seed3, coherentC_sum seed3_coherent seed3_coherent,
   fun hconn => coprodC_disconnected seed3 seed3 PUnit.unit PUnit.unit
     (hconn (Sum.inl PUnit.unit) (Sum.inr PUnit.unit))⟩

/-! ## Stage 3 — P3h, positive direction (2-04-mechanization-c §3; FP-B6)

The close preserves hostedness: a relation hosted in a coherent description maps to a hosted
relation of Ω_C. With `unhosted_exists` (Spec204b), FP3's split lands — P3h holds on the
close-image of descriptions, fails globally. -/

/-- A connected coherent description: coherent, connected, and every relation hosted (borne within
some object's pattern). The `close`-images of these are where P3h's positive half lives. -/
def ConnectedDescription (A : RawC) : Prop :=
  CoherentC A ∧ ConnectedC A ∧ ∀ r : A.R, ∃ w : A.O, r ∈ A.pat w

/-- Hostedness is preserved by the close: a relation held in `A` maps to a relation held in Ω_C
(inside the closed object's pattern). -/
theorem hosted_of_closeC (A : RawC) (hA : BoundedC A) (r : A.R) (w : A.O) (hrw : r ∈ A.pat w) :
    hostedC (fRC A hA r) :=
  ⟨fOC A hA w, ⟨r, hrw, rfl⟩⟩

/-- FP-B6 — CONFIRMED: every relation-point in the close-image of a connected coherent description
is hosted. Together with `unhosted_exists` (Spec204b — unhosted points exist globally), FP3's split
is complete: **P3h fails globally, holds on the connected close-image.** The §5 doctrine's positive
half, mechanized. -/
theorem hosted_of_closeC_connected (A : RawC) (hA : BoundedC A)
    (hd : ConnectedDescription A) (r : A.R) : hostedC (fRC A hA r) := by
  obtain ⟨w, hw⟩ := hd.2.2 r
  exact hosted_of_closeC A hA r w hw

/-! ## Stage 4 — B5 interface pack (2-04-mechanization-c §4; T14 + Reveal + deployable, light) -/

/-- T14 (R1) — containment is a preorder (reflexive). -/
theorem containedInC_refl (A : RawC) (x : A.O) : ContainedInC A x x := subset_rfl

/-- T14 (R1) — containment is a preorder (transitive). -/
theorem containedInC_trans (A : RawC) {x y z : A.O}
    (h₁ : ContainedInC A x y) (h₂ : ContainedInC A y z) : ContainedInC A x z := h₁.trans h₂

/-- T14 (R1) — π ratified: containment is `π = pat x` (the shared part exhausts the observer). -/
theorem containedInC_iff_piC (A : RawC) (x y : A.O) :
    ContainedInC A x y ↔ piC A x y = A.pat x := Set.inter_eq_left.symm

/-- Spec 2-01 §3.7 (D15), corrected: an attention is DEPLOYABLE by `x` iff it is the context of some
actual attending of `x`. -/
def DeployableC (A : RawC) (x : A.O) (Aset : Set A.R) : Prop :=
  ∃ r ∈ A.pat x, Aset = ctxC A x r

/-- PR-J(b), corrected — THE DICHOTOMY: every deployable attention is proper, or its witnessing
relation is self-anchored (the same address the R-C3 split gave A8(i), now over the tower). -/
theorem deployableC_dichotomy (A : RawC) (x : A.O) (Aset : Set A.R) (hA : DeployableC A x Aset) :
    Aset ⊂ A.pat x ∨ ∃ r ∈ A.pat x, Aset = ctxC A x r ∧ SelfAnchoredC A r := by
  obtain ⟨r, hr, rfl⟩ := hA
  by_cases h : SelfAnchoredC A r
  · exact Or.inr ⟨r, hr, rfl, h⟩
  · exact Or.inl (genericC_properness A x r hr h)

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms windowlessC_total
#print axioms no_windowlessC_of_connected_no_total
#print axioms coprodC_disconnected
#print axioms FP_B4_disconnection
#print axioms hosted_of_closeC_connected
#print axioms deployableC_dichotomy
end AxiomAudit
