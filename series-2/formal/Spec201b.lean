/-
Spec 2.1b — the transfer theorem and the design-ready group.

Normative sources: `series-2/2-0.md` and `series-2/2-1.md`. Builds on
`Spec201` (imported): the two-sorted signature `Model`/`Raw`/`Hom`, `ctx`,
`SelfAnchored`, `generic_properness`, `coprod`, and the L1 covariety closures.

Centerpiece — the **transfer theorem** (T2t): spec 2.1 §4's three-step
construction of Ω, machine-checked *modulo the existence of the raw final
coalgebra νF*. With L1 proved (Spec201), the covariety step (2)→(3) is
formalized here: if the raw universe νF is final, then Ω — the universe of
coherent objects — exists and is final among coherent models, and every
coherent description lands in the coherent part. The sole remaining gap is the
classical existence of νF (Adámek–Trnková 2011), scheduled for its own order.

Deliverables (work order 2-1-mechanization-b.md §1):
  T2t-i    coherentPart_good        (CoherentAt, Good, coherentPartO/R)
  T2t-ii   image_good
  T2t-iii  transfer, transfer_lands
  T2t-iv   subtype packaging        — DROPPED (see mapping table)
  PRJb     deployable_dichotomy     (+ Deployable)
  T12s     shared_bearing_in_both_apertures
  P1b1     shared_part_barrier      (+ RelatesBeyond)
  P2c      contexts_differ
  C2d      coprod_disconnected      (+ StepR, Connected)
  T14q     qualitative containment predicates + heart-corner witness (partial; see foot)

Several definitions are introduced ahead of spec 2.2 and are flagged
`pending ratification (2.2)` in their doc-comments (work order §8).
-/
import Spec201
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

namespace RelEx
namespace TwoSorted

universe u

/-! ## Part A — the transfer theorem (T2t) -/

/-- Spec 2.1 §4. Coherence at a single relation (elementwise; ambient-absolute):
every endpoint of `r` keeps `r` in its pattern. -/
def CoherentAt (Z : Raw) (r : Z.R) : Prop :=
  ∀ x : Z.O, x ∈ Z.endpoints r → r ∈ Z.pat x

/-- Spec 2.1 §4. A good pair of subsets: elementwise coherent and closed under
the two-sorted structure (endpoints of kept relations are kept objects; patterns
of kept objects are kept relations). Good pairs are the two-sorted
subcoalgebras-with-coherence; `coherentPart` below is their union. -/
structure Good (Z : Raw) (UO : Set Z.O) (UR : Set Z.R) : Prop where
  coh : ∀ r ∈ UR, CoherentAt Z r
  ends : ∀ r ∈ UR, ∀ x ∈ Z.endpoints r, x ∈ UO
  pats : ∀ x ∈ UO, Z.pat x ⊆ UR

/-- Spec 2.1 §4, step (3): the coherent part of a raw universe (objects side) —
the union of all good pairs. "Ω is the greatest coherent subcoalgebra of νF." -/
def coherentPartO (Z : Raw) : Set Z.O := ⋃₀ { UO | ∃ UR, Good Z UO UR }

/-- The coherent part, relations side. -/
def coherentPartR (Z : Raw) : Set Z.R := ⋃₀ { UR | ∃ UO, Good Z UO UR }

/-- Any good pair is contained (objects side) in the coherent part. -/
theorem subset_coherentPartO {Z : Raw} {UO : Set Z.O} {UR : Set Z.R}
    (h : Good Z UO UR) : UO ⊆ coherentPartO Z :=
  fun _ hx => Set.mem_sUnion.mpr ⟨UO, ⟨UR, h⟩, hx⟩

/-- Any good pair is contained (relations side) in the coherent part. -/
theorem subset_coherentPartR {Z : Raw} {UO : Set Z.O} {UR : Set Z.R}
    (h : Good Z UO UR) : UR ⊆ coherentPartR Z :=
  fun _ hr => Set.mem_sUnion.mpr ⟨UR, ⟨UO, h⟩, hr⟩

/-- Spec 2.1 §4, T2t-i. The union of all good pairs is itself good: the coherent
part is the GREATEST good pair (Knaster–Tarski by hand, on an elementwise-closed
property). This is the "greatest coherent subcoalgebra" as a pair of subsets. -/
theorem coherentPart_good (Z : Raw) :
    Good Z (coherentPartO Z) (coherentPartR Z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨UR, ⟨UO, hG⟩, hrUR⟩ := Set.mem_sUnion.mp hr
    exact hG.coh r hrUR
  · intro r hr x hx
    obtain ⟨UR, ⟨UO, hG⟩, hrUR⟩ := Set.mem_sUnion.mp hr
    exact subset_coherentPartO hG (hG.ends r hrUR x hx)
  · intro x hx r hr
    obtain ⟨UO, ⟨UR, hG⟩, hxUO⟩ := Set.mem_sUnion.mp hx
    exact subset_coherentPartR hG (hG.pats x hxUO hr)

/-- Bridge: forget a `Model`'s coherence bundling to get a `Raw`. -/
def Model.toRaw (M : Model) : Raw :=
  ⟨M.O, M.R, M.endpoints, M.pat, M.pat_nonempty⟩

/-- Spec 2.1 §4, T2t-ii (image lemma): the image of ANY hom from a coherent
model is a good pair — the elementwise form of "homomorphic images of coherent
coalgebras are coherent," the covariety closure that powers the transfer. -/
theorem image_good (M : Model) (Z : Raw) (h : Hom M.toRaw Z) :
    Good Z (Set.range h.fO) (Set.range h.fR) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨r, rfl⟩ x' hx'
    rw [h.end_comm r, Sym2.mem_map] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    rw [h.pat_comm a]
    exact ⟨r, M.coherent r a ha, rfl⟩
  · rintro _ ⟨r, rfl⟩ x' hx'
    rw [h.end_comm r, Sym2.mem_map] at hx'
    obtain ⟨a, _, rfl⟩ := hx'
    exact ⟨a, rfl⟩
  · rintro _ ⟨x, rfl⟩ r hr
    rw [h.pat_comm x, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact ⟨a, rfl⟩

/-- Two-sorted finality for raw universes (the ambient νF hypothesis).
Pinned to a single universe `u` so the ambient and coherent models live together. -/
def IsFinalRaw (Z : Raw.{u}) : Prop :=
  ∀ A : Raw.{u}, ∃! _h : Hom A Z, True

/-- Spec 2.0 T2 / spec 2.1 §4 — THE TRANSFER THEOREM. If the raw universe is
final, then every coherent model admits exactly one morphism into it. Objects
exist, modulo the raw universe: the covariety step of Ω's construction is
machine-checked; the sole remaining gap is the classical existence of νF
(Adámek–Trnková 2011). Philosophically: given any raw universe at all, the
coherent patterns in it form a universe of their own — every coherent
description specifies exactly one object. -/
theorem transfer (Z : Raw.{u}) (hZ : IsFinalRaw Z) (M : Model.{u}) :
    ∃! _h : Hom M.toRaw Z, True := hZ M.toRaw

/-- Spec 2.1 §4, T2t-iii (companion): the unique morphism lands entirely in the
coherent part. Objects live nowhere but among the coherent patterns. -/
theorem transfer_lands (Z : Raw) (M : Model) (h : Hom M.toRaw Z) :
    (∀ x, h.fO x ∈ coherentPartO Z) ∧ (∀ r, h.fR r ∈ coherentPartR Z) := by
  have hg := image_good M Z h
  exact ⟨fun x => subset_coherentPartO hg ⟨x, rfl⟩,
         fun r => subset_coherentPartR hg ⟨r, rfl⟩⟩

/-! ## Part B — the design-ready group -/

/-- Spec 2.1 §3.7 (pre-registered definition, D15) — pending ratification (2.2).
An attention is DEPLOYABLE by `x` iff it is the aperture of some actual attending
of `x`. A8 recognizes no free-floating attention: all attending is along a
relation through its context. -/
def Deployable (M : Model) (x : M.O) (A : Set M.R) : Prop :=
  ∃ r ∈ M.pat x, A = ctx M x r

/-- Spec 2.0 §3, PR-J(b) — the DICHOTOMY, in the exact form the interface
supports: every deployable attention is proper, or its witnessing relation is
self-anchored. With `reflexive_saturation` (Spec201) this settles PR-J(b)'s
interface-level status: properness of deployable attention is a THEOREM off the
self-anchored locus and an AXIOM-candidate on it — the same address C3 gave
A8(i). Full PR-J(b) ("every deployable attention is proper") is therefore exactly
as strong as A8(i)-at-loops: the pre-registered question resolved. -/
theorem deployable_dichotomy (M : Model) (x : M.O) (A : Set M.R)
    (hA : Deployable M x A) :
    A ⊂ M.pat x ∨ ∃ r ∈ M.pat x, A = ctx M x r ∧ SelfAnchored M r := by
  obtain ⟨r, hr, rfl⟩ := hA
  by_cases h : SelfAnchored M r
  · exact Or.inr ⟨r, hr, rfl, h⟩
  · exact Or.inl (generic_properness M r x hr h)

/-- Spec 2.0 §2.5 / T12, static skeleton: a SHARED bearing on `r` sits inside
`r`'s aperture on EVERY side that contains it. One enrichment is aperture-material
for both relata at once — the static mechanism by which clarifying a shared
relation clarifies both parties. The symmetry of the two components IS the point.
Propagation over time is dynamics, Series 3 (2.0 O9). -/
theorem shared_bearing_in_both_apertures (M : Model) (r s : M.R) (x y : M.O)
    (hsx : s ∈ M.pat x) (hsy : s ∈ M.pat y)
    (hbears : M.dy r ∈ M.endpoints s) :
    s ∈ ctx M x r ∧ s ∈ ctx M y r :=
  ⟨⟨hsx, hbears⟩, ⟨hsy, hbears⟩⟩

/-- `y` relates beyond `x`: some part of `y` is not shared with `x`.
Pending ratification (2.2). -/
def RelatesBeyond (M : Model) (y x : M.O) : Prop :=
  ∃ r ∈ M.pat y, r ∉ M.pat x

/-- Spec 2.0 §2.4 / general P1, barrier one (shared-part bound): whenever `y`
relates beyond `x`, the shared part is a PROPER part of `y` — so `x`'s access to
`y`, which runs entirely through shared relations, cannot exhaust `y`. Barrier two
(the foreign-context bound) needs the witnessing structure of a later spec and is
deliberately absent here. -/
theorem shared_part_barrier (M : Model) (x y : M.O) (h : RelatesBeyond M y x) :
    M.pat x ∩ M.pat y ⊂ M.pat y := by
  obtain ⟨r, hry, hrnx⟩ := h
  refine (Set.ssubset_iff_of_subset Set.inter_subset_right).mpr ⟨r, hry, ?_⟩
  exact fun hmem => hrnx hmem.1

/-- A witness model for P2c/T14q (heart corner): objects and relations are
`Bool`; `true` is the "large" object holding both relations, `false` the "small"
one holding only the shared relation `true`. Pending ratification (2.2). -/
def boolWitness : Model.{0} where
  O := Bool
  R := Bool
  endpoints b := match b with
    | true => s(true, false)
    | false => s(true, true)
  pat b := match b with
    | true => Set.univ
    | false => {true}
  pat_nonempty := by intro b; cases b <;> exact ⟨true, by simp⟩
  coherent := by intro r x hx; cases r <;> cases x <;> simp_all [Sym2.mem_iff]
  dy _ := true

/-- Spec 2.0 §2.4 / P2 with content: one shared relation, two genuinely unequal
apertures. Spec201's P2 was type-level (the two directions belong to different
objects); this witness shows the difference is MATERIAL — the same relation's
context in `x` contains a bearing its context in `y` lacks, because the bearing
is private to `x`. Same part, different wholes, different lenses. -/
theorem contexts_differ :
    ∃ (M : Model.{0}) (r : M.R) (x y : M.O),
      r ∈ M.pat x ∧ r ∈ M.pat y ∧ ctx M x r ≠ ctx M y r := by
  refine ⟨boolWitness, true, true, false, Set.mem_univ _, rfl, ?_⟩
  intro heq
  have hin : (false : Bool) ∈ ctx boolWitness true true :=
    ⟨Set.mem_univ _, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  rw [heq] at hin
  have hbad : (false : Bool) ∈ boolWitness.pat false := hin.1
  simp [boolWitness] at hbad

/-- One step of relational connection between objects (raw level): some relation
has both among its endpoints. Pending ratification (2.2). -/
def StepR (Z : Raw) (x y : Z.O) : Prop :=
  ∃ r : Z.R, x ∈ Z.endpoints r ∧ y ∈ Z.endpoints r

/-- Spec 2.0 C2 (weak form) — pending ratification (2.2): a raw universe is
connected iff any two objects are linked by a finite chain of shared-endpoint
steps. -/
def Connected (Z : Raw) : Prop :=
  ∀ x y : Z.O, Relation.ReflTransGen (StepR Z) x y

/-- Spec 2.0 C2, SHARPENED: connectivity is NOT interface-forced — the coproduct
of two inhabited raw universes is disconnected. Consequence: C2, if true, is a
theorem about Ω SPECIFICALLY (about what the closure of coherent descriptions
produces), not about the signature. The desired answer ("the fish is a part of
me, ever so slightly") cannot be obtained by definitional accident; it must be
earned at 2.2. This is D15 working as intended — an anti-desired-outcome result
demonstrating the definitions were not tuned. -/
theorem coprod_disconnected (A B : Raw) (a : A.O) (b : B.O) :
    ¬ Connected (coprod A B) := by
  intro hconn
  -- A single connection step preserves left-ness: a coproduct relation is all-inl
  -- or all-inr, so its two endpoints share a side.
  have step_pres : ∀ p q : (coprod A B).O,
      StepR (coprod A B) p q → p.isLeft = q.isLeft := by
    rintro p q ⟨rr, hp, hq⟩
    cases rr with
    | inl r =>
      simp only [coprod, Sum.elim_inl, Sym2.mem_map] at hp hq
      obtain ⟨_, _, rfl⟩ := hp; obtain ⟨_, _, rfl⟩ := hq; rfl
    | inr r =>
      simp only [coprod, Sum.elim_inr, Sym2.mem_map] at hp hq
      obtain ⟨_, _, rfl⟩ := hp; obtain ⟨_, _, rfl⟩ := hq; rfl
  -- Hence any chain out of `Sum.inl a` stays left.
  have inv : ∀ y, Relation.ReflTransGen (StepR (coprod A B)) (Sum.inl a) y →
      (Sum.inl a : (coprod A B).O).isLeft = y.isLeft := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hstep ih => rw [ih]; exact step_pres _ _ hstep
  have hcontra := inv (Sum.inr b) (hconn (Sum.inl a) (Sum.inr b))
  simp at hcontra

/-! ## Part C — T14q (SHOULD, partial): qualitative containment predicates

The *unweighted shadows* of π (graded forms need 2.2's quality-weighting).
All three predicates are `pending ratification (2.2)`. -/

/-- Qualitative full containment (unweighted shadow of π = 1). Pending ratification (2.2). -/
def ContainedIn (M : Model) (x y : M.O) : Prop := M.pat x ⊆ M.pat y

/-- Qualitative touching (unweighted shadow of π > 0). Pending ratification (2.2). -/
def Touches (M : Model) (x y : M.O) : Prop := (M.pat x ∩ M.pat y).Nonempty

/-- Qualitative mutual partiality (neither contains the other, yet they touch).
Pending ratification (2.2). -/
def MutualPartial (M : Model) (x y : M.O) : Prop :=
  Touches M x y ∧ ¬ ContainedIn M x y ∧ ¬ ContainedIn M y x

/-- Spec 2.0 T14, the heart corner: containment one way but not the other —
"the heart is a part of me; I am not (all of) the heart." Witnessed by
`boolWitness`, where `false`'s pattern `{true}` is contained in `true`'s pattern
`univ`, but not conversely. (Only this corner is mechanized; the remaining three
corners and the graded form await π at 2.2 — see the file foot.) -/
theorem containment_asymmetric_witness :
    ∃ (M : Model.{0}) (x y : M.O), ContainedIn M x y ∧ ¬ ContainedIn M y x := by
  refine ⟨boolWitness, false, true, fun _ _ => Set.mem_univ _, ?_⟩
  intro hsub
  have hbad : (false : Bool) ∈ boolWitness.pat false := hsub (Set.mem_univ false)
  simp [boolWitness] at hbad

end TwoSorted
end RelEx

/-! ## Axiom audit (work order §6, item 2) -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms coherentPart_good
#print axioms image_good
#print axioms transfer
#print axioms transfer_lands
#print axioms deployable_dichotomy
#print axioms shared_bearing_in_both_apertures
#print axioms shared_part_barrier
#print axioms contexts_differ
#print axioms coprod_disconnected
#print axioms containment_asymmetric_witness
end AxiomAudit

/-
-- Specs 2.0 / 2.1 ↔ series-2/formal/Spec201b.lean
-- T2 (transfer, i)    = RelEx.TwoSorted.coherentPart_good (+ CoherentAt, Good, coherentPartO/R)
-- T2 (transfer, ii)   = RelEx.TwoSorted.image_good
-- T2 (transfer, iii)  = RelEx.TwoSorted.transfer, RelEx.TwoSorted.transfer_lands
-- T2 (packaging, iv)  = DROPPED (see deviations)
-- PR-J(b) (dichotomy) = RelEx.TwoSorted.deployable_dichotomy (+ Deployable)
-- T12 (statics)       = RelEx.TwoSorted.shared_bearing_in_both_apertures
-- P1 (barrier one)    = RelEx.TwoSorted.shared_part_barrier (+ RelatesBeyond)
-- P2 (content)        = RelEx.TwoSorted.contexts_differ (+ boolWitness)
-- C2 (sharpening)     = RelEx.TwoSorted.coprod_disconnected (+ StepR, Connected)
-- T14q                = RelEx.TwoSorted.ContainedIn/Touches/MutualPartial;
--                       RelEx.TwoSorted.containment_asymmetric_witness (heart corner only)
-- Pending ratification (2.2): Deployable*, RelatesBeyond, StepR, Connected,
--   ContainedIn, Touches, MutualPartial   (*Deployable is 2.1 §3.7's definition,
--   transcribed; the rest are new here.)
--
-- Deviations from 2-1-mechanization-b.md:
--   * File registered as a fourth Lake library root (`Spec201b`) alongside
--     Series2/Spec200/Spec201 in `lake/lakefile.toml`.
--   * T2t-iv (subtype packaging of the coherent part as a `Model`) DROPPED per the
--     work order's §3.4 droppable clause: constructing `Sym2` over a subtype from
--     membership proofs is dependent-elimination plumbing, and the transfer theorem
--     already carries the mathematical content. Noted, not attempted further.
--   * `good_le_coherentPart` is split into `subset_coherentPartO`/`subset_coherentPartR`
--     (the two sorts have separate carriers).
--   * T14q delivered partially: the three predicates plus the heart-corner witness
--     (`containment_asymmetric_witness`); the remaining three corners are not
--     mechanized (the graded forms await π at 2.2).
-/
