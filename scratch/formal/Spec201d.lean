/-
Spec 2.01d — the unblocked four (T6, T9, T5, T10) and the coinduction principle.

Normative sources: `scratch/spec/2-00.md`, `2-01.md`, `2-02.md`. Builds on
`Spec201`/`Spec201b`/`Spec201c` (imported). Spec201c changed the tense — Ω exists
(`T2_discharged`), inhabited (`omegaHat_coherent`) — and this file proves the theorem
group that existence unblocked, stated against the constructed universe `ZΩ`.
-/
import Spec201
import Spec201b
import Spec201c
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite.Lattice

namespace RelEx
namespace TwoSorted

/-- Every `Sym2` is inhabited: it has at least one member. -/
theorem sym2_hasMem {α : Type*} (z : Sym2 α) : ∃ a, a ∈ z := by
  induction z using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-! ## T6 — no constitutive origin -/

/-- Spec 2-00 T6 / D13(1). One step of constitutive descent: `z` occurs one level
inside `x` — some relation of x's pattern has z among its endpoints. -/
def Desc (A : Raw) (z x : A.O) : Prop :=
  ∃ r ∈ A.pat x, z ∈ A.endpoints r

/-- Descent is serial in EVERY Raw: patterns are nonempty (D4's unformulability of
emptiness) and every relation has an endpoint (every `Sym2` is inhabited). -/
theorem desc_serial (A : Raw) : ∀ x, ∃ z, Desc A z x := by
  intro x
  obtain ⟨r, hr⟩ := A.pat_nonempty x
  obtain ⟨z, hz⟩ := sym2_hasMem (A.endpoints r)
  exact ⟨z, r, hr, hz⟩

/-- Spec 2-00 T6 — NO CONSTITUTIVE ORIGIN. On any inhabited Raw, constitutive
descent is not well-founded: no ground floor, no first brick, no atom at which the
descent stops. Triple duty (2-00 §5): A1's "ad infinitum" downward; D13(1)'s "no day
zero in the order of constitution"; and the consistency model for non-well-founded
grounding (§6). A well-founded descent would have a minimal element, but seriality
gives every element a predecessor-in-descent. -/
theorem no_constitutive_origin (A : Raw) [Nonempty A.O] :
    ¬ WellFounded (Desc A) := by
  intro hwf
  obtain ⟨m, -, hmin⟩ := hwf.has_min Set.univ ⟨Classical.arbitrary A.O, trivial⟩
  obtain ⟨z, hz⟩ := desc_serial A m
  exact hmin z (Set.mem_univ z) hz

/-- T6 at the constructed universe: Ω, inhabited by ω̂, has non-well-founded descent. -/
theorem no_origin_ZΩ : ¬ WellFounded (Desc ZΩ) :=
  have : Nonempty ZΩ.O := ⟨omegaHat⟩
  no_constitutive_origin ZΩ

/-- Corollary: chains of every finite depth descend from every object.
"Ad infinitum" in its concrete form — built from a global descending sequence. -/
theorem desc_chain (A : Raw) (x : A.O) :
    ∀ n : ℕ, ∃ c : Fin (n + 1) → A.O, c 0 = x ∧
      ∀ i : Fin n, Desc A (c i.succ) (c i.castSucc) := by
  classical
  let f : ℕ → A.O := fun n => Nat.rec x (fun _ prev => (desc_serial A prev).choose) n
  have hfstep : ∀ k, Desc A (f (k + 1)) (f k) := fun k => (desc_serial A (f k)).choose_spec
  intro n
  exact ⟨fun i => f i.val, rfl, fun i => hfstep i.val⟩

/-! ## COIND — identity by unfolding, and self-relation realized -/

/-- Spec 2-00 A4/A6, the formal face: AN OBJECT IS ITS UNFOLDING. Two objects of Ω₀
related by any G-bisimulation are equal — the coinduction principle, which is what
"defined by its relations, ad infinitum" MEANS once the universe exists. This is
`QPF.Cofix.bisim` re-exported at the framework's door; it is also T7's seed (the
representation-layer half of identity-as-limit). The bisimulation condition is the
QPF relation-lifting `QPF.Liftr` of the unfoldings. -/
theorem identity_by_unfolding (R : Ω₀ → Ω₀ → Prop)
    (H : ∀ x y, R x y →
      Functor.Liftr R (QPF.Cofix.dest (F := G) x) (QPF.Cofix.dest (F := G) y)) :
    ∀ x y, R x y → x = y :=
  QPF.Cofix.bisim R H

/-- Spec 2-00 A5, realized: the universe contains an object that relates to itself —
ω̂, whose pattern is exactly its own self-relation. From Spec201c's `pat_omegaHat`.
The ledger's "self-loop by Lambek" made concrete. -/
theorem self_relation_realized :
    ∃ (x : ZΩ.O) (r : ZΩ.R), r ∈ ZΩ.pat x ∧ ZΩ.endpoints r = s(x, x) :=
  ⟨omegaHat, s(omegaHat, omegaHat), by rw [pat_omegaHat]; rfl, rfl⟩

/-! ## T9 — canonicity -/

/-- Identity Raw hom. -/
def Hom.idRaw (A : Raw) : Hom A A where
  fO := id
  fR := id
  end_comm := fun r => by simp [Sym2.map_id]
  pat_comm := fun x => by simp

/-- Composition of Raw homs. -/
def Hom.compRaw {A B C : Raw} (g : Hom B C) (f : Hom A B) : Hom A C where
  fO := g.fO ∘ f.fO
  fR := g.fR ∘ f.fR
  end_comm := fun r => by
    show C.endpoints (g.fR (f.fR r)) = (A.endpoints r).map (g.fO ∘ f.fO)
    rw [g.end_comm (f.fR r), f.end_comm r, Sym2.map_map]
  pat_comm := fun x => by
    show C.pat (g.fO (f.fO x)) = (g.fR ∘ f.fR) '' A.pat x
    rw [g.pat_comm (f.fO x), f.pat_comm x, Set.image_image]
    rfl

/-- Spec 2-00 T9 (Canonicity) / D12's mathematical content: any two bounded-final
Raws are isomorphic — the universe is characterized by its universal property,
independently of every encoding choice. THE ATOMS BELONG TO THE MAP: QPF, the
polynomial, `Quot.out`, `Type 0` are all scaffolding; what is canonical is Ω up to
isomorphism. The two unique morphisms compose to unique endomorphisms, which equal
the identities (uniqueness at each final object applied to itself). -/
theorem final_unique (Z Z' : Raw) (h : IsFinalBRaw Z) (h' : IsFinalBRaw Z') :
    ∃ (f : Hom Z Z') (g : Hom Z' Z),
      Hom.compRaw g f = Hom.idRaw Z ∧ Hom.compRaw f g = Hom.idRaw Z' := by
  obtain ⟨f, -, -⟩ := h'.2 Z h.1
  obtain ⟨g, -, -⟩ := h.2 Z' h'.1
  refine ⟨f, g, ?_, ?_⟩
  · obtain ⟨_, -, uniq⟩ := h.2 Z h.1
    rw [uniq (Hom.compRaw g f) trivial, uniq (Hom.idRaw Z) trivial]
  · obtain ⟨_, -, uniq⟩ := h'.2 Z' h'.1
    rw [uniq (Hom.compRaw f g) trivial, uniq (Hom.idRaw Z') trivial]

/-! ## T5 machinery — depth equivalence, ρ, and reachability -/

/-- Relation lifting through unordered pairs. -/
def Sym2Lift {α β : Type*} (R : α → β → Prop) (p : Sym2 α) (q : Sym2 β) : Prop :=
  ∃ a b c d, p = s(a, b) ∧ q = s(c, d) ∧ ((R a c ∧ R b d) ∨ (R a d ∧ R b c))

/-- Egli–Milner-style lifting to sets: everything matches something, both ways. -/
def SetLift {α β : Type*} (R : α → β → Prop) (S : Set α) (T : Set β) : Prop :=
  (∀ p ∈ S, ∃ q ∈ T, R p q) ∧ (∀ q ∈ T, ∃ p ∈ S, R p q)

/-- Depth-n behavioural equivalence on Ω₀: agreement of unfoldings to depth n —
`d(x, y) ≤ 2⁻ⁿ` without the metric. -/
def EqDepth : ℕ → Ω₀ → Ω₀ → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun x y => SetLift (Sym2Lift (EqDepth n)) (ZΩ.pat x) (ZΩ.pat y)

/-- Spec 2-00 §7 / T5: ρ — the finitely-realized objects: images of finite bounded
descriptions. "The patterns that close in finitely many steps." -/
def FinitelyRealized (x : Ω₀) : Prop :=
  ∃ (A : Raw), Bounded A ∧ Finite A.O ∧ Finite A.R ∧ ∃ (h : Hom A ZΩ) (a : A.O), h.fO a = x

/-- `Sym2Lift` of a reflexive relation is reflexive. -/
theorem sym2Lift_refl {α : Type*} (R : α → α → Prop) (hR : ∀ x, R x x) (p : Sym2 α) :
    Sym2Lift R p p := by
  induction p using Sym2.ind with
  | _ a b => exact ⟨a, b, a, b, rfl, rfl, Or.inl ⟨hR a, hR b⟩⟩

/-- `EqDepth n` is reflexive for every depth n. -/
theorem eqDepth_refl : ∀ (n : ℕ) (x : Ω₀), EqDepth n x x
  | 0, _ => trivial
  | n + 1, _x =>
    ⟨fun p hp => ⟨p, hp, sym2Lift_refl _ (eqDepth_refl n) p⟩,
     fun p hp => ⟨p, hp, sym2Lift_refl _ (eqDepth_refl n) p⟩⟩

/-- Depth-bounded reachable set: `reach x 0 = {x}`; each step adds all endpoints of
all relations of members. -/
def reach (x : Ω₀) : ℕ → Set Ω₀
  | 0 => {x}
  | k + 1 => reach x k ∪ {w | ∃ z ∈ reach x k, ∃ r ∈ ZΩ.pat z, w ∈ ZΩ.endpoints r}

theorem reach_mono_step (x : Ω₀) (k : ℕ) :
    ∀ z ∈ reach x k, ∀ r ∈ ZΩ.pat z, ∀ w ∈ ZΩ.endpoints r, w ∈ reach x (k + 1) :=
  fun z hz r hr _w hw => Or.inr ⟨z, hz, r, hr, hw⟩

/-- The membership set of an unordered pair is finite (at most two elements). -/
theorem sym2_mem_finite {α : Type*} (p : Sym2 α) : {a | a ∈ p}.Finite := by
  induction p using Sym2.ind with
  | _ a b =>
    refine Set.Finite.subset ((Set.finite_singleton b).insert a) (fun w hw => ?_)
    rw [Set.mem_setOf_eq, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

/-- Reachability is finite at every depth: patterns are finite (`bounded_ZΩ`) and
each relation contributes at most two endpoints. The enabling lemma for T5. -/
theorem reach_finite (x : Ω₀) (k : ℕ) : (reach x k).Finite := by
  induction k with
  | zero => exact Set.finite_singleton x
  | succ k ih =>
    refine Set.Finite.union ih ?_
    have hbig : (⋃ z ∈ reach x k, ⋃ r ∈ ZΩ.pat z, {w | w ∈ ZΩ.endpoints r}).Finite :=
      ih.biUnion (fun z _ => (bounded_ZΩ z).biUnion (fun r _ => sym2_mem_finite _))
    refine Set.Finite.subset hbig (fun w hw => ?_)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact hw

/-- The one-point self-loop Raw: `omegaHat`'s finite realization. -/
def loopRaw : Raw.{0} where
  O := PUnit
  R := Sym2 PUnit
  endpoints := id
  pat := fun _ => {s(PUnit.unit, PUnit.unit)}
  pat_nonempty := fun _ => ⟨s(PUnit.unit, PUnit.unit), rfl⟩

/-- ω̂ is finitely realized (smoke test of `FinitelyRealized`, and ρ ≠ ∅): it is the
image of the finite one-point self-loop Raw. -/
theorem omegaHat_finitelyRealized : FinitelyRealized omegaHat := by
  refine ⟨loopRaw, fun _ => Set.finite_singleton _, ?finO, ?finR,
    ⟨fun _ => omegaHat, fun r => Sym2.map (fun _ => omegaHat) r, fun _ => rfl, ?patc⟩,
    PUnit.unit, rfl⟩
  case finO => show Finite PUnit; exact inferInstance
  case finR => show Finite (Sym2 PUnit); exact inferInstance
  case patc =>
    intro x
    show ZΩ.pat omegaHat = (fun r => Sym2.map (fun _ => omegaHat) r) '' {s(PUnit.unit, PUnit.unit)}
    rw [pat_omegaHat, Set.image_singleton, Sym2.map_pair_eq]

/-! ## T10s — genesis, anchored (statement only; open in truth-value) -/

/-- One generative step: y arises within x's unfolding — the orbit-growing relation
for D13(3). -/
def Arises (y x : Ω₀) : Prop := Desc ZΩ y x

/-- The orbit of the self-loop: everything reachable from ω̂ by finite unfolding. -/
def omegaOrbit : Set Ω₀ := { y | Relation.ReflTransGen Arises y omegaHat }

/-- Sanity: ω̂ is in its own orbit (the `refl` case). -/
theorem omegaHat_mem_omegaOrbit : omegaHat ∈ omegaOrbit := Relation.ReflTransGen.refl

/-- Spec 2-00 T10 / D13(3) — GENESIS, the named conjecture: does all multiplicity
unfold from self-meeting? Stated as depth-density of ω̂'s orbit (the metric-free form
matching T5's). OPEN IN TRUTH-VALUE: this declaration is an anchor, not a claim —
proof or refutation is future work, and per D13 the framework brings no perspective
where a proof can be had. With T5 in hand, Genesis reduces to whether the
finitely-realized objects are orbit-approximable — a genuinely open combinatorial
question about which finite loop-closed shapes ω̂'s unfolding reaches. -/
def Genesis : Prop :=
  ∀ (x : Ω₀) (n : ℕ), ∃ y ∈ omegaOrbit, EqDepth n x y

end TwoSorted
end RelEx

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms no_constitutive_origin
#print axioms no_origin_ZΩ
#print axioms desc_chain
#print axioms identity_by_unfolding
#print axioms self_relation_realized
#print axioms final_unique
#print axioms eqDepth_refl
#print axioms reach_finite
#print axioms omegaHat_finitelyRealized
#print axioms omegaHat_mem_omegaOrbit
end AxiomAudit

/-
-- Specs 2-00 / 2-01 / 2-02 ↔ scratch/formal/Spec201d.lean
-- T6 (no origin)      = RelEx.TwoSorted.desc_serial, no_constitutive_origin, no_origin_ZΩ, desc_chain
-- COIND               = RelEx.TwoSorted.identity_by_unfolding, self_relation_realized
-- T9 (canonicity)     = RelEx.TwoSorted.final_unique (+ Hom.idRaw, Hom.compRaw)
-- T5 machinery        = RelEx.TwoSorted.Sym2Lift, SetLift, EqDepth, FinitelyRealized,
--                       sym2Lift_refl, eqDepth_refl, reach, reach_mono_step,
--                       sym2_mem_finite, reach_finite, loopRaw, omegaHat_finitelyRealized
-- T5 (closing_dense)  = DEFERRED (drop-clause §5): the truncation assembly; plan in PR
-- T10s (genesis)      = RelEx.TwoSorted.Arises, omegaOrbit, omegaHat_mem_omegaOrbit, Genesis
--
-- Deviations from 2-01-mechanization-d.md:
--   * Registered as a seventh Lake library root (`Spec201d`).
--   * T5 `closing_dense` DEFERRED per the §5 drop-clause: the EqDepth/ρ/reach
--     machinery (load-bearing for T4/T7) is proved; the final truncation assembly
--     is deferred, its blueprint recorded in the PR description. File stays
--     sorry-free. T5 labelled [machinery proved; assembly deferred].
--   * `identity_by_unfolding` delivered as the `Functor.Liftr`-based re-export of
--     `QPF.Cofix.bisim` (the clean mathlib-API wrapper).
-/
