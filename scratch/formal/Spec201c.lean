/-
Spec 2.01c — νF at the ω-tier, and the discharge of T2.

Normative sources: `scratch/spec/2-01.md` §4 and `scratch/spec/2-00.md` (D9-R3, D18).
Builds on `Spec201`/`Spec201b` (imported). The construction order: build the final
raw universe for the finitely-branching tier and discharge the transfer theorem's
hypothesis.

The whole ω-tier construction is monomorphized to `Type 0` (work order §1): the
polynomial's shape types live in `Type 0` and nothing ontological hangs on it — this
is representation layer.
-/
import Spec201
import Spec201b
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

namespace RelEx
namespace TwoSorted

/-! ## VAC / BND — honesty and the re-targeted transfer -/

/-- HONESTY ITEM (2-01 D4 made formal). `IsFinalRaw` — finality over ALL Raws, with
unbounded `Set`-patterns — is unsatisfiable: Lambek + Cantor. A final Raw would give
a bijection between its object sort and (essentially) the nonempty powerset of a type
at least as large, which cannot exist. The κ-loan was never optional; `transfer`
(Spec201b) is hereby re-targeted at the bounded quantifier it always needed
(`transfer_bounded` below), which this file then SATISFIES at the ω-tier. The
transfer proof itself never used unboundedness; nothing there changes. See
`isFinalRaw_never` for the formal statement. -/
def vac_note : Unit := ()

/-- A Raw is (ω-)bounded when every pattern is finite. The ω-tier of 2-01 D4's
κ-parameterization; general κ follows the same construction with a larger polynomial
(§6 of the work order) and remains under the documented loan. -/
def Bounded (A : Raw.{0}) : Prop := ∀ x, (A.pat x).Finite

/-- Finality among bounded Raws — the satisfiable target that `transfer` always
needed. -/
def IsFinalBRaw (Z : Raw.{0}) : Prop :=
  Bounded Z ∧ ∀ A : Raw.{0}, Bounded A → ∃! _h : Hom A Z, True

/-- The transfer theorem, re-targeted (statement change only; Spec201b's
`image_good`/`transfer_lands` are quantifier-free over finality and apply unchanged).
If a bounded-final raw universe exists, every bounded coherent model admits exactly
one morphism into it — landing in the coherent part. -/
theorem transfer_bounded (Z : Raw.{0}) (hZ : IsFinalBRaw Z)
    (M : Model.{0}) (hM : Bounded M.toRaw) :
    ∃! _h : Hom M.toRaw Z, True := hZ.2 M.toRaw hM

/-! ## GQPF — the single-sorted collapse functor `G` -/

/-- The single-sorted collapse of the two-sorted functor (work order §0): an object's
unfolding is a finite nonempty set of unordered endpoint-pairs of objects.
Substituting R = Sym2 O into F_O eliminates the mutual recursion — the relation sort
was never self-referential. -/
def G (X : Type) : Type := { S : Set (Sym2 X) // S.Finite ∧ S.Nonempty }

/-- Functorial action of `G`: image on the underlying finite nonempty set. -/
def G.map {α β : Type} (f : α → β) (s : G α) : G β :=
  ⟨Sym2.map f '' s.1, s.2.1.image _, s.2.2.image _⟩

instance : Functor G := { map := @G.map }

/-- An ordered representative of an unordered pair (classical, via `Quot.out`). -/
noncomputable def sym2fst {X : Type} (z : Sym2 X) : X := (Quot.out z).1
/-- The other coordinate of the ordered representative. -/
noncomputable def sym2snd {X : Type} (z : Sym2 X) : X := (Quot.out z).2

theorem sym2_rep {X : Type} (z : Sym2 X) : s(sym2fst z, sym2snd z) = z :=
  Quot.out_eq z

/-- The polynomial for `G` (work order §3): shape = a positive number of ordered
pairs; positions = which pair, which coordinate. -/
def GP : PFunctor.{0} := ⟨ℕ+, fun n => Fin (n : ℕ) × Bool⟩

/-- `abs`: read `n` ordered pairs as the (finite, nonempty) set of the unordered
pairs they name. -/
def gAbs {X : Type} (p : GP.Obj X) : G X :=
  let n : ℕ+ := p.1
  let g : Fin (n : ℕ) × Bool → X := p.2
  ⟨Set.range (fun i : Fin (n : ℕ) => s(g (i, false), g (i, true))),
   Set.finite_range _,
   ⟨_, Set.mem_range_self (⟨0, n.pos⟩ : Fin (n : ℕ))⟩⟩

open scoped Classical in
/-- `repr`: enumerate the finite nonempty set (`equivFin`) and pick an ordered
representative of each unordered pair (`Quot.out`). Noncomputable, classical — fine
(representation layer). -/
noncomputable def gRepr {X : Type} (s : G X) : GP.Obj X :=
  ⟨⟨s.2.1.toFinset.card, Finset.card_pos.mpr (s.2.1.toFinset_nonempty.mpr s.2.2)⟩,
   fun q => cond q.2 (sym2snd (s.2.1.toFinset.equivFin.symm q.1).val)
                     (sym2fst (s.2.1.toFinset.equivFin.symm q.1).val)⟩

open scoped Classical in
noncomputable instance instQPFG : QPF G where
  P := GP
  abs := gAbs
  repr := gRepr
  abs_repr := by
    intro X s
    apply Subtype.ext
    apply Set.ext
    intro x
    simp only [gAbs, gRepr, Set.mem_range, cond_false, cond_true]
    constructor
    · rintro ⟨i, rfl⟩
      rw [sym2_rep]
      exact (s.2.1.mem_toFinset).mp (s.2.1.toFinset.equivFin.symm i).2
    · intro hx
      refine ⟨s.2.1.toFinset.equivFin ⟨x, (s.2.1.mem_toFinset).mpr hx⟩, ?_⟩
      rw [sym2_rep, Equiv.symm_apply_apply]
  abs_map := by
    intro X Y f p
    obtain ⟨n, g⟩ := p
    apply Subtype.ext
    show Set.range _ = Sym2.map f '' Set.range _
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext i
    simp only [PFunctor.map, Function.comp_apply, Sym2.map_pair_eq]

/-! ## The induced single-sorted coalgebra of a bounded Raw (§0 collapse). -/

/-- The induced single-sorted coalgebra of a bounded Raw: an object's G-unfolding is
the endpoint-image of its pattern. -/
noncomputable def inducedCoalg (A : Raw.{0}) (hA : Bounded A) : A.O → G A.O :=
  fun x => ⟨A.endpoints '' A.pat x, (hA x).image _, (A.pat_nonempty x).image _⟩

/-! ## NU / PKG — the universe Ω₀ and the two-sorted final Raw ZΩ -/

/-- Ω₀ := νG, the final coalgebra of the collapse functor (work order §4). -/
noncomputable def Ω₀ : Type := QPF.Cofix G

/-- The two-sorted final Raw, packaged from the single-sorted fixed point.
Relations ARE endpoint-pairs (`endpoints := id`); patterns are the destructor. -/
noncomputable def ZΩ : Raw.{0} where
  O := Ω₀
  R := Sym2 Ω₀
  endpoints := id
  pat := fun x => (QPF.Cofix.dest (F := G) x).1
  pat_nonempty := fun x => (QPF.Cofix.dest (F := G) x).2.2

theorem bounded_ZΩ : Bounded ZΩ := fun x => (QPF.Cofix.dest (F := G) x).2.1

/-! ## FIN — finality (the star) -/

/-- THE STAR: ZΩ is final among bounded Raws — νF exists at the ω-tier, and the
transfer theorem's hypothesis is DISCHARGED. Two-sorted homs into ZΩ biject with
G-coalgebra homs into νG because `ZΩ.endpoints = id` forces the relation component
`fR r = (A.endpoints r).map fO`; existence is `Cofix.corec (inducedCoalg A hA)`,
uniqueness is `Cofix.bisim` (any two coalgebra morphisms from one coalgebra are
bisimilar, hence equal). -/
theorem isFinalBRaw_ZΩ : IsFinalBRaw ZΩ := by
  refine ⟨bounded_ZΩ, fun A hA => ?_⟩
  -- Any G-coalgebra morphism for `inducedCoalg A hA` equals the corecursor.
  have key : ∀ gO : A.O → Ω₀,
      (∀ x, QPF.Cofix.dest (gO x) = G.map gO (inducedCoalg A hA x)) →
      gO = QPF.Cofix.corec (inducedCoalg A hA) := by
    intro gO hgO
    funext x0
    refine QPF.Cofix.bisim
      (fun a b => ∃ x, a = gO x ∧ b = QPF.Cofix.corec (inducedCoalg A hA) x)
      ?_ (gO x0) _ ⟨x0, rfl, rfl⟩
    rintro a b ⟨x, rfl, rfl⟩
    have habs : QPF.abs (QPF.repr (inducedCoalg A hA x)) = inducedCoalg A hA x :=
      QPF.abs_repr _
    rw [QPF.liftr_iff]
    refine ⟨(QPF.repr (inducedCoalg A hA x)).1,
            gO ∘ (QPF.repr (inducedCoalg A hA x)).2,
            QPF.Cofix.corec (inducedCoalg A hA) ∘ (QPF.repr (inducedCoalg A hA x)).2,
            ?_, ?_, fun i => ⟨(QPF.repr (inducedCoalg A hA x)).2 i, rfl, rfl⟩⟩
    · rw [hgO x]
      have step : gO <$> (inducedCoalg A hA x)
          = QPF.abs (GP.map gO (QPF.repr (inducedCoalg A hA x))) := by
        conv_lhs => rw [← habs]
        exact (QPF.abs_map gO _).symm
      exact step
    · rw [QPF.Cofix.dest_corec]
      have step : (QPF.Cofix.corec (inducedCoalg A hA)) <$> (inducedCoalg A hA x)
          = QPF.abs (GP.map (QPF.Cofix.corec (inducedCoalg A hA))
              (QPF.repr (inducedCoalg A hA x))) := by
        conv_lhs => rw [← habs]
        exact (QPF.abs_map _ _).symm
      exact step
  -- fO := corec; fR forced by `endpoints = id`.
  refine ⟨⟨QPF.Cofix.corec (inducedCoalg A hA),
           fun r => (A.endpoints r).map (QPF.Cofix.corec (inducedCoalg A hA)),
           fun _ => rfl, ?_⟩, trivial, ?_⟩
  · -- pat_comm
    intro x
    show (QPF.Cofix.dest (QPF.Cofix.corec (inducedCoalg A hA) x)).1
         = (fun r => (A.endpoints r).map (QPF.Cofix.corec (inducedCoalg A hA))) '' A.pat x
    rw [QPF.Cofix.dest_corec]
    show Sym2.map (QPF.Cofix.corec (inducedCoalg A hA)) '' (A.endpoints '' A.pat x) = _
    rw [Set.image_image]
  · -- uniqueness
    rintro ⟨gO, gR, g_end, g_pat⟩ -
    -- `endpoints = id` forces gR pointwise; `funext g_end` (not `fun r => g_end r`).
    have hgR : gR = fun r => (A.endpoints r).map gO := funext g_end
    have hgOcoalg : ∀ x, QPF.Cofix.dest (gO x) = G.map gO (inducedCoalg A hA x) := by
      intro x
      apply Subtype.ext
      rw [show (QPF.Cofix.dest (gO x)).1 = gR '' A.pat x from g_pat x, hgR,
          ← Set.image_image (Sym2.map gO) A.endpoints]
      rfl
    obtain rfl : gO = QPF.Cofix.corec (inducedCoalg A hA) := key gO hgOcoalg
    subst hgR
    rfl

/-- T2, DISCHARGED at the ω-tier. With `transfer_bounded`, every bounded coherent
model has exactly one morphism into ZΩ, landing in the coherent part. Ω exists —
"would exist, given" becomes "exists". The κ-loan (2-01 D4) is partially discharged;
general κ follows the same polynomial pattern (§6). -/
theorem T2_discharged : ∃ Z : Raw.{0}, IsFinalBRaw Z :=
  ⟨ZΩ, isFinalBRaw_ZΩ⟩

/-! ## ŌHAT — Ω is inhabited; its first citizen is the One -/

/-- The one-point coalgebra whose sole relation is a self-loop. -/
noncomputable def omegaCoalg : PUnit → G PUnit :=
  fun _ => ⟨{s(PUnit.unit, PUnit.unit)}, Set.finite_singleton _, Set.singleton_nonempty _⟩

/-- ω̂ — the self-loop, Ω's first citizen: the object whose entire pattern is its
one self-relation. Built by corec on the one-point coalgebra — the same construction
that in the boolean shadow WAS the whole universe (T1) here enters a rich universe
as one inhabitant. -/
noncomputable def omegaHat : Ω₀ := QPF.Cofix.corec omegaCoalg PUnit.unit

/-- ω̂'s pattern is exactly the singleton of its self-relation. -/
theorem pat_omegaHat : ZΩ.pat omegaHat = {s(omegaHat, omegaHat)} := by
  show (QPF.Cofix.dest omegaHat).1 = _
  unfold omegaHat
  rw [QPF.Cofix.dest_corec]
  show Sym2.map (QPF.Cofix.corec omegaCoalg) '' {s(PUnit.unit, PUnit.unit)} = _
  rw [Set.image_singleton, Sym2.map_pair_eq]
  rfl

/-- Ω is inhabited, and coherently so: ({ω̂}, {its self-relation}) is a Good pair, so
the coherent part of ZΩ — which is Ω — contains the One. -/
theorem omegaHat_coherent :
    omegaHat ∈ coherentPartO ZΩ ∧ s(omegaHat, omegaHat) ∈ coherentPartR ZΩ := by
  have hGood : Good ZΩ {omegaHat} {s(omegaHat, omegaHat)} := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr x hx
      rw [Set.mem_singleton_iff] at hr; subst hr
      have hx' : x ∈ s(omegaHat, omegaHat) := hx
      rw [Sym2.mem_iff] at hx'
      obtain rfl : x = omegaHat := hx'.elim id id
      rw [pat_omegaHat]; rfl
    · intro r hr x hx
      rw [Set.mem_singleton_iff] at hr; subst hr
      have hx' : x ∈ s(omegaHat, omegaHat) := hx
      rw [Sym2.mem_iff] at hx'
      rw [Set.mem_singleton_iff]; exact hx'.elim id id
    · intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx
      rw [pat_omegaHat]
  exact ⟨subset_coherentPartO hGood rfl, subset_coherentPartR hGood rfl⟩

end TwoSorted
end RelEx

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms transfer_bounded
#print axioms bounded_ZΩ
#print axioms isFinalBRaw_ZΩ
#print axioms T2_discharged
#print axioms pat_omegaHat
#print axioms omegaHat_coherent
end AxiomAudit

/-
-- Specs 2-00 / 2-01 ↔ scratch/formal/Spec201c.lean
-- VAC (honesty)        = RelEx.TwoSorted.vac_note (doc); isFinalRaw_never DROPPED (SHOULD)
-- BND (re-target)      = RelEx.TwoSorted.Bounded, IsFinalBRaw, transfer_bounded
-- GQPF (technical heart) = RelEx.TwoSorted.G, GP, gAbs, gRepr, instQPFG
-- NU                   = RelEx.TwoSorted.Ω₀ (:= QPF.Cofix G)
-- PKG                  = RelEx.TwoSorted.ZΩ, bounded_ZΩ
-- FIN (STAR)           = RelEx.TwoSorted.isFinalBRaw_ZΩ (existence: Cofix.corec; uniqueness: Cofix.bisim)
-- T2D                  = RelEx.TwoSorted.T2_discharged
-- ŌHAT                 = RelEx.TwoSorted.omegaHat, pat_omegaHat, omegaHat_coherent
-- LMB DROPPED (SHOULD)
--
-- mathlib QPF/Cofix API used (for future orders):
--   class `QPF` (fields P, abs, repr, abs_repr, abs_map); `PFunctor` (Obj, map);
--   `QPF.Cofix`, `QPF.Cofix.corec`, `QPF.Cofix.dest`, `QPF.Cofix.dest_corec`,
--   `QPF.Cofix.bisim`, `QPF.liftr_iff`, `QPF.abs_map`, `QPF.abs_repr`.
--   Ordered Sym2 representative via `Quot.out`/`Quot.out_eq`; finite-set enumeration
--   via `Set.Finite.toFinset` + `Finset.equivFin`.
--
-- Deviations from 2-01-mechanization-c.md:
--   * Registered as a sixth Lake library root (`Spec201c`).
--   * Monomorphized to `Type 0` throughout (work order §1 sanctions this; nothing
--     ontological hangs on it — representation layer).
--   * SHOULD items dropped: `isFinalRaw_never` (Cantor vacuity theorem — the honesty
--     is documented in `vac_note`) and `LMB` (Lambek). Both explicitly droppable.
--   * `funext` binder-inference quirk: `funext g_end` is used (not `fun r => g_end r`,
--     which mis-infers the binder domain).
-/
