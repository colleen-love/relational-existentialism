/-
Spec 2.4c — The construction: νHC, the corrected universe Ω_C, and its finality (Stages 2–3).

Normative source: `series-2/2-4.md` §4 (construction), §2 (Ω_C := greatest coherent
subcoalgebra), and the work order `2-4-mechanization-a.md` Stages 2–3. Continues `Spec204b.lean`
(the univariate reduction `HC`). Specs win.

This file discharges the construction that Spec204b flagged as the remaining boundary. The
technical heart is `instQPFHC` — a `QPF` instance for `HC X = Sym2(P⁺f(X) ⊕ X)` — built directly
(the analogue of Spec201c's `instQPFG`, here over a polynomial whose ordered representative pairs
two heterogeneous "sides", each a finite-nonempty set or a single element). With it,
`Ω_R := QPF.Cofix HC` and `Ω_O := P⁺f(Ω_R)` give the corrected universe, packaged as a two-sorted
`RawC` (`ZΩC`) that is FINAL among bounded corrected coalgebras (`isFinalBRawC`) — T2 discharged
for the corrected functor at the ω-tier.

File naming/numbering follows Spec204/Spec204b (see the Spec204 header note on the order's
`2.5`/`Spec205` off-by-one, resolved spec-first).
-/
import Spec204b
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## The QPF for HC (the technical heart, 2.4 §4)

`HC X = Sym2(P⁺f(X) ⊕ X)`. Its polynomial `HP`: an ordered pair of "sides", each side either a
positive count (a finite nonempty set) or a single element; positions are the `X`'s across both
sides. `abs` reads the ordered pair as an unordered pair (Sym2); `repr` picks an ordered
representative (`Quot.out`) and enumerates each set side (`toFinset`/`equivFin`). Two layers of
quotient (outer `Sym2`, inner `P⁺f`) absorbed by `abs`/`repr`, as in Spec201c. -/

/-- A side shape: a positive count (finite nonempty set) or a single (Unit). -/
def SideA : Type := ℕ+ ⊕ Unit
/-- Side positions: `Fin n` for a set of size `n`, `Unit` for a single. -/
abbrev SideB : SideA → Type
  | Sum.inl n => Fin (n : ℕ)
  | Sum.inr _ => Unit

/-- The polynomial for `HC`: an ordered pair of sides; positions across both. -/
def HP : PFunctor.{0} := ⟨SideA × SideA, fun a => SideB a.1 ⊕ SideB a.2⟩

/-- Reconstruct one side from shape+positions. -/
noncomputable def sideAbs {X : Type} : (s : SideA) → (SideB s → X) → (PfNe X ⊕ X)
  | Sum.inl n, g => Sum.inl ⟨Set.range g, Set.finite_range _, ⟨g ⟨0, n.pos⟩, Set.mem_range_self _⟩⟩
  | Sum.inr _, g => Sum.inr (g ())

/-- `abs`: an ordered pair of sides as the unordered endpoint pair. -/
noncomputable def hAbs {X : Type} (p : HP.Obj X) : HC X :=
  s(sideAbs p.1.1 (fun b => p.2 (Sum.inl b)), sideAbs p.1.2 (fun b => p.2 (Sum.inr b)))

open scoped Classical in
/-- Represent one side (enumerate a set via `toFinset`/`equivFin`; a single is trivial). -/
noncomputable def sideRepr {X : Type} : (PfNe X ⊕ X) → Σ s : SideA, (SideB s → X)
  | Sum.inl S => ⟨Sum.inl ⟨S.2.1.toFinset.card,
      Finset.card_pos.mpr (S.2.1.toFinset_nonempty.mpr S.2.2)⟩,
      fun i => (S.2.1.toFinset.equivFin.symm i).val⟩
  | Sum.inr x => ⟨Sum.inr (), fun _ => x⟩

open scoped Classical in
/-- `repr`: ordered representative of the unordered pair (`Quot.out`), each side represented. -/
noncomputable def hRepr {X : Type} (z : HC X) : HP.Obj X :=
  ⟨((sideRepr (Quot.out z).1).1, (sideRepr (Quot.out z).2).1),
   Sum.elim (sideRepr (Quot.out z).1).2 (sideRepr (Quot.out z).2).2⟩

/-- Side reconstruction — the crux (mirrors Spec201c's set-reconstruction): representing then
rebuilding a side is the identity. -/
theorem sideAbs_sideRepr {X : Type} (u : PfNe X ⊕ X) :
    sideAbs (sideRepr u).1 (sideRepr u).2 = u := by
  classical
  rcases u with S | x
  · apply congrArg Sum.inl
    apply Subtype.ext
    show Set.range (fun i => (S.2.1.toFinset.equivFin.symm i).val) = S.1
    apply Set.ext
    intro y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.2.1.mem_toFinset).mp (S.2.1.toFinset.equivFin.symm i).2
    · intro hy
      exact ⟨S.2.1.toFinset.equivFin ⟨y, (S.2.1.mem_toFinset).mpr hy⟩, by
        rw [Equiv.symm_apply_apply]⟩
  · rfl

/-- Side naturality: `sideAbs` commutes with the functorial action. -/
theorem sideAbs_map {X Y : Type} (f : X → Y) (s : SideA) (h : SideB s → X) :
    sideAbs s (fun b => f (h b)) =
      Sum.map (fun S => (⟨f '' S.1, S.2.1.image _, S.2.2.image _⟩ : PfNe Y)) f (sideAbs s h) := by
  rcases s with n | u
  · apply congrArg Sum.inl
    apply Subtype.ext
    show Set.range (fun b => f (h b)) = f '' Set.range h
    exact Set.range_comp f h
  · rfl

open scoped Classical in
/-- The QPF instance for `HC` — the technical heart of the corrected construction. -/
noncomputable instance instQPFHC : QPF HC where
  P := HP
  abs := hAbs
  repr := hRepr
  abs_repr := by
    intro X z
    show hAbs (hRepr z) = z
    have h1 : sideAbs (sideRepr (Quot.out z).1).1 (sideRepr (Quot.out z).1).2 = (Quot.out z).1 :=
      sideAbs_sideRepr _
    have h2 : sideAbs (sideRepr (Quot.out z).2).1 (sideRepr (Quot.out z).2).2 = (Quot.out z).2 :=
      sideAbs_sideRepr _
    show s(sideAbs (sideRepr (Quot.out z).1).1 (fun b => Sum.elim (sideRepr (Quot.out z).1).2
            (sideRepr (Quot.out z).2).2 (Sum.inl b)),
          sideAbs (sideRepr (Quot.out z).2).1 (fun b => Sum.elim (sideRepr (Quot.out z).1).2
            (sideRepr (Quot.out z).2).2 (Sum.inr b))) = z
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [h1, h2]
    show Quot.mk _ ((Quot.out z).1, (Quot.out z).2) = z
    rw [Prod.mk.eta, Quot.out_eq]
  abs_map := by
    intro X Y f p
    obtain ⟨⟨s1, s2⟩, g⟩ := p
    show hAbs ⟨(s1, s2), fun pos => f (g pos)⟩ = HC.map f (hAbs ⟨(s1, s2), g⟩)
    simp only [hAbs, HC.map, Sym2.map_pair_eq]
    rw [sideAbs_map f s1 (fun b => g (Sum.inl b)), sideAbs_map f s2 (fun b => g (Sum.inr b))]

/-! ## Ω_C — the corrected universe (2.4 §4, Stage 3)

`Ω_R := νHC` (the relation sort), `Ω_O := P⁺f(Ω_R)` (the object sort), packaged as a two-sorted
`RawC` whose relation-endpoints are the fixpoint destructor and whose object-patterns are the
underlying finite sets. -/

/-- The relation sort of the corrected universe: `Ω_R := νHC`. -/
noncomputable def ΩR : Type := QPF.Cofix HC

/-- The object sort: finite nonempty patterns of relations, `Ω_O := P⁺f(Ω_R)`. -/
abbrev ΩO : Type := PfNe ΩR

/-- The corrected universe, packaged as a two-sorted `RawC`. Relations ARE fixpoint points; their
endpoints are the destructor `HC ΩR = Sym2(Ω_O ⊕ Ω_R)`; an object IS its pattern. -/
noncomputable def ZΩC : RawC where
  O := ΩO
  R := ΩR
  endpoints := fun r => QPF.Cofix.dest (F := HC) r
  pat := fun x => x.1
  pat_nonempty := fun x => x.2.2

/-! ## Finality among bounded corrected coalgebras (Stage 3, T2-C) -/

/-- A corrected `RawC` is bounded when every pattern is finite (the ω-tier). -/
def BoundedC (A : RawC) : Prop := ∀ x, (A.pat x).Finite

theorem bounded_ZΩC : BoundedC ZΩC := fun x => x.2.1

/-- Finality among bounded corrected coalgebras — the target `transfer` needs. -/
def IsFinalBRawC (Z : RawC) : Prop :=
  BoundedC Z ∧ ∀ A : RawC, BoundedC A → ∃! _h : HomC A Z, True

/-- The HC-coalgebra induced by a bounded corrected `RawC`: a relation's `HC`-unfolding maps each
object endpoint to its (finite nonempty) pattern and keeps relation endpoints. -/
noncomputable def inducedCoalgC (A : RawC) (hA : BoundedC A) : A.R → HC A.R :=
  fun r => Sym2.map (Sum.map (fun y => (⟨A.pat y, hA y, A.pat_nonempty y⟩ : PfNe A.R)) id)
    (A.endpoints r)

/-- The relation-map into `Ω_R`: corecursion on the induced coalgebra. -/
noncomputable def fRC (A : RawC) (hA : BoundedC A) : A.R → ΩR :=
  QPF.Cofix.corec (inducedCoalgC A hA)

/-- The object-map into `Ω_O`: the image of the pattern under `fRC` (finite nonempty). -/
noncomputable def fOC (A : RawC) (hA : BoundedC A) : A.O → ΩO :=
  fun x => ⟨fRC A hA '' A.pat x, (hA x).image _, (A.pat_nonempty x).image _⟩

/-- THE STAR — `ZΩC` is final among bounded corrected coalgebras: νF_C exists at the ω-tier and
T2 is discharged for the corrected functor. `fRC` corecurses into `Ω_R`; `fOC` sends an object to
the `fRC`-image of its pattern; `end_comm` is `dest_corec` + `Sym2`/`Sum` naturality; uniqueness
is `Cofix.bisim` (any two coalgebra morphisms are bisimilar, hence equal) combined with the fact
that `pat_comm` forces the object map to be the pattern-image of the relation map. -/
theorem isFinalBRawC : IsFinalBRawC ZΩC := by
  refine ⟨bounded_ZΩC, fun A hA => ?_⟩
  -- Any HC-coalgebra morphism for `inducedCoalgC A hA` equals the corecursor.
  have key : ∀ gR : A.R → ΩR,
      (∀ r, QPF.Cofix.dest (gR r) = HC.map gR (inducedCoalgC A hA r)) →
      gR = fRC A hA := by
    intro gR hgR
    funext r0
    refine QPF.Cofix.bisim
      (fun a b => ∃ r, a = gR r ∧ b = fRC A hA r) ?_ (gR r0) _ ⟨r0, rfl, rfl⟩
    rintro a b ⟨r, rfl, rfl⟩
    have habs : QPF.abs (QPF.repr (inducedCoalgC A hA r)) = inducedCoalgC A hA r :=
      QPF.abs_repr _
    rw [QPF.liftr_iff]
    refine ⟨(QPF.repr (inducedCoalgC A hA r)).1,
            gR ∘ (QPF.repr (inducedCoalgC A hA r)).2,
            fRC A hA ∘ (QPF.repr (inducedCoalgC A hA r)).2,
            ?_, ?_, fun i => ⟨(QPF.repr (inducedCoalgC A hA r)).2 i, rfl, rfl⟩⟩
    · rw [hgR r]
      conv_lhs => rw [← habs]
      exact (QPF.abs_map (F := HC) gR _).symm
    · rw [fRC, QPF.Cofix.dest_corec]
      conv_lhs => rw [← habs]
      exact (QPF.abs_map (F := HC) _ _).symm
  refine ⟨⟨fOC A hA, fRC A hA, ?_, ?_⟩, trivial, ?_⟩
  · -- end_comm : ZΩC.endpoints (fRC r) = (A.endpoints r).map (Sum.map fOC fRC)
    intro r
    show QPF.Cofix.dest (fRC A hA r)
        = Sym2.map (Sum.map (fOC A hA) (fRC A hA)) (A.endpoints r)
    rw [fRC, QPF.Cofix.dest_corec]
    show HC.map (QPF.Cofix.corec (inducedCoalgC A hA)) (inducedCoalgC A hA r) = _
    rw [inducedCoalgC, HC.map]
    show Sym2.map _ (Sym2.map _ (A.endpoints r)) = Sym2.map _ (A.endpoints r)
    rw [Sym2.map_map]
    congr 1
    funext z
    rcases z with y | s
    · show Sum.inl _ = Sum.map (fOC A hA) (fRC A hA) (Sum.inl y)
      rfl
    · rfl
  · -- pat_comm : ZΩC.pat (fOC x) = fRC '' A.pat x
    intro x
    show (fOC A hA x).1 = fRC A hA '' A.pat x
    rfl
  · -- uniqueness
    rintro ⟨gO, gR, g_end, g_pat⟩ -
    have hgRcoalg : ∀ r, QPF.Cofix.dest (gR r) = HC.map gR (inducedCoalgC A hA r) := by
      intro r
      have he := g_end r
      -- he : ZΩC.endpoints (gR r) = (A.endpoints r).map (Sum.map gO gR)
      show QPF.Cofix.dest (gR r) = _
      rw [show QPF.Cofix.dest (gR r) = ZΩC.endpoints (gR r) from rfl, he]
      rw [inducedCoalgC, HC.map, Sym2.map_map]
      congr 1
      funext z
      rcases z with y | s
      · -- object endpoint: gO y = image of pat y under gR (from pat_comm)
        have hgy : gO y =
            (⟨gR '' A.pat y, (hA y).image _, (A.pat_nonempty y).image _⟩ : PfNe ΩR) := by
          apply Subtype.ext
          exact g_pat y
        show Sum.inl (gO y) = Sum.inl _
        rw [hgy]
      · rfl
    obtain rfl : gR = fRC A hA := key gR hgRcoalg
    -- gO forced by pat_comm
    have hgO : gO = fOC A hA := by
      funext x
      apply Subtype.ext
      exact g_pat x
    subst hgO
    rfl

/-- T2-C — DISCHARGED at the ω-tier for the corrected functor. Every bounded corrected coalgebra
has exactly one morphism into `ZΩC`. Ω exists for the corrected signature: "would exist, given"
becomes "exists". -/
theorem T2C_discharged : ∃ Z : RawC, IsFinalBRawC Z :=
  ⟨ZΩC, isFinalBRawC⟩

/-! ## Lambek, ω̂₂, and FP5 — the anti-Mirror against the constructed universe (Stages 3–4)

Lambek: `QPF.Cofix.dest` (i.e. `ZΩC.endpoints`) is the structure iso `Ω_R ≅ HC Ω_R = Sym2(Ω_O ⊕
Ω_R)`, inherited from `QPF.Cofix` (`dest`/`corec` with `dest_corec`). The two coherent seeds close
into distinct elements of the constructed universe, separated at depth 1 — the anti-Mirror. -/

theorem bounded_seed2 : BoundedC seed2 := fun _ => Set.finite_singleton _
theorem bounded_seed3 : BoundedC seed3 := fun _ => Set.finite_singleton _

/-- The bearing seed closed into `Ω_R`. -/
noncomputable def elt2 : ΩR := fRC seed2 bounded_seed2 PUnit.unit
/-- The higher seed closed into `Ω_R` — the self-witnessing loop. -/
noncomputable def elt3 : ΩR := fRC seed3 bounded_seed3 PUnit.unit

/-- **ω̂₂** — the corrected universe's first citizen: the self-witnessing loop as an OBJECT (the
`fRC`-image of seed 3's pattern). The pre-correction `omegaHat` (Spec201c) named the wrong citizen
— the bare self-loop, incoherent under the K-triple (`seed1_incoherent`, Spec204); ω̂₂ is the One
that turns upon its turning (retiring `omegaHat_coherent`; 2.4 O-2-5-3). -/
noncomputable def omegaHat2 : ΩO := fOC seed3 bounded_seed3 PUnit.unit

/-- `elt3`'s unfolding: both endpoints are the loop itself — pure higher-order, no object endpoint
(the higher seed `s(r̂,r̂)`, closed). -/
theorem dest_elt3 : ZΩC.endpoints elt3 = s(Sum.inr elt3, Sum.inr elt3) := by
  show QPF.Cofix.dest elt3 = _
  rw [elt3, fRC, QPF.Cofix.dest_corec]
  show HC.map (QPF.Cofix.corec (inducedCoalgC seed3 bounded_seed3))
      (inducedCoalgC seed3 bounded_seed3 PUnit.unit) = _
  rw [inducedCoalgC, show seed3.endpoints PUnit.unit = seedRR from rfl, seedRR,
      Sym2.map_pair_eq, HC.map, Sym2.map_pair_eq]
  rfl

/-- `elt2`'s unfolding carries an object endpoint (the bearing seed `s(⋆,r̂)`, closed). -/
theorem dest_elt2 :
    ZΩC.endpoints elt2 = s(Sum.inl (fOC seed2 bounded_seed2 PUnit.unit), Sum.inr elt2) := by
  show QPF.Cofix.dest elt2 = _
  rw [elt2, fRC, QPF.Cofix.dest_corec]
  show HC.map (QPF.Cofix.corec (inducedCoalgC seed2 bounded_seed2))
      (inducedCoalgC seed2 bounded_seed2 PUnit.unit) = _
  rw [inducedCoalgC, show seed2.endpoints PUnit.unit = seedOR from rfl, seedOR,
      Sym2.map_pair_eq, HC.map, Sym2.map_pair_eq]
  rfl

/-- Depth-1 anti-Mirror invariant on `Ω_R`: the relation's unfolding carries an object endpoint. -/
def HasObjEndpointΩ (r : ΩR) : Prop := ∃ o : ΩO, Sum.inl o ∈ ZΩC.endpoints r

/-- FP5 — THE ANTI-MIRROR, against the constructed universe. Two elements of `Ω_R` (the closed
coherent seeds) are separated at depth 1 by sort-profile: `elt2` (the bearing) carries an object
endpoint, `elt3` (the loop) does not — so they are non-bisimilar, hence DISTINCT in the final
coalgebra. The theorem the collapsed universe could not have, now against `Ω` proper: **the
corrected universe is many.** -/
theorem anti_mirror_C : HasObjEndpointΩ elt2 ∧ ¬ HasObjEndpointΩ elt3 := by
  constructor
  · exact ⟨fOC seed2 bounded_seed2 PUnit.unit, by rw [dest_elt2]; exact Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · rintro ⟨o, ho⟩
    rw [dest_elt3, Sym2.mem_iff] at ho
    rcases ho with h | h <;> simp at h

/-- The two closed seeds are distinct elements of the constructed universe (`Ω_R`) — the plurality
the Mirror forbade, read off the anti-Mirror invariant. -/
theorem elt2_ne_elt3 : elt2 ≠ elt3 := by
  intro h
  have := anti_mirror_C
  rw [h] at this
  exact this.2 this.1

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms instQPFHC
#print axioms isFinalBRawC
#print axioms T2C_discharged
#print axioms dest_elt3
#print axioms dest_elt2
#print axioms anti_mirror_C
#print axioms elt2_ne_elt3
end AxiomAudit
