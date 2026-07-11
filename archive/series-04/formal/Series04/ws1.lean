/-
`series-04/formal/ws1.lean`

WS1 — **The world and its faces.** Series 04, blocking workstream.

This file is SELF-CONTAINED: it carries its own copy of the groundless carrier
(the terminal coalgebra of the κ-bounded powerset functor `P_κ`, built as the
`Cofix` of a QPF), reproduced from the Series 03 development (archived under
`archive/formal/ws1.lean`, `ws2.lean`) so that Series 04 depends on nothing outside
`series-04/formal/`. Every carrier lemma below is a faithful transcription of an
already machine-checked, axiom-clean Series 03 proof; the *new* Series 04 content is
the **face** layer (§ "The face" onward): the part of a source turned toward a
successor, defined from the successor relation alone (design candidate R2).

Design doc: `series-04/spec/ws01-design.md`. Deliverables here:
`RoutedThrough`, `face`, `face_sub_reach`, `ws1_face_forced`,
`ws1_weak_pullback_inherited`, `ws1_omega_face`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext`/`Classical.choice`/
`Quot.sound` (verify with `#print axioms ws1_weak_pullback_inherited`).
-/
import Mathlib

universe u

namespace Series04.WS1

open Cardinal QPF Functor

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (carrier foundation, from Series 03 WS1) -/

/-- `PkObj κ X` — the subsets of `X` of cardinality `< κ`. -/
def PkObj (κ : Cardinal.{u}) (X : Type u) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}

/-- The functorial action of `P_κ` on maps. -/
def PkMap (κ : Cardinal.{u}) {X Y : Type u} (f : X → Y) (s : PkObj κ X) : PkObj κ Y :=
  ⟨f '' s.1, lt_of_le_of_lt Cardinal.mk_image_le s.2⟩

@[simp] lemma PkMap_val {X Y : Type u} (f : X → Y) (s : PkObj κ X) :
    (PkMap κ f s).1 = f '' s.1 := rfl

@[simp] lemma PkMap_id {X : Type u} (s : PkObj κ X) : PkMap κ (id : X → X) s = s := by
  apply Subtype.ext; simp [PkMap]

lemma PkMap_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) (s : PkObj κ X) :
    PkMap κ (g ∘ f) s = PkMap κ g (PkMap κ f s) := by
  apply Subtype.ext
  show (g ∘ f) '' s.1 = g '' (f '' s.1)
  exact Set.image_comp g f s.1

lemma mk_empty_lt {α : Type u} (hinf : ℵ₀ ≤ κ) : Cardinal.mk (↥(∅ : Set α)) < κ := by
  haveI : IsEmpty (↥(∅ : Set α)) := ⟨fun x => (Set.mem_empty_iff_false _).mp x.2⟩
  rw [Cardinal.mk_eq_zero]
  exact lt_of_lt_of_le Cardinal.aleph0_pos hinf

lemma mk_singleton_lt {α : Type u} (hinf : ℵ₀ ≤ κ) (a : α) :
    Cardinal.mk (↥({a} : Set α)) < κ := by
  rw [Cardinal.mk_singleton]
  exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf

/-! ## Coalgebras and terminality -/

/-- A `P_κ`-coalgebra: a carrier `X` with a structure map `X → P_κ X`. -/
structure Coalg (κ : Cardinal.{u}) where
  X : Type u
  str : X → PkObj κ X

/-- `U` is **terminal**: from every coalgebra there is a unique coalgebra morphism. -/
def IsTerminalCoalg (U : Coalg κ) : Prop :=
  ∀ C : Coalg κ, ∃! h : C.X → U.X, ∀ x, U.str (h x) = PkMap κ h (C.str x)

lemma hom_unique {U : Coalg κ} (hU : IsTerminalCoalg U) (C : Coalg κ)
    {h₁ h₂ : C.X → U.X}
    (n₁ : ∀ x, U.str (h₁ x) = PkMap κ h₁ (C.str x))
    (n₂ : ∀ x, U.str (h₂ x) = PkMap κ h₂ (C.str x)) : h₁ = h₂ :=
  (hU C).unique n₁ n₂

lemma endo_eq_id {U : Coalg κ} (hU : IsTerminalCoalg U) (h : U.X → U.X)
    (hh : ∀ x, U.str (h x) = PkMap κ h (U.str x)) : h = id :=
  hom_unique hU U hh (fun x => by simp)

/-- Lambek's lemma: the structure map of a terminal coalgebra is a bijection. -/
theorem lambek {U : Coalg κ} (hU : IsTerminalCoalg U) : Function.Bijective U.str := by
  obtain ⟨g, hg, -⟩ := hU ⟨PkObj κ U.X, PkMap κ U.str⟩
  have hgU : (fun x => g (U.str x)) = id := by
    apply endo_eq_id hU
    intro x
    calc U.str ((fun x => g (U.str x)) x)
        = U.str (g (U.str x)) := rfl
      _ = PkMap κ g (PkMap κ U.str (U.str x)) := hg (U.str x)
      _ = PkMap κ (fun x => g (U.str x)) (U.str x) := (PkMap_comp g U.str (U.str x)).symm
  have left : Function.LeftInverse g U.str := fun x => congrFun hgU x
  have right : Function.RightInverse g U.str := by
    intro y
    calc U.str (g y)
        = PkMap κ g (PkMap κ U.str y) := hg y
      _ = PkMap κ (fun x => g (U.str x)) y := (PkMap_comp g U.str y).symm
      _ = PkMap κ id y := by rw [hgU]
      _ = y := PkMap_id y
  exact ⟨left.injective, right.surjective⟩

/-! ## Identity: bisimulation = equality -/

/-- An `F`-bisimulation on a coalgebra `C`. -/
structure Bisim (C : Coalg κ) (R : C.X → C.X → Prop) where
  ζ : {p : C.X × C.X // R p.1 p.2} → PkObj κ {p : C.X × C.X // R p.1 p.2}
  nat_fst : ∀ p, C.str p.1.1 = PkMap κ (fun q => q.1.1) (ζ p)
  nat_snd : ∀ p, C.str p.1.2 = PkMap κ (fun q => q.1.2) (ζ p)

/-- In a terminal coalgebra every bisimulation is contained in the diagonal. -/
theorem bisim_eq {U : Coalg κ} (hU : IsTerminalCoalg U)
    (R : U.X → U.X → Prop) (hR : Bisim U R) : ∀ x y, R x y → x = y := by
  intro x y hxy
  have h := hom_unique hU ⟨{p : U.X × U.X // R p.1 p.2}, hR.ζ⟩
    (h₁ := fun q => q.1.1) (h₂ := fun q => q.1.2) hR.nat_fst hR.nat_snd
  exact congrFun h ⟨(x, y), hxy⟩

/-! ## The canonical inhabitant Ω, and non-degeneracy witnesses -/

/-- Ω's defining coalgebra: the one-node self-loop `∗ ↦ {∗}`. -/
def omegaCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨PUnit, fun _ => ⟨{PUnit.unit}, mk_singleton_lt hinf _⟩⟩

/-- The one-node graph with the empty relation, `∗ ↦ ∅`. -/
def emptyCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨PUnit, fun _ => ⟨∅, mk_empty_lt hinf⟩⟩

/-! ## Existence of the carrier — PROVED via the QPF/`Cofix` route -/

section Existence
open Ordinal Set QPF Functor

/-- The polynomial functor of which `P_κ` is a quotient. -/
def PkP (κ : Cardinal.{u}) : PFunctor.{u} where
  A := κ.ord.toType
  B a := {b : κ.ord.toType // b < a}

def absPk {α : Type u} (p : (PkP κ).Obj α) : PkObj κ α :=
  ⟨Set.range p.2, lt_of_le_of_lt Cardinal.mk_range_le (card_typein_toType_lt κ p.1)⟩

noncomputable def reprPk {α : Type u} (s : PkObj κ α) :
    { p : (PkP κ).Obj α // Set.range p.2 = s.1 } := by
  have ho' : (Cardinal.mk (↥s.1)).ord < type (α := κ.ord.toType) (· < ·) := by
    rw [type_toType]; exact Cardinal.ord_lt_ord.mpr s.2
  set a : κ.ord.toType := enum (α := κ.ord.toType) (· < ·) ⟨(Cardinal.mk (↥s.1)).ord, ho'⟩ with ha
  have hcard : Cardinal.mk ((PkP κ).B a) = Cardinal.mk (↥s.1) := by
    have h1 : Cardinal.mk ((PkP κ).B a) = (typein (α := κ.ord.toType) (· < ·) a).card :=
      card_typein a
    rw [h1, ha, typein_enum, Cardinal.card_ord]
  let e : (PkP κ).B a ≃ ↥s.1 := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨⟨a, fun i => (e i : α)⟩, ?_⟩
  show Set.range (Subtype.val ∘ e) = s.1
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]

noncomputable instance qpfPk : QPF (PkObj κ) where
  map f s := PkMap κ f s
  P := PkP κ
  abs := absPk
  repr s := (reprPk s).1
  abs_repr s := by
    apply Subtype.ext
    show Set.range (reprPk s).1.2 = s.1
    exact (reprPk s).2
  abs_map f p := by
    apply Subtype.ext
    show Set.range (f ∘ p.2) = f '' Set.range p.2
    exact Set.range_comp f p.2

/-- **Existence of the groundless carrier — the WS1 obligation, DISCHARGED.** -/
theorem exists_terminal_coalg (κ : Cardinal.{u}) : ∃ U : Coalg κ, IsTerminalCoalg U := by
  refine ⟨⟨Cofix (PkObj κ), Cofix.dest⟩, ?_⟩
  intro C
  refine ⟨Cofix.corec C.str, fun x => Cofix.dest_corec C.str x, ?_⟩
  intro h hh
  funext x
  refine Cofix.bisim' (fun _ => True) h (Cofix.corec C.str) ?_ x trivial
  intro y _
  refine ⟨(QPF.repr (C.str y)).1,
          (fun i => h ((QPF.repr (C.str y)).2 i)),
          (fun i => Cofix.corec C.str ((QPF.repr (C.str y)).2 i)), ?_, ?_, ?_⟩
  · calc Cofix.dest (h y)
        = PkMap κ h (C.str y) := hh y
      _ = h <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]; rfl
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst, fun i => h ((QPF.repr (C.str y)).snd i)⟩ := by
            rw [← QPF.abs_map]; rfl
  · calc Cofix.dest (Cofix.corec C.str y)
        = Cofix.corec C.str <$> C.str y := Cofix.dest_corec C.str y
      _ = Cofix.corec C.str <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst,
            fun i => Cofix.corec C.str ((QPF.repr (C.str y)).snd i)⟩ := by rw [← QPF.abs_map]; rfl
  · intro i
    exact ⟨(QPF.repr (C.str y)).2 i, trivial, rfl, rfl⟩

end Existence

/-! ## The concrete carrier `νPk` (from Series 03 WS2) -/

/-- The concrete carrier: the final coalgebra of `P_κ` (`νP_κ`). -/
noncomputable def νPk (κ : Cardinal.{u}) : Coalg κ := ⟨Cofix (PkObj κ), Cofix.dest⟩

/-- Terminality of the concrete carrier `νPk`. -/
theorem νPk_terminal (κ : Cardinal.{u}) : IsTerminalCoalg (νPk κ) := by
  intro C
  refine ⟨Cofix.corec C.str, fun x => Cofix.dest_corec C.str x, ?_⟩
  intro h hh
  funext x
  refine Cofix.bisim' (fun _ => True) h (Cofix.corec C.str) ?_ x trivial
  intro y _
  refine ⟨(QPF.repr (C.str y)).1,
          (fun i => h ((QPF.repr (C.str y)).2 i)),
          (fun i => Cofix.corec C.str ((QPF.repr (C.str y)).2 i)), ?_, ?_, ?_⟩
  · calc Cofix.dest (h y)
        = PkMap κ h (C.str y) := hh y
      _ = h <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]; rfl
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst, fun i => h ((QPF.repr (C.str y)).snd i)⟩ := by
            rw [← QPF.abs_map]; rfl
  · calc Cofix.dest (Cofix.corec C.str y)
        = Cofix.corec C.str <$> C.str y := Cofix.dest_corec C.str y
      _ = Cofix.corec C.str <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst,
            fun i => Cofix.corec C.str ((QPF.repr (C.str y)).snd i)⟩ := by rw [← QPF.abs_map]; rfl
  · intro i
    exact ⟨(QPF.repr (C.str y)).2 i, trivial, rfl, rfl⟩

/-- Every bisimulation on `νPk` is contained in the diagonal. -/
theorem ws2_bisim_eq (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) :
    ∀ x y, R x y → x = y :=
  bisim_eq (νPk_terminal κ) R hR

/-! ## Weak-pullback preservation (Barr lifting), from Series 03 WS2 -/

/-- Relation composition. -/
def relComp {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop) : X → Z → Prop :=
  fun x z => ∃ y, R x y ∧ S y z

/-- Barr relation lifting of `P_κ`. -/
def PkRel {X Y : Type u} (R : X → Y → Prop) :
    PkObj κ X → PkObj κ Y → Prop := fun s t =>
  ∃ w : PkObj κ {p : X × Y // R p.1 p.2},
    PkMap κ (fun p => p.1.1) w = s ∧ PkMap κ (fun p => p.1.2) w = t

/-- **`P_κ` preserves weak pullbacks** (the substantive reflection-of-composition
direction). -/
theorem PkRel_le_comp {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : PkObj κ X) (u : PkObj κ Z) (h : PkRel (relComp R S) s u) :
    ∃ t, PkRel R s t ∧ PkRel S t u := by
  classical
  obtain ⟨w, hws, hwu⟩ := h
  refine ⟨PkMap κ (fun q => q.2.choose) w,
    ⟨PkMap κ (fun q => (⟨(q.1.1, q.2.choose), q.2.choose_spec.1⟩ :
        {p : X × Y // R p.1 p.2})) w, ?_, ?_⟩,
     PkMap κ (fun q => (⟨(q.2.choose, q.1.2), q.2.choose_spec.2⟩ :
        {p : Y × Z // S p.1 p.2})) w, ?_, ?_⟩
  · rw [← PkMap_comp]; exact hws
  · rw [← PkMap_comp]; rfl
  · rw [← PkMap_comp]; rfl
  · rw [← PkMap_comp]; exact hwu

/-- Weak-pullback preservation for `P_κ`, packaged as a predicate. -/
def PkPreservesWeakPullback (κ : Cardinal.{u}) : Prop :=
  ∀ {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : PkObj κ X) (u : PkObj κ Z),
    PkRel (relComp R S) s u → ∃ t, PkRel R s t ∧ PkRel S t u

theorem ws2_weak_pullback : PkPreservesWeakPullback κ :=
  fun R S s u h => PkRel_le_comp R S s u h

/-! ## Reachability (from Series 03 WS10/WS12) -/

/-- Reachability along the successor relation. -/
def Reaches (x y : (νPk κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ ((νPk κ).str a).1) x y

/-- The reachable set of a state. -/
def ReachSet (u : (νPk κ).X) : Set (νPk κ).X := {y | Reaches u y}

lemma Reaches.refl' (x : (νPk κ).X) : Reaches x x := Relation.ReflTransGen.refl

lemma Reaches.step {x y : (νPk κ).X} (h : y ∈ ((νPk κ).str x).1) : Reaches x y :=
  Relation.ReflTransGen.single h

lemma Reaches.trans' {x y z : (νPk κ).X} (h₁ : Reaches x y) (h₂ : Reaches y z) :
    Reaches x z := h₁.trans h₂

/-! ## The face — the new Series 04 content (design candidate R2)

When `x` relates to a successor `y`, the **face** `x↾(x,y)` is the part of `x`
turned toward `y`: the states reachable from `x` *through* the edge to `y`. It is
defined from the successor relation alone — no annotation, no imported data. This is
the R2 "derived intrinsic face" of `series-04/spec/ws01-design.md`. -/

/-- A path from `x` whose first step is the edge to `y`, then reaching `z`. -/
def RoutedThrough (x y z : (νPk κ).X) : Prop :=
  y ∈ ((νPk κ).str x).1 ∧ Reaches y z

/-- **The face**: the part of `x` reachable through its edge to successor `y`.
Forced by `str` alone. (When `y ∈ succ x`, the design's `∪ {y}` is subsumed: `y`
routes through itself via reflexivity — see `mem_face_self`.) -/
def face (x y : (νPk κ).X) : Set (νPk κ).X := {z | RoutedThrough x y z}

@[simp] lemma mem_face {x y z : (νPk κ).X} :
    z ∈ face x y ↔ y ∈ ((νPk κ).str x).1 ∧ Reaches y z := Iff.rfl

/-- When `y` is a genuine successor of `x`, `y` lies in its own face. -/
lemma mem_face_self {x y : (νPk κ).X} (hy : y ∈ ((νPk κ).str x).1) : y ∈ face x y :=
  ⟨hy, Reaches.refl' y⟩

/-- **The face is an internal sub-object**: it lies inside `x`'s reachable part. -/
theorem face_sub_reach (x y : (νPk κ).X) : face x y ⊆ ReachSet x := by
  rintro z ⟨hstep, hreach⟩
  exact (Reaches.step hstep).trans' hreach

/-- **D1 — the face is forced, not annotated.** `face` is literally a function of
the structure map: it is uniquely determined, so Series 04 *refines* the plain
carrier rather than adding data (the lossiness thesis, trivial form). -/
theorem ws1_face_forced :
    ∃! f : (νPk κ).X → (νPk κ).X → Set (νPk κ).X,
      ∀ x y, f x y = {z | y ∈ ((νPk κ).str x).1 ∧ Reaches y z} :=
  ⟨face, fun _ _ => rfl, fun g hg => by funext x y; rw [hg x y]; rfl⟩

/-- **D2 — the gate, inherited.** Because the face is a *derived operation* and does
not change the functor `P_κ`, weak-pullback preservation — the existential gate the
whole program is conditional on — is inherited verbatim from the functor, not
re-proved for a bespoke carrier. This is the design's central payoff: the risk that
kills programs (a bespoke functor failing the gate) does not arise. -/
theorem ws1_weak_pullback_inherited : PkPreservesWeakPullback κ := ws2_weak_pullback

/-! ## Ω recovered with its (improper) face -/

/-- The canonical self-relating point `Ω` inside `νPk`. -/
noncomputable def omegaState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (omegaCoalg hinf)).choose PUnit.unit

/-- Ω's structure is the self-singleton `{Ω}`. -/
theorem omega_selfsingleton (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (omegaState hinf)).1 = {omegaState hinf} := by
  have hnat := (νPk_terminal κ (omegaCoalg hinf)).choose_spec.1 PUnit.unit
  unfold omegaState
  rw [hnat]; simp [PkMap, omegaCoalg]

/-- Ω reaches only itself. -/
theorem reaches_omega (hinf : ℵ₀ ≤ κ) (z : (νPk κ).X) :
    Reaches (omegaState hinf) z ↔ z = omegaState hinf := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
        subst ih
        rw [omega_selfsingleton hinf] at hbc
        exact (Set.mem_singleton_iff.mp hbc).symm ▸ rfl
  · rintro rfl; exact Reaches.refl' _

/-- Ω's reachable set is exactly `{Ω}`. -/
theorem reachSet_omega (hinf : ℵ₀ ≤ κ) : ReachSet (omegaState hinf) = {omegaState hinf} := by
  ext z; simp only [ReachSet, Set.mem_setOf_eq, Set.mem_singleton_iff]; exact reaches_omega hinf z

/-- **D3 — Ω recovered with its face.** Ω's only successor is itself, so its
self-face is *all* of Ω: `Ω↾(Ω,Ω) = {Ω}`. This is the improper-face-on-the-diagonal
fact (the disarmed pole-coincidence): Ω is the sole point where the part-that-faces
equals the whole-faced. -/
theorem ws1_omega_face (hinf : ℵ₀ ≤ κ) :
    face (omegaState hinf) (omegaState hinf) = {omegaState hinf} := by
  ext z
  simp only [mem_face, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hz⟩; exact (reaches_omega hinf z).mp hz
  · rintro rfl
    refine ⟨?_, Reaches.refl' _⟩
    rw [omega_selfsingleton hinf]; rfl

end Series04.WS1
