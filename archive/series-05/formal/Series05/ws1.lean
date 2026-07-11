/-
`series-05/formal/ws1.lean`

WS1 — **The tower and its colimit.** Series 05, blocking workstream.

This file is SELF-CONTAINED (charter §1, `spec/readme.md`): it carries its own copy
of the Series 04 carrier machinery — the plain κ-bounded powerset carrier `νPk`
(from Series 04 `ws1`), the labelled carrier `νLk` and its composition `lcomp` (from
Series 04 `ws3`), and the carrier lower bound (from Series 04 `ws2`) — re-namespaced
`Series05.WS1`. Nothing is imported from `series-04/` or `archive/`.

The *new* Series 05 content (from `Level` onward) is the **directed tower** `Tower`,
its colimit carrier `Winf`, and the colimit gate `ws1_bisim_eq_colim`: the
existential obligation on which the whole program is conditional.

Design doc: `series-05/spec/ws01-design.md` (candidate C2, bound-relaxing inclusions).
Deliverables: `Level`, `Tower`, `TowerColimRel`, `Winf`, `toColim`, `ws1_colim_equiv`
(D1), `destInf`/`RelatesInf` + `ws1_bisim_eq_colim` (D2, the gate), `omegaInf` +
`ws1_omega_selfloop` + `ws1_local_bound` (D3).

Sorry-free; axiom-clean beyond Mathlib's standard `propext`/`Classical.choice`/
`Quot.sound`.
-/
import Mathlib

universe u w

namespace Series05.WS1

open Cardinal QPF Functor

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (transcribed Series 04 WS1) -/

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

/-! ## Coalgebras and terminality (transcribed) -/

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

/-! ## Identity: bisimulation = equality (transcribed) -/

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

/-- Ω's defining coalgebra: the one-node self-loop `∗ ↦ {∗}`. -/
def omegaCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨PUnit, fun _ => ⟨{PUnit.unit}, mk_singleton_lt hinf _⟩⟩

/-! ## Existence of the carrier — via the QPF/`Cofix` route (transcribed) -/

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

end Existence

/-- The concrete plain carrier: the final coalgebra of `P_κ` (`νP_κ`). -/
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

/-! ## Carrier lower bound (transcribed Series 04 WS2 `carrier_card_ge`) -/

/-- `κ ≤ #(νPk κ).X`: if the carrier were smaller than `κ` then Lambek would give
`X ≃ Set X`, contradicting Cantor. -/
theorem carrier_card_ge (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X := by
  by_contra hlt
  push_neg at hlt
  have hall : ∀ s : Set (νPk κ).X, Cardinal.mk (↥s) < κ :=
    fun s => lt_of_le_of_lt (Cardinal.mk_subtype_le (· ∈ s)) hlt
  have e1 : PkObj κ (νPk κ).X ≃ Set (νPk κ).X := Equiv.subtypeUnivEquiv hall
  have hbij : Function.Bijective (νPk κ).str := lambek (νPk_terminal κ)
  have hc : Cardinal.mk (νPk κ).X = 2 ^ Cardinal.mk (νPk κ).X :=
    calc Cardinal.mk (νPk κ).X
        = Cardinal.mk (PkObj κ (νPk κ).X) := Cardinal.mk_congr (Equiv.ofBijective _ hbij)
      _ = Cardinal.mk (Set (νPk κ).X) := Cardinal.mk_congr e1
      _ = 2 ^ Cardinal.mk (νPk κ).X := Cardinal.mk_set
  have hcantor := Cardinal.cantor (Cardinal.mk (νPk κ).X)
  rw [← hc] at hcantor
  exact lt_irrefl _ hcantor

/-! ## Reachability and the face (transcribed Series 04 WS1) -/

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

/-- A path from `x` whose first step is the edge to `y`, then reaching `z`. -/
def RoutedThrough (x y z : (νPk κ).X) : Prop :=
  y ∈ ((νPk κ).str x).1 ∧ Reaches y z

/-- **The face**: the part of `x` reachable through its edge to successor `y`. -/
def face (x y : (νPk κ).X) : Set (νPk κ).X := {z | RoutedThrough x y z}

@[simp] lemma mem_face {x y z : (νPk κ).X} :
    z ∈ face x y ↔ y ∈ ((νPk κ).str x).1 ∧ Reaches y z := Iff.rfl

lemma mem_face_self {x y : (νPk κ).X} (hy : y ∈ ((νPk κ).str x).1) : y ∈ face x y :=
  ⟨hy, Reaches.refl' y⟩

theorem face_sub_reach (x y : (νPk κ).X) : face x y ⊆ ReachSet x := by
  rintro z ⟨hstep, hreach⟩
  exact (Reaches.step hstep).trans' hreach

/-! ## Ω recovered inside `νPk`, with its improper self-face (transcribed) -/

noncomputable def omegaState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (omegaCoalg hinf)).choose PUnit.unit

theorem omega_selfsingleton (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (omegaState hinf)).1 = {omegaState hinf} := by
  have hnat := (νPk_terminal κ (omegaCoalg hinf)).choose_spec.1 PUnit.unit
  unfold omegaState
  rw [hnat]; simp [PkMap, omegaCoalg]

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

theorem reachSet_omega (hinf : ℵ₀ ≤ κ) : ReachSet (omegaState hinf) = {omegaState hinf} := by
  ext z; simp only [ReachSet, Set.mem_setOf_eq, Set.mem_singleton_iff]; exact reaches_omega hinf z

theorem omega_face (hinf : ℵ₀ ≤ κ) :
    face (omegaState hinf) (omegaState hinf) = {omegaState hinf} := by
  ext z
  simp only [mem_face, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hz⟩; exact (reaches_omega hinf z).mp hz
  · rintro rfl
    refine ⟨?_, Reaches.refl' _⟩
    rw [omega_selfsingleton hinf]; rfl

/-! ## The labelled (faced) carrier `νLk κ Q` (transcribed Series 04 WS3) -/

variable {Q : Type u}

/-- The labelled powerset functor: successors of `X` each carry a quality label from `Q`. -/
def LkObj (κ : Cardinal.{u}) (Q : Type u) (X : Type u) : Type u := PkObj κ (Q × X)

/-- Functorial action: relabel the target of each edge, keeping its face. -/
def LkMap {X Y : Type u} (f : X → Y) (s : LkObj κ Q X) : LkObj κ Q Y :=
  PkMap κ (Prod.map id f) s

section QPFInstance
open Ordinal Set

/-- The polynomial functor of which the labelled functor is a quotient. -/
def LkP (κ : Cardinal.{u}) (Q : Type u) : PFunctor.{u} where
  A := Σ a : κ.ord.toType, ({b : κ.ord.toType // b < a} → Q)
  B := fun p => {b : κ.ord.toType // b < p.1}

def absLk {X : Type u} (p : (LkP κ Q).Obj X) : LkObj κ Q X :=
  ⟨Set.range (fun i => (p.1.2 i, p.2 i)),
    lt_of_le_of_lt Cardinal.mk_range_le (card_typein_toType_lt κ p.1.1)⟩

noncomputable def reprLk {X : Type u} (s : LkObj κ Q X) :
    { p : (LkP κ Q).Obj X // Set.range (fun i => (p.1.2 i, p.2 i)) = s.1 } := by
  have ho' : (Cardinal.mk (↥s.1)).ord < type (α := κ.ord.toType) (· < ·) := by
    rw [type_toType]; exact Cardinal.ord_lt_ord.mpr s.2
  set a : κ.ord.toType := enum (α := κ.ord.toType) (· < ·) ⟨(Cardinal.mk (↥s.1)).ord, ho'⟩ with ha
  have hcard : Cardinal.mk {b : κ.ord.toType // b < a} = Cardinal.mk (↥s.1) := by
    have h1 : Cardinal.mk {b : κ.ord.toType // b < a} = (typein (α := κ.ord.toType) (· < ·) a).card :=
      card_typein a
    rw [h1, ha, typein_enum, Cardinal.card_ord]
  let e : {b : κ.ord.toType // b < a} ≃ ↥s.1 := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨⟨⟨a, fun i => ((e i : Q × X)).1⟩, fun i => ((e i : Q × X)).2⟩, ?_⟩
  show Set.range (fun i => (((e i : Q × X)).1, ((e i : Q × X)).2)) = s.1
  have : (fun i => (((e i : Q × X)).1, ((e i : Q × X)).2)) = (Subtype.val ∘ e) := by
    funext i; exact Prod.ext rfl rfl
  rw [this, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]

noncomputable instance qpfLk : QPF (LkObj κ Q) where
  map f s := LkMap f s
  P := LkP κ Q
  abs := absLk
  repr s := (reprLk s).1
  abs_repr s := by
    apply Subtype.ext
    show Set.range (fun i => ((reprLk s).1.1.2 i, (reprLk s).1.2 i)) = s.1
    exact (reprLk s).2
  abs_map f p := by
    apply Subtype.ext
    show Set.range (fun i => (p.1.2 i, f (p.2 i))) = (Prod.map id f) '' Set.range (fun i => (p.1.2 i, p.2 i))
    have hfun : (fun i => (p.1.2 i, f (p.2 i)))
        = (Prod.map id f) ∘ (fun i => (p.1.2 i, p.2 i)) := by funext i; rfl
    rw [hfun, Set.range_comp]

end QPFInstance

/-- The labelled carrier: the terminal coalgebra of `X ↦ P_κ (Q × X)`. -/
noncomputable def νLk (κ : Cardinal.{u}) (Q : Type u) : Type u := Cofix (LkObj κ Q)

/-- The structure map (dest) of the labelled carrier. -/
noncomputable def lstr (x : νLk κ Q) : LkObj κ Q (νLk κ Q) := Cofix.dest x

/-- The one-point coalgebra with a self-loop carrying face `q`. -/
noncomputable def loopCoalg (q : Q) (hinf : ℵ₀ ≤ κ) :
    PUnit.{u+1} → LkObj κ Q PUnit.{u+1} :=
  fun _ => ⟨{(q, PUnit.unit)}, mk_singleton_lt hinf _⟩

/-- The self-loop state at face `q`. -/
noncomputable def loopState (q : Q) (hinf : ℵ₀ ≤ κ) : νLk κ Q :=
  Cofix.corec (loopCoalg q hinf) PUnit.unit

/-- The loop's unfolding: its single successor is itself, carried on a face-`q` edge. -/
theorem loop_dest (q : Q) (hinf : ℵ₀ ≤ κ) :
    (Cofix.dest (loopState q hinf)).1 = {(q, loopState q hinf)} := by
  have h := Cofix.dest_corec (loopCoalg q hinf) PUnit.unit
  show (Cofix.dest (loopState q hinf)).1 = _
  rw [loopState, h]
  show (LkMap (Cofix.corec (loopCoalg q hinf)) (loopCoalg q hinf PUnit.unit)).1 = _
  simp only [LkMap, loopCoalg, PkMap_val, Set.image_singleton, Prod.map_apply, id_eq]

/-- **Twin self-loops with different faces are distinct.** -/
theorem ws3_loopface_ne (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    loopState q₁ hinf ≠ loopState q₂ hinf := by
  intro he
  apply hne
  have h1 := loop_dest q₁ hinf
  have h2 := loop_dest q₂ hinf
  rw [he] at h1
  rw [h2] at h1
  have hpair : (q₂, loopState q₂ hinf) = (q₁, loopState q₂ hinf) :=
    Set.singleton_eq_singleton_iff.mp h1
  exact (Prod.ext_iff.mp hpair).1.symm

/-- A labelled state is **non-atomic** when its successor set is nonempty. -/
def NonAtomic (x : νLk κ Q) : Prop := (Cofix.dest x).1.Nonempty

theorem loop_nonAtomic (q : Q) (hinf : ℵ₀ ≤ κ) : NonAtomic (loopState q hinf) := by
  rw [NonAtomic, loop_dest]; exact Set.singleton_nonempty _

/-- **Plurality without atoms.** -/
theorem ws3_plurality_core (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ∃ a b : νLk κ Q, a ≠ b ∧ NonAtomic a ∧ NonAtomic b :=
  ⟨loopState q₁ hinf, loopState q₂ hinf, ws3_loopface_ne hinf hne,
   loop_nonAtomic q₁ hinf, loop_nonAtomic q₂ hinf⟩

theorem ws3_plurality_core_concrete (hinf : ℵ₀ ≤ κ) :
    ∃ a b : νLk κ (ULift.{u} Bool), a ≠ b ∧ NonAtomic a ∧ NonAtomic b :=
  ws3_plurality_core hinf (q₁ := ⟨false⟩) (q₂ := ⟨true⟩) (by decide)

/-! ## Composition stays atom-free (transcribed Series 04 WS3 `lcomp`) -/

/-- The composition (state-forming) coalgebra. -/
noncomputable def lcompCoalg (t : LkObj κ Q (νLk κ Q)) :
    Option (νLk κ Q) → LkObj κ Q (Option (νLk κ Q))
  | none => PkMap κ (Prod.map id Option.some) t
  | some s => PkMap κ (Prod.map id Option.some) (Cofix.dest s)

/-- **The composite state** formed from a labelled successor structure. -/
noncomputable def lcomp (t : LkObj κ Q (νLk κ Q)) : νLk κ Q :=
  Cofix.corec (lcompCoalg t) none

theorem lcomp_dest (t : LkObj κ Q (νLk κ Q)) :
    Cofix.dest (lcomp t)
      = LkMap (Cofix.corec (lcompCoalg t)) (PkMap κ (Prod.map id Option.some) t) := by
  rw [lcomp, Cofix.dest_corec]; rfl

theorem lcomp_succ_nonatomic (t : LkObj κ Q (νLk κ Q)) (s : νLk κ Q) (hs : NonAtomic s) :
    NonAtomic (Cofix.corec (lcompCoalg t) (Option.some s)) := by
  rw [NonAtomic, Cofix.dest_corec]
  show (LkMap (Cofix.corec (lcompCoalg t))
      (PkMap κ (Prod.map id Option.some) (Cofix.dest s))).1.Nonempty
  simp only [LkMap, PkMap_val]
  exact ((show (Cofix.dest s).1.Nonempty from hs).image _).image _

/-- **Composition never annihilates a face** — unconditionally. -/
theorem ws3_faces_never_annihilate (t : LkObj κ Q (νLk κ Q))
    (ht : t.1.Nonempty) (hmem : ∀ p ∈ t.1, NonAtomic p.2) :
    NonAtomic (lcomp t) ∧ ∀ p ∈ (Cofix.dest (lcomp t)).1, NonAtomic p.2 := by
  refine ⟨?_, ?_⟩
  · rw [NonAtomic, lcomp_dest]
    show (LkMap (Cofix.corec (lcompCoalg t)) (PkMap κ (Prod.map id Option.some) t)).1.Nonempty
    simp only [LkMap, PkMap_val]
    exact (ht.image _).image _
  · intro p hp
    rw [lcomp_dest] at hp
    simp only [LkMap, PkMap_val] at hp
    rcases hp with ⟨a, ha, rfl⟩
    rcases ha with ⟨b, hb, rfl⟩
    exact lcomp_succ_nonatomic t b.2 (hmem b hb)

/-! ## Level-local bisimulation-is-identity for the labelled carrier `νLk`

The colimit gate reduces to bisimulation-is-identity *at each level* (the design's D2:
"the gate is level-local `bisim_eq` + `ι_inj`"). Series 04 never needed a `bisim_eq` for
the labelled carrier `νLk`; Series 05's gate does, so we derive it directly from
Mathlib's generic `Cofix.bisim_rel` (`νLk κ Q = Cofix (LkObj κ Q)`, and `<$>` on the
QPF `LkObj κ Q` is `LkMap`). -/

/-- **`νLk` bisimulation-is-identity.** If `R` relates states whose one-step
unfoldings agree after quotienting by `R`, then `R`-related states are equal. This is
`Cofix.bisim_rel` for the labelled functor. -/
theorem nuLk_bisim_eq {κ : Cardinal.{u}} {Q : Type u} (R : νLk κ Q → νLk κ Q → Prop)
    (h : ∀ x y, R x y → LkMap (Quot.mk R) (lstr x) = LkMap (Quot.mk R) (lstr y)) :
    ∀ x y, R x y → x = y :=
  Cofix.bisim_rel R (fun x y hxy => h x y hxy)

/-! ## Bound relaxation: including a `< κ₁`-bounded structure as `< κ₂`-bounded

The connecting maps `ι` of the tower are **bound-relaxing inclusions** (design C2): they
do not touch edges, they only relax the successor bound `κ_α ≤ κ_β`. In Lean `LkObj κ_α`
and `LkObj κ_β` are *distinct types* (the cardinality predicate differs), so the
coalgebra-morphism law must carry this relaxation explicitly — on the underlying set it
is the identity. -/

/-- Relax the bound of a `P_κ₁`-object to a `P_κ₂`-object (`κ₁ ≤ κ₂`); the underlying
set is unchanged. -/
noncomputable def PkRelax {X : Type u} {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (s : PkObj κ₁ X) :
    PkObj κ₂ X :=
  ⟨s.1, lt_of_lt_of_le s.2 hle⟩

@[simp] lemma PkRelax_val {X : Type u} {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (s : PkObj κ₁ X) :
    (PkRelax hle s).1 = s.1 := rfl

/-- Relax the bound of a labelled structure. -/
noncomputable def LkRelax {X : Type u} {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (s : LkObj κ₁ Q X) :
    LkObj κ₂ Q X := PkRelax hle s

/-! ## The directed tower and its colimit (design C2) -/

/-- A **level**: a Series-04 faced carrier at a cardinal `κ_α ≥ ℵ₀`. -/
structure Level (Q : Type u) where
  card : Cardinal.{u}
  hinf : ℵ₀ ≤ card

/-- The carrier of a level is the labelled terminal coalgebra `νLk κ_α Q`. -/
noncomputable def Level.carrier {Q : Type u} (L : Level Q) : Type u := νLk L.card Q

/-- The **directed tower**: an index with no greatest element required only to be
*directed* here (no-least/no-greatest are WS2's obligations), unbounded cardinals, and
bound-relaxing connecting maps that preserve the successor structure. The
coalgebra-morphism law `ι_dest` carries the bound relaxation `LkRelax`. -/
structure Tower (Q : Type u) where
  Idx      : Type w
  le       : Idx → Idx → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  directed : ∀ a b, ∃ c, le a c ∧ le b c
  lvl      : Idx → Level Q
  mono     : ∀ {a b}, le a b → (lvl a).card ≤ (lvl b).card
  ι        : ∀ {a b}, le a b → (lvl a).carrier → (lvl b).carrier
  ι_dest   : ∀ {a b} (h : le a b) (x : (lvl a).carrier),
               lstr (ι h x) = LkRelax (mono h) (LkMap (ι h) (lstr x))
  ι_refl   : ∀ {a} (x : (lvl a).carrier), ι (le_refl a) x = x
  ι_trans  : ∀ {a b c} (hab : le a b) (hbc : le b c) (x : (lvl a).carrier),
               ι hbc (ι hab x) = ι (le_trans hab hbc) x
  ι_inj    : ∀ {a b} (h : le a b), Function.Injective (ι h)

variable {Q : Type u}

/-- The directed-system relation: `p ~ q` iff they agree at some common upper level. -/
def TowerColimRel (T : Tower Q) :
    (Σ a, (T.lvl a).carrier) → (Σ a, (T.lvl a).carrier) → Prop :=
  fun p q => ∃ (c : T.Idx) (hpc : T.le p.1 c) (hqc : T.le q.1 c), T.ι hpc p.2 = T.ι hqc q.2

/-- The colimit carrier `W_∞`. Lives in `Type (max u w)`: the level carriers are `Type u`,
but the index `T.Idx` is `Type w`, so with a proper-class (universe-bumped) index the colimit
lands one universe up. For set-indexed towers (`w = u`, e.g. `constTower`, `growingTower`) it
is the expected `Type u`. -/
def Winf (T : Tower.{u, w} Q) : Type (max u w) := Quot (TowerColimRel T)

/-- Injection of a level into the colimit. -/
def toColim (T : Tower Q) {a : T.Idx} (x : (T.lvl a).carrier) : Winf T := Quot.mk _ ⟨a, x⟩

/-- **D1 — the directed-system relation is an equivalence** (the colimit exists). -/
theorem ws1_colim_equiv (T : Tower Q) : Equivalence (TowerColimRel T) := by
  constructor
  · intro p; exact ⟨p.1, T.le_refl p.1, T.le_refl p.1, rfl⟩
  · rintro p q ⟨c, hpc, hqc, h⟩; exact ⟨c, hqc, hpc, h.symm⟩
  · rintro p q r ⟨c, hpc, hqc, h1⟩ ⟨d, hqd, hrd, h2⟩
    obtain ⟨e, hce, hde⟩ := T.directed c d
    refine ⟨e, T.le_trans hpc hce, T.le_trans hrd hde, ?_⟩
    have e1 : T.ι (T.le_trans hpc hce) p.2 = T.ι hce (T.ι hpc p.2) := (T.ι_trans hpc hce p.2).symm
    have e2 : T.ι (T.le_trans hrd hde) r.2 = T.ι hde (T.ι hrd r.2) := (T.ι_trans hrd hde r.2).symm
    have e3 : T.ι hce (T.ι hqc q.2) = T.ι (T.le_trans hqc hce) q.2 := T.ι_trans hqc hce q.2
    have e4 : T.ι hde (T.ι hqd q.2) = T.ι (T.le_trans hqd hde) q.2 := T.ι_trans hqd hde q.2
    rw [e1, e2, h1, ← h2, e3, e4]

/-- Moving a state up the tower does not change its colimit image. -/
theorem toColim_ι (T : Tower Q) {a c : T.Idx} (h : T.le a c) (x : (T.lvl a).carrier) :
    toColim T (T.ι h x) = toColim T x :=
  Quot.sound ⟨c, T.le_refl c, h, T.ι_refl (T.ι h x)⟩

/-! ### The colimit structure map, as a representative-independent successor set

Design D2 typed `destInf : Winf T → Σ' a, LkObj κ_α Q (Winf T)`. That `Σ'` codomain is
**not** definable by `Quot.lift`: the first component `α` depends on the representative's
level, so two representatives of the same colimit point give `⟨a, _⟩ ≠ ⟨b, _⟩` unless
`a = b`. The representative-*independent* object is the successor **set** inside `W_∞`.
We realize `destInf` as that set (`succSet`); the honest local bound `< κ_α` is recovered
separately as `ws1_local_bound`. (Design fix recorded in `charter-status.md`, WS1.) -/

/-- The successor set of a chosen representative, mapped into the colimit. -/
def succSetPre (T : Tower Q) (p : Σ a, (T.lvl a).carrier) : Set (Q × Winf T) :=
  (fun qz : Q × (T.lvl p.1).carrier => (qz.1, toColim T qz.2)) '' (lstr p.2).1

/-- Reindexing a representative up the tower leaves its colimit successor set unchanged
— the load-bearing use of `ι_dest` (the connecting maps commute with `dest`). -/
theorem succSetPre_ι (T : Tower Q) {a c : T.Idx} (h : T.le a c) (x : (T.lvl a).carrier) :
    succSetPre T ⟨a, x⟩ = succSetPre T ⟨c, T.ι h x⟩ := by
  have hdest : (lstr (T.ι h x)).1 = (Prod.map id (T.ι h)) '' (lstr x).1 := by
    rw [T.ι_dest h x]; simp only [LkRelax, PkRelax_val, LkMap, PkMap_val]
  show (fun qz : Q × (T.lvl a).carrier => (qz.1, toColim T qz.2)) '' (lstr x).1
     = (fun qz : Q × (T.lvl c).carrier => (qz.1, toColim T qz.2)) '' (lstr (T.ι h x)).1
  rw [hdest]
  ext w
  constructor
  · rintro ⟨qz, hqz, rfl⟩
    exact ⟨(qz.1, T.ι h qz.2), ⟨qz, hqz, rfl⟩, by simp [toColim_ι]⟩
  · rintro ⟨qz', hqz', rfl⟩
    obtain ⟨qz, hqz, rfl⟩ := hqz'
    exact ⟨qz, hqz, by simp [Prod.map, toColim_ι]⟩

theorem succSetPre_respects (T : Tower Q) :
    ∀ p q, TowerColimRel T p q → succSetPre T p = succSetPre T q := by
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, hac, hbc, heq⟩
  rw [succSetPre_ι T hac x, succSetPre_ι T hbc y, heq]

/-- **`destInf` (realized as the colimit successor set).** Representative-independent by
`ι_dest`. -/
def succSet (T : Tower Q) : Winf T → Set (Q × Winf T) :=
  Quot.lift (succSetPre T) (succSetPre_respects T)

@[simp] theorem succSet_toColim (T : Tower Q) {a : T.Idx} (x : (T.lvl a).carrier) :
    succSet T (toColim T x)
      = (fun qz : Q × (T.lvl a).carrier => (qz.1, toColim T qz.2)) '' (lstr x).1 := rfl

/-- `x` relates to `y` in the colimit: `y`, on some face `q`, is a colimit successor of
`x`. -/
def RelatesInf (T : Tower Q) (x y : Winf T) : Prop := ∃ q : Q, (q, y) ∈ succSet T x

/-! ### D2 — the colimit gate: bisimulation is identity on `W_∞` -/

/-- A **colimit bisimulation**: a relation on `W_∞` that, at a common level, restricts to
a level-local `νLk`-bisimulation. This is exactly the design's reduction — "`R` pulls back
along `toColim` to a bisimulation on each `W_α`." -/
def ColimBisim (T : Tower Q) (R : Winf T → Winf T → Prop) : Prop :=
  ∀ x y, R x y → ∃ (c : T.Idx) (x' y' : (T.lvl c).carrier),
    x = toColim T x' ∧ y = toColim T y' ∧
    ∃ Rloc : (T.lvl c).carrier → (T.lvl c).carrier → Prop, Rloc x' y' ∧
      (∀ u v, Rloc u v → LkMap (Quot.mk Rloc) (lstr u) = LkMap (Quot.mk Rloc) (lstr v))

/-- **D2 — the gate. Bisimulation is identity on `W_∞`.** A colimit bisimulation is
contained in the diagonal: it reduces, at a common level, to the level-local
`nuLk_bisim_eq` (terminal-coalgebra bisimulation-is-identity), transported by `toColim`.
This is the existential obligation the whole program is conditional on, discharged. -/
theorem ws1_bisim_eq_colim (T : Tower Q) (R : Winf T → Winf T → Prop)
    (hR : ColimBisim T R) : ∀ x y, R x y → x = y := by
  intro x y hxy
  obtain ⟨c, x', y', hx, hy, Rloc, hloc, hbis⟩ := hR x y hxy
  have hxy' : x' = y' := nuLk_bisim_eq Rloc hbis x' y' hloc
  rw [hx, hy, hxy']

/-! ### D3 — Ω recovered inside `W_∞`, with an honest local bound -/

/-- The self-loop Ω lives at every level; here it is placed at level `a` with face `q`. -/
noncomputable def omegaInf (T : Tower Q) (a : T.Idx) (q : Q) : Winf T :=
  toColim T (loopState q (T.lvl a).hinf)

/-- **Ω's colimit unfolding is the self-singleton `{(q, Ω)}`.** -/
theorem ws1_omega_selfloop (T : Tower Q) (a : T.Idx) (q : Q) :
    succSet T (omegaInf T a q) = {(q, omegaInf T a q)} := by
  have hloop : (lstr (loopState q (T.lvl a).hinf)).1 = {(q, loopState q (T.lvl a).hinf)} :=
    loop_dest q (T.lvl a).hinf
  unfold omegaInf
  rw [succSet_toColim, hloop, Set.image_singleton]

/-- **D3 — every colimit object has an honest local `< κ_α` bound.** Every point has a
representative at some level `α`, where its successor count is `< κ_α` by the `νLk`
bound. -/
theorem ws1_local_bound (T : Tower Q) (x : Winf T) :
    ∃ (a : T.Idx) (y : (T.lvl a).carrier), x = toColim T y ∧
      Cardinal.mk ↥(lstr y).1 < (T.lvl a).card := by
  obtain ⟨⟨a, y⟩, hxy⟩ := Quot.exists_rep x
  exact ⟨a, y, hxy.symm, (lstr y).2⟩

/-! ### Non-vacuity: a concrete tower exists (the constant tower)

`Tower Q` is inhabited, so the `∀ T : Tower Q` theorems are not vacuous. The constant
tower (all levels at one cardinal `κ`, `ι = id`) is a genuine `Tower`; it does *not*
satisfy `DoubleUnboundedness` (its cardinals are not unbounded) — correctly, since a
constant tower is really a single carrier and walls (WS2/WS3). A *doubly-unbounded*
inhabitant needs the bound-relaxing injective coalgebra-morphism inclusions between
different-cardinal `νLk`, which is the charter §9 existential; the abstract `Tower` is
the WS1 deliverable, per the design. -/
noncomputable def constTower (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) (Q : Type u) : Tower Q where
  Idx := ULift.{u} ℤ
  le := fun a b => a.down ≤ b.down
  le_refl := fun a => le_refl a.down
  le_trans := fun hab hbc => le_trans hab hbc
  directed := fun a b => ⟨⟨max a.down b.down⟩, le_max_left _ _, le_max_right _ _⟩
  lvl := fun _ => ⟨κ, hinf⟩
  mono := fun _ => le_refl κ
  ι := fun _ x => x
  ι_dest := fun _ x => by
    apply Subtype.ext
    show (lstr x).1 = ((LkRelax (le_refl κ) (LkMap (id : νLk κ Q → νLk κ Q) (lstr x)))).1
    simp [LkRelax, LkMap, PkMap_id]
  ι_refl := fun _ => rfl
  ι_trans := fun _ _ _ => rfl
  ι_inj := fun _ => Function.injective_id

end Series05.WS1
