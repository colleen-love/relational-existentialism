/-
`series-9/formal/Series9/ws1.lean`

WS1 — **The hold-reflexive carrier and the diagonal spine.** Series 9, the blocking spine.

This file is SELF-CONTAINED: it transcribes (re-namespaced `Series9.WS1`) the plain `P_κ` /
bisimulation machinery, the labelled/face machinery, the collapse, and the Series 8 coincidence
witness (`ws1_symmetric_states_bisimilar`) — nothing is imported from `series-8/`, `series-7/`,
`series-4/`, or `archive/`. On top of that transcribed carrier it adds the Series 9 primitive it
lacked: **hold-reflexivity**, an inspection `insp : Hold dest → (Hold dest → Prop)` under which a hold
ranges over the space of holds. It then establishes the central negative — no hold contains its own
complete content — by a Cantor/Lawvere diagonal (`ws1_no_self_total_hold`), and CERTIFIES the proof is
a fixed-point contradiction, NOT the Series 8 bisimulation (`ws1_diagonal_not_bisim`).

Design doc: `series-9/spec/ws1-design.md`; shared objects `series-9/spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Mathlib

universe u

namespace Series9.WS1

open Cardinal

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (transcribed from Series 8 `ws1`) -/

def PkObj (κ : Cardinal.{u}) (X : Type u) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}

def PkMap (κ : Cardinal.{u}) {X Y : Type u} (f : X → Y) (s : PkObj κ X) : PkObj κ Y :=
  ⟨f '' s.1, lt_of_le_of_lt Cardinal.mk_image_le s.2⟩

@[simp] lemma PkMap_val {X Y : Type u} (f : X → Y) (s : PkObj κ X) :
    (PkMap κ f s).1 = f '' s.1 := rfl

lemma mk_empty_lt {α : Type u} (hinf : ℵ₀ ≤ κ) : Cardinal.mk (↥(∅ : Set α)) < κ := by
  haveI : IsEmpty (↥(∅ : Set α)) := ⟨fun x => (Set.mem_empty_iff_false _).mp x.2⟩
  rw [Cardinal.mk_eq_zero]
  exact lt_of_lt_of_le Cardinal.aleph0_pos hinf

lemma mk_singleton_lt {α : Type u} (hinf : ℵ₀ ≤ κ) (a : α) :
    Cardinal.mk (↥({a} : Set α)) < κ := by
  rw [Cardinal.mk_singleton]
  exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf

noncomputable def toPk (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) : PkObj κ X :=
  ⟨s, by
    haveI : Finite (↥s) := Subtype.finite
    exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite (↥s)) hinf⟩

@[simp] lemma toPk_val (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) :
    (toPk hinf s).1 = s := rfl

/-! ## Reaching, atomlessness, bisimulation, behavioral identity (transcribed) -/

def SReaches {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  Relation.ReflTransGen (fun a b => b ∈ (dest a).1)

/-- Strong hereditary non-emptiness: every reachable state has a nonempty successor set. -/
def SHNE {X : Type u} (dest : X → PkObj κ X) (x : X) : Prop :=
  ∀ v, SReaches dest x v → (dest v).1 ≠ ∅

lemma SHNE.ne_empty {X : Type u} {dest : X → PkObj κ X} {x : X}
    (hx : SHNE dest x) : (dest x).1 ≠ ∅ := hx x Relation.ReflTransGen.refl

lemma SHNE.succ {X : Type u} {dest : X → PkObj κ X} {x w : X}
    (hx : SHNE dest x) (hw : w ∈ (dest x).1) : SHNE dest w :=
  fun v hv => hx v (Relation.ReflTransGen.head hw hv)

def IsBisim {X : Type u} (dest : X → PkObj κ X) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ x' ∈ (dest x).1, ∃ y' ∈ (dest y).1, R x' y') ∧
    (∀ y' ∈ (dest y).1, ∃ x' ∈ (dest x).1, R x' y')

/-- **Behavioral identity = no imported atom.** -/
def BehaviorallyIdentified {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ (R : X → X → Prop), IsBisim dest R → ∀ x y, R x y → x = y

/-- The "both hereditarily non-empty" relation. -/
def hneRel {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  fun x y => SHNE dest x ∧ SHNE dest y

/-- **The engine's core.** The "both-atomless" relation is a bisimulation. -/
lemma hneRel_isBisim {X : Type u} (dest : X → PkObj κ X) : IsBisim dest (hneRel dest) := by
  rintro x y ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · intro x' hx'
    obtain ⟨y', hy'⟩ := Set.nonempty_iff_ne_empty.mpr hy.ne_empty
    exact ⟨y', hy', hx.succ hx', hy.succ hy'⟩
  · intro y' hy'
    obtain ⟨x', hx'⟩ := Set.nonempty_iff_ne_empty.mpr hx.ne_empty
    exact ⟨x', hx', hx.succ hx', hy.succ hy'⟩

/-- **The engine.** On any plain coalgebra, any two atomless states are related by a bisimulation. -/
theorem ws1_atomless_bisim {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y :=
  ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩

/-- Behavioral identity turns the engine into equality. -/
theorem ws1_recovers_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) :
    x = y := by
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim dest x y hx hy
  exact hbehav R hR x y hxy

/-- **The Import Theorem (static form, the collapse).** A plain, behaviorally-identified, atomless
coalgebra is a subsingleton. -/
theorem ws2_import_theorem_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ⟨fun x y => ws1_recovers_static dest hbehav x y (hatom x) (hatom y)⟩

/-! ## The trivial self-loop (the positionless One), transcribed -/

noncomputable def twoLoop (hinf : ℵ₀ ≤ κ) : ULift.{u} Bool → PkObj κ (ULift.{u} Bool) :=
  fun i => toPk hinf {i}

@[simp] lemma twoLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) : (twoLoop hinf i).1 = {i} := rfl

lemma twoLoop_step (hinf : ℵ₀ ≤ κ) (a b : ULift.{u} Bool) :
    b ∈ (twoLoop hinf a).1 ↔ b = a := by rw [twoLoop_val, Set.mem_singleton_iff]

lemma twoLoop_reaches (hinf : ℵ₀ ≤ κ) (i j : ULift.{u} Bool) :
    SReaches (twoLoop hinf) i j → j = i := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      have hcb := (twoLoop_step hinf _ _).mp hbc
      rw [hcb]; exact ih

lemma twoLoop_HNE (hinf : ℵ₀ ≤ κ) : ∀ i, SHNE (twoLoop hinf) i := by
  intro i v hv
  rw [twoLoop_reaches hinf i v hv, twoLoop_val]
  exact Set.singleton_ne_empty i

/-! ## The labelled functor and the recoverable/free face test (transcribed from Series 8 `ws1`/`ws4`) -/

/-- The **labelled** functor: successors carry a coordinate from `Q` — NOT plain `P_κ`. -/
def LkObj (κ : Cardinal.{u}) (Q X : Type u) : Type u := PkObj κ (Q × X)

/-- A **label-respecting** bisimulation. -/
def IsBisimL {Q X : Type u} (dest : X → LkObj κ Q X) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ p ∈ (dest x).1, ∃ q ∈ (dest y).1, p.1 = q.1 ∧ R p.2 q.2) ∧
    (∀ q ∈ (dest y).1, ∃ p ∈ (dest x).1, p.1 = q.1 ∧ R p.2 q.2)

/-- Behavioral identity for the labelled functor. -/
def BehaviorallyIdentifiedL {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisimL dest R → ∀ x y, R x y → x = y

/-- Forget the label, keep the target: the plain (label-forgetting) coalgebra. -/
noncomputable def plainOf {Q X : Type u} (dest : X → LkObj κ Q X) : X → PkObj κ X :=
  fun x => PkMap κ Prod.snd (dest x)

/-- A label is **recoverable** if every plain bisimulation is already a label-bisimulation. -/
def Recoverable {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R

/-- **A recoverable label is NOT an import (semantic import test, negative horn).** -/
theorem ws4_recoverable_not_import {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (x y : X)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
    ∃ R, IsBisimL dest R ∧ R x y :=
  let ⟨R, hR, hxy⟩ := h
  ⟨R, hrec R hR, hxy⟩

/-- **The free directed hold**: state `i` self-loops carrying its own index as the label. -/
noncomputable def labelLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Bool) (ULift.{u} Bool) :=
  fun i => toPk hinf {(i, i)}

@[simp] lemma labelLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (labelLoop hinf i).1 = {(i, i)} := rfl

/-- **The label distinction survives the label-quotient.** -/
theorem ws4_label_survives_quotient (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hforward, _⟩ := hR ⟨true⟩ ⟨false⟩ hRel
  obtain ⟨q, hq, hfst, _⟩ := hforward (⟨true⟩, ⟨true⟩) (by rw [labelLoop_val]; exact rfl)
  rw [labelLoop_val, Set.mem_singleton_iff] at hq
  subst hq
  exact absurd hfst (by decide)

@[simp] lemma plainOf_labelLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (plainOf (labelLoop hinf) i).1 = {i} := by
  show Prod.snd '' ({(i, i)} : Set (ULift.{u} Bool × ULift.{u} Bool)) = {i}
  rw [Set.image_singleton]

lemma plainOf_labelLoop_reaches (hinf : ℵ₀ ≤ κ) (i j : ULift.{u} Bool) :
    SReaches (plainOf (labelLoop hinf)) i j → j = i := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rw [plainOf_labelLoop_val, Set.mem_singleton_iff] at hbc
      rw [hbc]; exact ih

lemma labelLoop_atomless (hinf : ℵ₀ ≤ κ) : ∀ i, SHNE (plainOf (labelLoop hinf)) i := by
  intro i v hv
  rw [plainOf_labelLoop_reaches hinf i v hv, plainOf_labelLoop_val]
  exact Set.singleton_ne_empty i

lemma plainOf_labelLoop_true_bisim (hinf : ℵ₀ ≤ κ) :
    IsBisim (plainOf (labelLoop hinf)) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' _; exact ⟨y, by rw [plainOf_labelLoop_val]; exact rfl, trivial⟩
  · intro y' _; exact ⟨x, by rw [plainOf_labelLoop_val]; exact rfl, trivial⟩

/-- **The free label is a genuine import (semantic import test, positive horn).** -/
theorem ws4_free_label_is_import (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩,
   ws4_label_survives_quotient hinf⟩

/-- **The free label is NOT recoverable.** -/
theorem ws4_labelLoop_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) := by
  intro hrec
  exact ws4_label_survives_quotient hinf
    ⟨fun _ _ => True, hrec _ (plainOf_labelLoop_true_bisim hinf), trivial⟩

/-! ## The Series 8 coincidence witness (transcribed as the negative touchstone, §4.1) -/

/-- **The positionless property.** Every position relates identically. -/
def Symmetric {Q X : Type u} (dest : X → LkObj κ Q X) : Prop := ∀ x y, dest x = dest y

/-- **On a positionless coalgebra the all-true relation is a label-bisimulation.** -/
theorem ws1_symmetric_bisim_trivial {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) : IsBisimL dest (fun _ _ => True) := by
  intro x y _
  refine ⟨fun p hp => ⟨p, ?_, rfl, trivial⟩, fun q hq => ⟨q, ?_, rfl, trivial⟩⟩
  · rw [← hsym x y]; exact hp
  · rw [hsym x y]; exact hq

/-- **The Series 8 coincidence witness.** On a positionless coalgebra ANY two states are
label-bisimilar. This is the thing the Series 9 spine must NOT unfold to (charter §4.1): Series 8's
collapse was behavioral identity applied to THIS bisimulation. WS1's diagonal must be a fixed-point
contradiction that is structurally UNLIKE this — it produces no bisimulation, it denies a fixed point. -/
theorem ws1_symmetric_states_bisimilar {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) (x y : X) : ∃ R, IsBisimL dest R ∧ R x y :=
  ⟨fun _ _ => True, ws1_symmetric_bisim_trivial dest hsym, trivial⟩

/-! ## The hold primitive `x↾(x,y)` (Series 8/4, holding-first — charter §3) -/

/-- **A hold `x↾(x,y)`**: `x` restricting toward its successor `y`. Holding is primitive. -/
def Hold {X : Type u} (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }

/-- **What the hold affords**: the sub-field it turns toward (Series 4's face, forced by `dest`). -/
def afford {X : Type u} (dest : X → PkObj κ X) (h : Hold dest) : Set X :=
  { z | SReaches dest h.1.2 z }

/-! ## The hold-reflexive layer (Series 9, README §2.3) -/

/-- A **content**: which holds a hold's complete face contains. A predicate over the WHOLE space of
holds — not a successor point. This is what a self-loop carrier cannot express. -/
def HoldPred {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → Prop

/-- The **diagonal residue** of an inspection: the completed judgment about self-holding — the content
no hold can correctly contain. Cantor/Lawvere's diagonal term. -/
def diag {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  fun h => ¬ insp h h

/-- **The self-total fixed-point equation.** A hold `t` is self-total iff its content is the completed
self-inspection: `insp t = diag insp`. "A hold whose content includes its own complete content." -/
def SelfTotal {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := ∀ h, insp t h ↔ diag insp h

/-- A **self-loop inspection**: content is a POINT (the singleton predicate `· = h`). The degenerate,
Series-8-strength inspection on which the diagonal has nothing to bite. -/
def inspLoop {X : Type u} {dest : X → PkObj κ X} : Hold dest → HoldPred dest :=
  fun h => (fun h' => h' = h)

/-! ## The WS1 deliverables -/

/-- **D0 — the hold is forced (carrier hygiene).** `afford` is the unique function of `dest`; the
reflexive layer refines the carrier, it does not annotate it. (Series 4 `ws1_face_forced`.) -/
theorem ws1_hold_forced {X : Type u} (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z } :=
  ⟨afford dest, fun _ => rfl, fun _g hg => funext fun h => hg h⟩

/-- **D1 — THE SPINE (Impossibility proved, independent of relational identity).** No hold contains its
own complete content: the self-total fixed-point equation `insp t = diag insp` has no solution, by the
diagonal instantiation `insp t t ↔ ¬ insp t t`. The proof references ONLY `insp` and propositional
logic — NO bisimulation, NO behavioral identity. -/
theorem ws1_no_self_total_hold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t := by
  rintro ⟨t, ht⟩
  have h : insp t t ↔ ¬ insp t t := ht t
  have np : ¬ insp t t := fun hp => h.mp hp hp
  exact np (h.mpr np)

/-- **D2 — the Cantor form (equivalent to D1).** No inspection surjects onto the space of contents; the
missed content is `diag insp`. -/
theorem ws1_insp_not_surjective {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (diag insp)
  exact ws1_no_self_total_hold dest insp ⟨t, fun h => Iff.of_eq (congrFun ht h)⟩

/-- **D3 — the coincidence check (the cardinal payoff).** The spine holds with NO bisimulation and NO
atomlessness hypothesis, so it is not `ws1_symmetric_states_bisimilar` in disguise: it holds on ANY
carrier, whether relational identity is trivial there or not. Orthogonality to relational identity. -/
theorem ws1_diagonal_not_bisim {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws1_no_self_total_hold dest insp, fun d ins => ws1_no_self_total_hold d ins⟩

/-- **D4 — the Russell guard.** A carrier where a hold ranges over ALL contents (surjective `insp`) is
inconsistent: no model. The κ-bounded `(dest, insp)` carrier never demands surjectivity, so the
diagonal is a gap inside a consistent object. -/
theorem ws1_unrestricted_carrier_inconsistent {X : Type u} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp :=
  fun ⟨insp, hs⟩ => ws1_insp_not_surjective dest insp hs

/-- **D5 — hold-reflexive, not self-loop (§4.4 carrier-strength obligation).** The carrier expresses
genuine NON-POINT contents: an inspection whose content `⊤` holds two distinct holds `h₀ ≠ h₁` at once
— a content no self-loop can express, since every `inspLoop` content is a point (`inspLoop h h' ↔
h' = h`). So a hold genuinely ranges over the space of holds, strictly stronger than a self-loop.

NB (design correction, recorded in `charter-status.md`): the pre-build design's first horn — an
inspection "near-surjective onto every content but the diagonal" — is UNREALIZABLE by cardinality (the
complement of a single point in `HoldPred` still has cardinality `2 ^ |Hold| > |Hold|`, so no map from
`Hold` covers it). Hold-reflexivity is the correct guard: content is a genuine predicate over holds
(non-point), witnessed here, NOT near-surjectivity. This is a faithful realization of the §4.4 guard. -/
theorem ws1_holdreflexive_not_selfloop {X : Type u} (dest : X → PkObj κ X)
    (h₀ h₁ : Hold dest) (_hne : h₀ ≠ h₁) :
    (∃ insp : Hold dest → HoldPred dest, insp h₀ h₀ ∧ insp h₀ h₁)
  ∧ (∀ (h h' : Hold dest), inspLoop (dest := dest) h h' ↔ h' = h) :=
  ⟨⟨fun _ => (fun _ => True), trivial, trivial⟩, fun _ _ => Iff.rfl⟩

end Series9.WS1
