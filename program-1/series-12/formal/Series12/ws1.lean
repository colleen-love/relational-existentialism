/-
`series-12/formal/Series12/ws1.lean`

WS1 - The opening and the coincidence. Series 12, the blocking workstream.

This file is SELF-CONTAINED. It transcribes (re-namespaced `Series12.WS1`) the plain `P_κ` /
bisimulation machinery and the collapse engine, the Series 07 import theorem (`ws2_import_theorem`,
`ws3_atomless_distinct_is_import`), the labelled/import test (`Recoverable`, `plainOf`, `labelLoop`,
`ws4_labelLoop_not_recoverable`), the diagonal layer and free residue (`ws1_no_self_total_hold`,
`ws1_diagonal_not_bisim`, `residue`, `ws2_residue_free`), the reification section (`IsReify`,
`ws1_reify_injective`), and the reification tower and its endogenous order (`reifyStep`, `towerN`,
`prec`, `ws3_reify_preserves_SHNE`, `ws3_order_endogenous`). Nothing is imported across series; the one
prior result presupposed and named is Series 07.

On that transcribed base it adds the Series 12 primitives of WS1: the opening shape `Opening`, and the
two halves and the shape-coincidence, keeping FORCED-FOR-ALL (the residue, `ws2_residue_free`, for every
inspection) distinct from EXISTS-SATISFYING (the imports, `ws4_labelLoop_not_recoverable`, a witnessed
import), asserting coincidence OF SHAPE only, never object-identity (`ws1_coincidence_not_identity`).

Design doc: `series-12/spec/ws1-design.md`; shared objects `series-12/spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Mathlib

universe u

namespace Series12.WS1

open Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (transcribed) -/

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
coalgebra is a subsingleton: without an import, the One. -/
theorem ws2_import_theorem_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ⟨fun x y => ws1_recovers_static dest hbehav x y (hatom x) (hatom y)⟩

/-- **The Import Theorem (Series 07, headline).** No plain coalgebra is behaviorally-identified,
atomless, and plural. -/
theorem ws2_import_theorem {X : Type u} (dest : X → PkObj κ X) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y)) := by
  rintro ⟨hb, ha, x, y, hxy⟩
  haveI := ws2_import_theorem_static dest hb ha
  exact hxy (Subsingleton.elim x y)

/-! ## The trichotomy pieces (Series 07 WS3, the required half of the coincidence) -/

/-- **A LEAF** - a descent difference: one of the two states bottoms out (an atom). -/
def LeafDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  ¬ SHNE dest x ∨ ¬ SHNE dest y

/-- **An IMPORT** - a coordinate invisible to relating: the states are bisimilar yet unequal. -/
def ImportDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y

/-- **The dichotomy.** Any distinction on a single plain coalgebra is a leaf or an import. -/
theorem ws3_dichotomy {X : Type u} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y := by
  by_cases hx : SHNE dest x
  · by_cases hy : SHNE dest y
    · exact Or.inr ⟨ws1_atomless_bisim dest x y hx hy, h⟩
    · exact Or.inl (Or.inr hy)
  · exact Or.inl (Or.inl hx)

/-- **A genuine atomless distinction is an import (Series 07).** Ruling out the leaf forces the import. -/
theorem ws3_atomless_distinct_is_import {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (h : x ≠ y) (hnl : ¬ LeafDiff dest x y) : ImportDiff dest x y := by
  simp only [LeafDiff, not_or, not_not] at hnl
  obtain ⟨hx, hy⟩ := hnl
  exact ⟨ws1_atomless_bisim dest x y hx hy, h⟩

/-! ## The labelled functor and the recoverable / free import test (transcribed) -/

/-- The **labelled** functor: successors carry a coordinate from `Q`, NOT plain `P_κ`. -/
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

/-! ## The hold primitive and the diagonal layer (transcribed) -/

/-- **A hold `x↾(x,y)`**: `x` restricting toward its successor `y`. -/
def Hold {X : Type u} (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }

/-- **What the hold affords**: the sub-field it turns toward. -/
def afford {X : Type u} (dest : X → PkObj κ X) (h : Hold dest) : Set X :=
  { z | SReaches dest h.1.2 z }

/-- A **content**: a predicate on holds. -/
def HoldPred {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → Prop

/-- The **diagonal residue** of an inspection. Cantor/Lawvere's diagonal term. -/
def diag {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  fun h => ¬ insp h h

/-- **The self-total fixed-point equation.** -/
def SelfTotal {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := ∀ h, insp t h ↔ diag insp h

/-- **THE DIAGONAL SPINE (Impossibility, independent of relational identity).** -/
theorem ws1_no_self_total_hold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t := by
  rintro ⟨t, ht⟩
  have h : insp t t ↔ ¬ insp t t := ht t
  have np : ¬ insp t t := fun hp => h.mp hp hp
  exact np (h.mpr np)

/-- **the Cantor form.** No inspection surjects onto the space of contents. -/
theorem ws1_insp_not_surjective {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (diag insp)
  exact ws1_no_self_total_hold dest insp ⟨t, fun h => Iff.of_eq (congrFun ht h)⟩

/-- **the coincidence check.** The spine holds with NO bisimulation and NO atomlessness hypothesis. -/
theorem ws1_diagonal_not_bisim {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws1_no_self_total_hold dest insp, fun d ins => ws1_no_self_total_hold d ins⟩

/-! ## The residue and its freeness (transcribed) -/

/-- The **residue** of an inspection: the diagonal content no hold realises. -/
def residue {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  diag insp

/-- The residue is **recoverable** iff some hold's content realises it. -/
def ResidueRecoverable {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ h, insp h = residue insp

/-- **plurality from one position.** The residue is distinct from every hold's content. -/
theorem ws2_residue_distinct {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ∀ h, insp h ≠ residue insp := by
  intro h hh
  exact ws1_no_self_total_hold dest insp ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

/-- **the residue is free.** -/
theorem ws2_residue_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ResidueRecoverable insp := by
  rintro ⟨h, hh⟩
  exact ws2_residue_distinct dest insp h hh

/-- **freeness is an import; recoverability ⇒ self-total hold.** -/
theorem ws2_residue_is_import {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) := by
  refine ⟨ws2_residue_free dest insp, ?_⟩
  rintro ⟨h, hh⟩
  exact ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

/-! ## The reification section (transcribed) -/

/-- **Reification.** A section of `dest`: the forward map of `Ω ≅ F(Ω)`. -/
def IsReify {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop :=
  ∀ s : PkObj κ X, dest (reify s) = s

/-- **`reify` is a section, injective.** -/
theorem ws1_reify_injective {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) : Function.Injective reify := by
  intro s₁ s₂ he
  have hd : dest (reify s₁) = dest (reify s₂) := by rw [he]
  rwa [h s₁, h s₂] at hd

/-! ## The reification tower and its endogenous order (transcribed) -/

/-- **One reification step.** Adjoin every relatum reifiable from a non-empty κ-bounded pattern. -/
def reifyStep {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }

lemma reifyStep_superset {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) :
    Ωα ⊆ reifyStep dest reify Ωα := fun _ hx => Or.inl hx

lemma reify_mem_reifyStep {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    {Ωα : Set X} {s : PkObj κ X} (hsub : s.1 ⊆ Ωα) (hne : s.1 ≠ ∅) :
    reify s ∈ reifyStep dest reify Ωα := Or.inr ⟨s, hsub, hne, rfl⟩

/-- A concrete ℕ-indexed iterate of the tower. -/
def towerN {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) : ℕ → Set X
  | 0 => Ω₀
  | n + 1 => reifyStep dest reify (towerN dest reify Ω₀ n)

/-- **THE TOWER ORDER, derived once.** `prec a b` iff `b` is reached by a reification sequence from `a`. -/
def prec {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Set X → Set X → Prop :=
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)

lemma prec_step {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) :
    prec dest reify Ωα (reifyStep dest reify Ωα) :=
  Relation.ReflTransGen.single rfl

/-- **(NL) reification preserves `SHNE`.** A reified non-empty hereditarily-non-empty pattern yields a
hereditarily-non-empty relatum: a full relatum with its own relating, never a leaf. -/
theorem ws3_reify_preserves_SHNE {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) := by
  intro v hv
  rcases Relation.ReflTransGen.cases_head hv with heq | ⟨w, hw, hwv⟩
  · subst heq; rw [h s]; exact hs
  · rw [h s] at hw
    exact hsucc w hw v hwv

theorem ws3_tower_step_subset {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X)
    (n : ℕ) : towerN dest reify Ω₀ n ⊆ towerN dest reify Ω₀ (n + 1) :=
  reifyStep_superset dest reify _

theorem ws3_tower_monotone {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X)
    {m n : ℕ} (hmn : m ≤ n) : towerN dest reify Ω₀ m ⊆ towerN dest reify Ω₀ n := by
  induction hmn with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (ws3_tower_step_subset dest reify Ω₀ _)

/-- **the ONE endogenous order.** `prec` IS the reification-step closure (`Iff.rfl`). -/
theorem ws3_order_endogenous {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (a b : Set X) :
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b := Iff.rfl

/-! ## THE OPENING (Series 12, WS1) - the shape `¬ Recoverable`, defined once -/

/-- **The opening (shape).** Relative to a notion `realizable : C → Prop` of what the plain relating can
force, a candidate `c : C` inhabits the opening iff it is NOT recoverable: `¬ realizable c`. Parametric
in BOTH the candidate type `C` and the recoverability notion `realizable`, so the residue (with
`realizable := ResidueRecoverable`) and the imports (with `realizable := Recoverable`) inhabit the same
shape by SEPARATE quantifiers, never by object-identity (they do not even share a type). -/
def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c

/-- **D1 - THE TWO HALVES.** (Required, Series 07) a genuine atomless distinction is an import.
(Generated, the diagonal) the residue is free for every inspection, and the diagonal is independent of
relational identity. -/
theorem ws1_two_halves {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ x y : X, x ≠ y → ¬ LeafDiff dest x y → ImportDiff dest x y)
  ∧ (¬ ResidueRecoverable insp)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t) :=
  ⟨fun x y h hnl => ws3_atomless_distinct_is_import dest x y h hnl,
   ws2_residue_free dest insp, (ws1_diagonal_not_bisim dest insp).2⟩

/-- **D2 - THE SHAPE-COINCIDENCE.** Both the residue and the imports inhabit the opening shape
`¬ Recoverable`, from OPPOSITE quantifier directions: the residue FORCED-FOR-ALL (non-recoverable for
EVERY inspection), the imports EXISTS-SATISFYING (there EXISTS a non-recoverable labelled distinction).
Shape-identity, stated with the quantifiers distinct; NEVER object-identity. -/
theorem ws1_shape_coincidence (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
        Opening (@ResidueRecoverable κ X dest) insp)
  ∧ (Opening (@Recoverable κ (ULift.{u} Bool) (ULift.{u} Bool)) (labelLoop hinf)) :=
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws4_labelLoop_not_recoverable hinf⟩

/-- **D3 - SHAPE, NOT IDENTITY.** Shared non-recoverability under-determines identity: the opening shape
has MANY distinct inhabitants on the residue side alone (distinct free residues), so "both fail
`Recoverable`" cannot entail "same object." The coincidence is of shape; a junk label also fails it. -/
theorem ws1_coincidence_not_identity {X : Type u} (dest : X → PkObj κ X)
    (insp₁ insp₂ : Hold dest → HoldPred dest) (hne : residue insp₁ ≠ residue insp₂) :
    Opening (@ResidueRecoverable κ X dest) insp₁
  ∧ Opening (@ResidueRecoverable κ X dest) insp₂
  ∧ residue insp₁ ≠ residue insp₂ :=
  ⟨ws2_residue_free dest insp₁, ws2_residue_free dest insp₂, hne⟩

/-- **D3' - THE ANTI-CONFLATION IS NON-VACUOUS (PR1-R2).** The hypothesis of
`ws1_coincidence_not_identity` is DISCHARGED on any carrier with an inhabited `Hold`: the constant-`True`
and constant-`False` inspections both inhabit the opening (`ws2_residue_free`) yet have POINTWISE-OPPOSITE
residues (`residue (fun _ _ => True) h₀ = False`, `residue (fun _ _ => False) h₀ = True`), so distinct
inhabitants of the shape genuinely exist and shared non-recoverability provably cannot entail identity. Not
an assumed non-identity: an exhibited one. -/
theorem ws1_coincidence_not_identity_witness {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    ∃ insp₁ insp₂ : Hold dest → HoldPred dest,
        Opening (@ResidueRecoverable κ X dest) insp₁
      ∧ Opening (@ResidueRecoverable κ X dest) insp₂
      ∧ residue insp₁ ≠ residue insp₂ := by
  refine ⟨fun _ _ => True, fun _ _ => False, ws2_residue_free dest _, ws2_residue_free dest _, ?_⟩
  intro hcontra
  have hc : False = True := by
    simpa only [residue, diag, not_true, not_false_iff] using congrFun hcontra h₀
  exact (Iff.of_eq hc.symm).mp trivial

end Series12.WS1
