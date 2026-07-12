/-
`series-11/formal/Series11/ws1.lean`

WS1 — **Finite attention, the κ-removal, and the attention-reality spine.** Series 11, the blocking spine.

This file is SELF-CONTAINED: it transcribes (re-namespaced `Series11.WS1`) the plain `P_κ` /
bisimulation machinery, the collapse engine, the labelled/import test, the Series 09/10 diagonal layer
(`insp`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free`,
`ws2_residue_is_import`), the reification section (`IsReify`, `ws1_reify_injective`), and the reification
tower and its endogenous order (`reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`,
`ws3_order_endogenous`) — nothing is imported from `series-10/`, `series-09/`, `series-08/`, `series-07/`,
`series-04/`, or `archive/`. On top of that transcribed base it adds the Series 11 primitive Series 10
lacked: **finite attention** (`FiniteAttention`, a bounded label-reading hold; `AttentionDistinguishes`,
`RealFor`), and establishes **attention-reality** (`ws1_attention_makes_real`): a finite attention
distinguishes the reified relatum WHERE THE PLAIN BISIMULATION COLLAPSES (the `ws4_free_label_is_import`
horn: `plainOf`-bisimilar but NOT label-bisimilar), and the distinction is FREE (not recoverable,
`ws4_labelLoop_not_recoverable`), routing through the diagonal residue.

**Outcome: BOOKKEEPING RE-HIT (series-review-1 S1, Phase E).** The spine `ws1_attention_makes_real` is
`ws4_free_label_is_import` — a fact about the FIXED `labelLoop` labelled coalgebra, NOT the `reifyStep`-tower
(`reify`/`reifyStep`/`towerN` occur in no attention theorem). "Attention" is Series 10's free label under a
new name: the distinction is drawn on two fixed Booleans, not on the tower's reified relata, which on the
tower bisim-embed (`Series11.WS7.ws7_tower_collapses` = Series 10's `ws2_reify_bisim_embeds`). This is
exactly the Bookkeeping re-hit the charter pre-registered as the gravest inheritance (§4.3, §5.5). Per the
§0.2a binary, the honest close is to REPORT it: the WS7 verdict is re-graded to `bookkeepingReHit` (not
`attentionEstablished`), as Series 10 re-graded ITS verdict to the negative branch. The Phase C framing
("Discharged-on-witness with the universal Partial") was the target-avoiding third theorem and is retracted.
The freeness (`ws1_attention_distinction_free`) and the residue-routing (`ws1_attention_routes_through_diagonal`)
are genuine, but about `labelLoop` / the residue — objects different from the tower — so they do not earn the
rescue. The κ-removal (WS3/WS4) survives as a genuine, separable positive.

Design doc: `series-11/spec/ws1-design.md`; shared objects `series-11/spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Mathlib

universe u

namespace Series11.WS1

open Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (transcribed from Series 10 `ws1`) -/

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

/-! ## The labelled functor and the recoverable/free import test (transcribed from Series 10 `ws1`) -/

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

/-! ## The Series 08 coincidence witness (transcribed as the negative touchstone) -/

/-- **The positionless property.** Every position relates identically. -/
def Symmetric {Q X : Type u} (dest : X → LkObj κ Q X) : Prop := ∀ x y, dest x = dest y

theorem ws1_symmetric_bisim_trivial {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) : IsBisimL dest (fun _ _ => True) := by
  intro x y _
  refine ⟨fun p hp => ⟨p, ?_, rfl, trivial⟩, fun q hq => ⟨q, ?_, rfl, trivial⟩⟩
  · rw [← hsym x y]; exact hp
  · rw [hsym x y]; exact hq

/-- **The Series 08 coincidence witness.** Kept as the negative touchstone (WS7 certifies Series 11's
payoffs do not launder through it). -/
theorem ws1_symmetric_states_bisimilar {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) (x y : X) : ∃ R, IsBisimL dest R ∧ R x y :=
  ⟨fun _ _ => True, ws1_symmetric_bisim_trivial dest hsym, trivial⟩

/-! ## The hold primitive `x↾(x,y)` (Series 08/04, holding-first — charter §3) -/

/-- **A hold `x↾(x,y)`**: `x` restricting toward its successor `y`. Holding is primitive. -/
def Hold {X : Type u} (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }

/-- **What the hold affords**: the sub-field it turns toward. -/
def afford {X : Type u} (dest : X → PkObj κ X) (h : Hold dest) : Set X :=
  { z | SReaches dest h.1.2 z }

/-! ## The hold-reflexive / diagonal layer (Series 09/10 WS1) -/

/-- A **content**: which holds a hold's complete face contains. -/
def HoldPred {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → Prop

/-- The **diagonal residue** of an inspection. Cantor/Lawvere's diagonal term. -/
def diag {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  fun h => ¬ insp h h

/-- **The self-total fixed-point equation.** -/
def SelfTotal {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := ∀ h, insp t h ↔ diag insp h

/-- A **self-loop inspection**: content is a POINT. -/
def inspLoop {X : Type u} {dest : X → PkObj κ X} : Hold dest → HoldPred dest :=
  fun h => (fun h' => h' = h)

/-- **the hold is forced (carrier hygiene).** -/
theorem ws1_hold_forced {X : Type u} (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z } :=
  ⟨afford dest, fun _ => rfl, fun _g hg => funext fun h => hg h⟩

/-- **THE DIAGONAL SPINE (Impossibility proved, independent of relational identity).** -/
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

/-- **the Russell guard.** A carrier where a hold ranges over ALL contents is inconsistent. -/
theorem ws1_unrestricted_carrier_inconsistent {X : Type u} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp :=
  fun ⟨insp, hs⟩ => ws1_insp_not_surjective dest insp hs

/-- **hold-reflexive, not self-loop.** -/
theorem ws1_holdreflexive_not_selfloop {X : Type u} (dest : X → PkObj κ X)
    (h₀ h₁ : Hold dest) (_hne : h₀ ≠ h₁) :
    (∃ insp : Hold dest → HoldPred dest, insp h₀ h₀ ∧ insp h₀ h₁)
  ∧ (∀ (h h' : Hold dest), inspLoop (dest := dest) h h' ↔ h' = h) :=
  ⟨⟨fun _ => (fun _ => True), trivial, trivial⟩, fun _ _ => Iff.rfl⟩

/-! ## The residue and its freeness (transcribed from Series 09/10 WS2) -/

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

/-! ## The reification section (transcribed from Series 10 `ws1`) -/

/-- **Reification.** A section of `dest`: the forward map of `Ω ≅ F(Ω)`. -/
def IsReify {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop :=
  ∀ s : PkObj κ X, dest (reify s) = s

/-- **`reify` is a section, injective.** -/
theorem ws1_reify_injective {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) : Function.Injective reify := by
  intro s₁ s₂ he
  have hd : dest (reify s₁) = dest (reify s₂) := by rw [he]
  rwa [h s₁, h s₂] at hd

/-- The diagonal forbids the closing top at the inspection level (charter §9, honest form). -/
theorem ws1_diagonal_forbids_closure {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp :=
  ws1_insp_not_surjective dest insp

/-! ## The reification tower and its endogenous order (transcribed from Series 10 `ws3`) -/

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

/-- **the imported-order branch refuted.** -/
theorem ws3_imported_order_refuted {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω₀ : Set X) :
    prec dest reify Ω₀ (reifyStep dest reify Ω₀)
  ∧ (∀ a b, prec dest reify a b ↔
       Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b) :=
  ⟨prec_step dest reify Ω₀, fun a b => ws3_order_endogenous dest reify a b⟩

/-! ## The Series 11 finite-attention layer (genuinely new) -/

/-- **Finite attention (README §2.6).** A hold on the labelled tower whose reading is FINITE — it holds a
bounded part of the tower and reads the label (the reified residue) the plain relating forgets. FINITUDE is
the load-bearing property: the bound the attention imposes is the finiteness of WHAT IT HOLDS, not an
imported index and not a cardinality ceiling on the tower. -/
structure FiniteAttention {Q X : Type u} (dest : X → LkObj κ Q X) : Type u where
  focus    : X
  reads    : Set X
  fin      : reads.Finite
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z

/-- **What an attention distinguishes.** `x` and `y` are merged by the plain quotient (the collapse engine
is blind) but kept apart by every label-bisimulation (the reader distinguishes) — the
`ws4_free_label_is_import` shape. This is the reader that is NOT the plain quotient. -/
def AttentionDistinguishes {Q X : Type u} (dest : X → LkObj κ Q X) (x y : X) : Prop :=
  (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)

/-- **Real for an attention.** `x` is real for `att` iff `att` distinguishes it from a plain-bisimilar
neighbor it reads — the reified relatum the plain engine merges but the reader holds apart. -/
def RealFor {Q X : Type u} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) (x : X) : Prop :=
  ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y

/-- **D1 — THE SPINE — reported BOOKKEEPING RE-HIT (series-review-1 S1).** The term IS
`ws4_free_label_is_import`: a fact about the FIXED `labelLoop` coalgebra (`⟨true⟩` vs `⟨false⟩` are
`plainOf`-bisimilar but not label-bisimilar). `reify`/`reifyStep`/`towerN` do NOT occur — the distinction
is drawn on two fixed Booleans, NOT on the reification tower's reified relata, which on the tower bisim-embed
(`Series11.WS7.ws7_tower_collapses`). So "attention makes real" is Series 10's `labelLoop` free-label fact
relabelled: **Bookkeeping re-hit**, the gravest inheritance the charter pre-registered (§4.3, §5.5), the
attempt honestly reported (not "Discharged-on-witness / universal Partial" — that framing was the Phase C
over-claim §0.2a forbids). The WS7 verdict is `bookkeepingReHit`. The freeness (`ws1_attention_distinction_free`)
and the diagonal residue-routing (`ws1_attention_routes_through_diagonal`) are genuine facts about `labelLoop`
/ the residue respectively, but on objects DIFFERENT from the tower, so they do not earn the rescue. -/
theorem ws1_attention_makes_real (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D2 — the distinction is FREE.** Not recoverable from the plain relating: an import (the self's act),
not a coordinate stamped from outside. -/
theorem ws1_attention_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

/-- **D3 — routing through the diagonal.** The label the attention reads is the residue `diag insp`; its
freeness is the residue's, and recovery reconstructs a self-total hold. The tie between the label and
`diag insp` is interpretive (the machine-checked content is residue-freeness, `insp` only), flagged not
hidden, as Series 10 disclosed for `ws1_free_reification`. -/
theorem ws1_attention_routes_through_diagonal {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp

/-- **D4 — attention is not the plain quotient (the Bookkeeping-re-hit guard).** A pair merged by the plain
quotient but kept apart by attention — the reader is genuinely not the plain bisimulation. -/
theorem ws1_attention_not_plain_quotient (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift.{u} Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y) :=
  ⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩

/-- **D5 — the κ-removal, re-checked (§2.7).** The diagonal bound uses NO κ; the collapse engine and (NL)
hold for all large κ. No result relies on small κ. The residual carrier branching-κ is disclosed as the
section's existence condition (WS5/WS7's verdict), not used here. -/
theorem ws1_kappa_free_recheck {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (reify : PkObj κ X → X) (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ x y, SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y)
  ∧ SHNE dest (reify s) :=
  ⟨ws1_no_self_total_hold dest insp, fun x y hx hy => ws1_atomless_bisim dest x y hx hy,
   ws3_reify_preserves_SHNE dest reify h s hs hsucc⟩

/-- **D6 — the unification seed.** A finite attention IS a finite hold; the universal equivalence is WS6's. -/
theorem ws1_attention_is_finite_hold {Q X : Type u} (dest : X → LkObj κ Q X)
    (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ⟨att.fin, att.grounded.2⟩

end Series11.WS1
