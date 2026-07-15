/-
`series-13/formal/Series13/ws1.lean`

WS1 - The two orders (the knot). Series 13, the post-terminal coda, the blocking workstream.

This file is SELF-CONTAINED. It transcribes (re-namespaced `Series13.WS1`) the plain `P_κ` /
bisimulation machinery and the collapse engine, the Series 07 import theorem (`ws2_import_theorem`,
`ws3_atomless_distinct_is_import`), the labelled/import test (`Recoverable`, `plainOf`, `labelLoop`,
`ws4_labelLoop_not_recoverable`), the diagonal layer and free residue (`ws1_no_self_total_hold`,
`residue`, `ws2_residue_distinct`, `ws2_residue_free`), and the opening and coincidence (Series 12 WS1,
`Opening`, `ws1_shape_coincidence`, `ws1_coincidence_not_identity_witness`). Nothing is imported across
series; the two prior results presupposed and named are Series 07 and Series 12 WS1.

On that transcribed base it adds the Series 13 primitives of WS1: the ORDER ON INSPECTIONS `instLEInsp`
(by residue) and the ORDER ON LABELLED COALGEBRAS `instLELab` (residue-position covariant, reference-bit
antitone), each proved NON-TRIVIAL (`ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial`). The mint's
codomain is represented by its two self-loop labels (`Lab dest h₀`, a structure carrying `h₀` in its type
so the `Preorder` instance resolves), realized as an actual labelled coalgebra by `coalg`; this is a
faithful realization of the design's `MCar → LkObj` shape (disclosed in `charter-status.md`), keeping every
`Recoverable` fact a fact about the genuine coalgebra `coalg b`.

Design docs: `series-13/spec/ws1-design.md`, `series-13/spec/ws1-orders-design.md`; shared objects
`series-13/spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Mathlib

universe u

namespace Series13.WS1

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

/-- **A bounded singleton**, valid over ANY type (the label types are infinite, so `toPk`'s `[Finite X]`
does not apply; a singleton has cardinal `1 < κ`). -/
def pkSingleton (hinf : ℵ₀ ≤ κ) {Y : Type u} (y : Y) : PkObj κ Y := ⟨{y}, mk_singleton_lt hinf y⟩

@[simp] lemma pkSingleton_val (hinf : ℵ₀ ≤ κ) {Y : Type u} (y : Y) : (pkSingleton hinf y).1 = {y} := rfl

/-- **A bounded empty set**, over any type. -/
def pkEmpty (hinf : ℵ₀ ≤ κ) {Y : Type u} : PkObj κ Y := ⟨∅, mk_empty_lt hinf⟩

@[simp] lemma pkEmpty_val (hinf : ℵ₀ ≤ κ) {Y : Type u} : (pkEmpty hinf (Y := Y)).1 = ∅ := rfl

/-! ## Reaching, atomlessness, bisimulation (transcribed) -/

def SReaches {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  Relation.ReflTransGen (fun a b => b ∈ (dest a).1)

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

def BehaviorallyIdentified {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ (R : X → X → Prop), IsBisim dest R → ∀ x y, R x y → x = y

def hneRel {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  fun x y => SHNE dest x ∧ SHNE dest y

lemma hneRel_isBisim {X : Type u} (dest : X → PkObj κ X) : IsBisim dest (hneRel dest) := by
  rintro x y ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · intro x' hx'
    obtain ⟨y', hy'⟩ := Set.nonempty_iff_ne_empty.mpr hy.ne_empty
    exact ⟨y', hy', hx.succ hx', hy.succ hy'⟩
  · intro y' hy'
    obtain ⟨x', hx'⟩ := Set.nonempty_iff_ne_empty.mpr hx.ne_empty
    exact ⟨x', hx', hx.succ hx', hy.succ hy'⟩

theorem ws1_atomless_bisim {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y :=
  ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩

theorem ws1_recovers_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) :
    x = y := by
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim dest x y hx hy
  exact hbehav R hR x y hxy

theorem ws2_import_theorem_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ⟨fun x y => ws1_recovers_static dest hbehav x y (hatom x) (hatom y)⟩

theorem ws2_import_theorem {X : Type u} (dest : X → PkObj κ X) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y)) := by
  rintro ⟨hb, ha, x, y, hxy⟩
  haveI := ws2_import_theorem_static dest hb ha
  exact hxy (Subsingleton.elim x y)

/-! ## The trichotomy pieces (Series 07 WS3, transcribed) -/

def LeafDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  ¬ SHNE dest x ∨ ¬ SHNE dest y

def ImportDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y

theorem ws3_dichotomy {X : Type u} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y := by
  by_cases hx : SHNE dest x
  · by_cases hy : SHNE dest y
    · exact Or.inr ⟨ws1_atomless_bisim dest x y hx hy, h⟩
    · exact Or.inl (Or.inr hy)
  · exact Or.inl (Or.inl hx)

theorem ws3_atomless_distinct_is_import {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (h : x ≠ y) (hnl : ¬ LeafDiff dest x y) : ImportDiff dest x y := by
  simp only [LeafDiff, not_or, not_not] at hnl
  obtain ⟨hx, hy⟩ := hnl
  exact ⟨ws1_atomless_bisim dest x y hx hy, h⟩

/-! ## The labelled functor and the recoverable / free import test (transcribed) -/

def LkObj (κ : Cardinal.{u}) (Q X : Type u) : Type u := PkObj κ (Q × X)

def IsBisimL {Q X : Type u} (dest : X → LkObj κ Q X) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ p ∈ (dest x).1, ∃ q ∈ (dest y).1, p.1 = q.1 ∧ R p.2 q.2) ∧
    (∀ q ∈ (dest y).1, ∃ p ∈ (dest x).1, p.1 = q.1 ∧ R p.2 q.2)

def BehaviorallyIdentifiedL {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisimL dest R → ∀ x y, R x y → x = y

noncomputable def plainOf {Q X : Type u} (dest : X → LkObj κ Q X) : X → PkObj κ X :=
  fun x => PkMap κ Prod.snd (dest x)

def Recoverable {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R

-- Touchstones (`series-review-1.md` SR1-11): the Series-07 import-theorem chain (`ws2_import_theorem` …)
-- and `ws4_recoverable_not_import` are transcribed as NAMED PREMISES (charter §3), not consumed by the new
-- WS1–WS5 payoffs; kept for transcription fidelity and the AxiomCheck record, not surplus.
theorem ws4_recoverable_not_import {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (x y : X)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
    ∃ R, IsBisimL dest R ∧ R x y :=
  let ⟨R, hR, hxy⟩ := h
  ⟨R, hrec R hR, hxy⟩

noncomputable def labelLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Bool) (ULift.{u} Bool) :=
  fun i => toPk hinf {(i, i)}

@[simp] lemma labelLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (labelLoop hinf i).1 = {(i, i)} := rfl

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

lemma plainOf_labelLoop_true_bisim (hinf : ℵ₀ ≤ κ) :
    IsBisim (plainOf (labelLoop hinf)) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' _; exact ⟨y, by rw [plainOf_labelLoop_val]; exact rfl, trivial⟩
  · intro y' _; exact ⟨x, by rw [plainOf_labelLoop_val]; exact rfl, trivial⟩

theorem ws4_labelLoop_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) := by
  intro hrec
  exact ws4_label_survives_quotient hinf
    ⟨fun _ _ => True, hrec _ (plainOf_labelLoop_true_bisim hinf), trivial⟩

/-! ## The hold primitive and the diagonal layer (transcribed) -/

def Hold {X : Type u} (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }

def afford {X : Type u} (dest : X → PkObj κ X) (h : Hold dest) : Set X :=
  { z | SReaches dest h.1.2 z }

def HoldPred {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → Prop

def diag {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  fun h => ¬ insp h h

def SelfTotal {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := ∀ h, insp t h ↔ diag insp h

theorem ws1_no_self_total_hold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t := by
  rintro ⟨t, ht⟩
  have h : insp t t ↔ ¬ insp t t := ht t
  have np : ¬ insp t t := fun hp => h.mp hp hp
  exact np (h.mpr np)

theorem ws1_insp_not_surjective {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (diag insp)
  exact ws1_no_self_total_hold dest insp ⟨t, fun h => Iff.of_eq (congrFun ht h)⟩

theorem ws1_diagonal_not_bisim {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws1_no_self_total_hold dest insp, fun d ins => ws1_no_self_total_hold d ins⟩

/-! ## The residue and its freeness (transcribed) -/

def residue {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  diag insp

def ResidueRecoverable {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ h, insp h = residue insp

theorem ws2_residue_distinct {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ∀ h, insp h ≠ residue insp := by
  intro h hh
  exact ws1_no_self_total_hold dest insp ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

theorem ws2_residue_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ResidueRecoverable insp := by
  rintro ⟨h, hh⟩
  exact ws2_residue_distinct dest insp h hh

theorem ws2_residue_is_import {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) := by
  refine ⟨ws2_residue_free dest insp, ?_⟩
  rintro ⟨h, hh⟩
  exact ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

/-! ## THE OPENING (Series 12 WS1, transcribed) -/

def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c

theorem ws1_two_halves {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ x y : X, x ≠ y → ¬ LeafDiff dest x y → ImportDiff dest x y)
  ∧ (¬ ResidueRecoverable insp)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t) :=
  ⟨fun x y h hnl => ws3_atomless_distinct_is_import dest x y h hnl,
   ws2_residue_free dest insp, (ws1_diagonal_not_bisim dest insp).2⟩

theorem ws1_shape_coincidence (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
        Opening (@ResidueRecoverable κ X dest) insp)
  ∧ (Opening (@Recoverable κ (ULift.{u} Bool) (ULift.{u} Bool)) (labelLoop hinf)) :=
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws4_labelLoop_not_recoverable hinf⟩

theorem ws1_coincidence_not_identity {X : Type u} (dest : X → PkObj κ X)
    (insp₁ insp₂ : Hold dest → HoldPred dest) (hne : residue insp₁ ≠ residue insp₂) :
    Opening (@ResidueRecoverable κ X dest) insp₁
  ∧ Opening (@ResidueRecoverable κ X dest) insp₂
  ∧ residue insp₁ ≠ residue insp₂ :=
  ⟨ws2_residue_free dest insp₁, ws2_residue_free dest insp₂, hne⟩

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

/-! ## SERIES 13 - THE TWO ORDERS (the knot)

`spec/ws1-orders-design.md`. The order on inspections is by residue (A-C2); the order on labelled
coalgebras compares the residue-position covariantly and the reference-position antitonically through its
self-bit at `h₀` (B-C3). Both are proved non-trivial.  -/

/-- Content implication `⊑c`. -/
def leC {X : Type u} {dest : X → PkObj κ X} (c₁ c₂ : HoldPred dest) : Prop := ∀ h, c₁ h → c₂ h

lemma leC_refl {X : Type u} {dest : X → PkObj κ X} (c : HoldPred dest) : leC c c := fun _ hc => hc
lemma leC_trans {X : Type u} {dest : X → PkObj κ X} {a b c : HoldPred dest}
    (hab : leC a b) (hbc : leC b c) : leC a c := fun h ha => hbc h (hab h ha)

/-- **Inspections** over `dest`. -/
def Insp {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → HoldPred dest

/-- **The order on inspections**, by residue. -/
instance instLEInsp {X : Type u} {dest : X → PkObj κ X} : LE (Insp dest) where
  le insp₁ insp₂ := leC (residue insp₁) (residue insp₂)

instance instPreorderInsp {X : Type u} {dest : X → PkObj κ X} : Preorder (Insp dest) where
  le := (· ≤ ·)
  le_refl insp := leC_refl _
  le_trans a b c hab hbc := leC_trans hab hbc

/-- **The mint's codomain**, represented by its two self-loop labels, with the reference hold `h₀` carried
in the type so the `Preorder` instance (which needs `h₀`) resolves. `coalg` realizes it as a genuine
labelled coalgebra. -/
structure Lab {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) : Type u where
  cT : HoldPred dest      -- the residue-position self-loop label
  cF : HoldPred dest      -- the reference-position self-loop label

/-- **The order on labelled coalgebras.** Residue-position (`cT`) covariant by content-implication;
reference-position enters only through its self-bit at `h₀`, ANTITONE (`d₂.cF h₀ → d₁.cF h₀`). -/
instance instLELab {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} : LE (Lab dest h₀) where
  le d₁ d₂ := leC d₁.cT d₂.cT ∧ (d₂.cF h₀ → d₁.cF h₀)

instance instPreorderLab {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} : Preorder (Lab dest h₀) where
  le := (· ≤ ·)
  le_refl d := ⟨leC_refl _, fun h => h⟩
  le_trans d₁ d₂ d₃ h12 h23 := ⟨leC_trans h12.1 h23.1, fun h => h12.2 (h23.2 h)⟩

/-- The carrier of the realized coalgebra: two regions. -/
def MCar {X : Type u} (dest : X → PkObj κ X) : Type u := ULift.{u} Bool

/-- **The realization.** `Lab dest h₀` as a genuine labelled coalgebra on `MCar`: region `⟨true⟩` self-loops
broadcasting `cT`, region `⟨false⟩` self-loops broadcasting `cF`. Every `Recoverable` fact is a fact about
this coalgebra. -/
noncomputable def coalg {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    (b : Lab dest h₀) : MCar dest → LkObj κ (HoldPred dest) (MCar dest) :=
  fun i => if i.down then pkSingleton hinf (b.cT, i) else pkSingleton hinf (b.cF, i)

@[simp] lemma coalg_true {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    (b : Lab dest h₀) : (coalg hinf b ⟨true⟩).1 = {(b.cT, ⟨true⟩)} := rfl

@[simp] lemma coalg_false {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    (b : Lab dest h₀) : (coalg hinf b ⟨false⟩).1 = {(b.cF, ⟨false⟩)} := rfl

/-- The plain projection of `coalg b` is the self-loop `i ↦ {i}`, INDEPENDENT of `b` (exogeneity's ground). -/
@[simp] lemma plainOf_coalg_val {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    (b : Lab dest h₀) (i : MCar dest) : (plainOf (coalg hinf b) i).1 = {i} := by
  show Prod.snd '' (coalg hinf b i).1 = {i}
  cases i using ULift.rec with
  | up bl => cases bl <;> simp [coalg, pkSingleton]

/-! ### Non-triviality of the two orders -/

/-- **The inspection order is NON-TRIVIAL.** Not discrete: `⊤i ≤ ⊥i` with `⊤i ≠ ⊥i`. Not indiscrete:
`¬ (⊥i ≤ ⊤i)`. Certified on any inhabited-`Hold` carrier. -/
theorem ws1_orders_insp_nontrivial {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    (∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b) := by
  refine ⟨⟨(fun _ _ => True), (fun _ _ => False), ?_, ?_⟩,
          ⟨(fun _ _ => False), (fun _ _ => True), ?_⟩⟩
  · -- ⊤i ≤ ⊥i : residue ⊤i = ⊥ ⊑c ⊤ = residue ⊥i
    intro h hh
    simp only [residue, diag] at hh
    exact absurd hh (by simp)
  · -- ⊤i ≠ ⊥i at h₀
    intro he
    have := congrFun (congrFun he h₀) h₀
    exact absurd this (by simp)
  · -- ¬ (⊥i ≤ ⊤i) : residue ⊥i = ⊤ ⋢c ⊥ = residue ⊤i, fails at h₀
    intro hle
    have := hle h₀
    simp only [residue, diag] at this
    exact absurd (this (by simp)) (by simp)

/-- **The labelled order is NON-TRIVIAL, and BOTH positions are load-bearing.** (1) Not discrete:
`⟨⊥,⊥⟩ ≤ ⟨⊤,⊥⟩` and they are unequal. (2) Not indiscrete via the RESIDUE position: `¬ (⟨⊤,⊥⟩ ≤ ⟨⊥,⊥⟩)`,
`⊤ ⋢c ⊥` at `h₀`. (3) The ANTITONE REFERENCE position is load-bearing (the third conjunct): `⟨⊤,⊥⟩` and
`⟨⊤,⊤⟩` share `cT` yet `¬ (⟨⊤,⊥⟩ ≤ ⟨⊤,⊤⟩)`, the failure ISOLATED to the reference clause (`⊤ h₀ → ⊥ h₀`,
a NON-vacuous `True → False`). This is the certificate the design's `mintL`-witnessed statement intended but
could not carry (the mint lives in WS2, so WS1 cannot name it; `ws2_mint_nontrivial` certifies the mint
points, WS2). The reference witness `⟨⊤,⊤⟩` is genuinely OFF the diagonal link (`cT h₀ = ⊤ ≠ ¬ ⊤ = ¬ cF h₀`),
so this non-triviality IS the off-link-coalgebra fact the WS4 defect and the WS3 non-iso both rest on:
the reference position is non-trivial precisely because off-link coalgebras exist, which is principled,
not tuned (addresses `series-review-1.md` SR1-1, SR1-2). -/
theorem ws1_orders_lab_nontrivial {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    (∃ a b : Lab dest h₀, a ≤ b ∧ a ≠ b)
  ∧ (∃ a b : Lab dest h₀, ¬ a ≤ b)
  ∧ (∃ a b : Lab dest h₀, a.cT = b.cT ∧ ¬ a ≤ b) := by
  refine ⟨⟨⟨(fun _ => False), (fun _ => False)⟩, ⟨(fun _ => True), (fun _ => False)⟩, ⟨?_, ?_⟩, ?_⟩,
          ⟨⟨(fun _ => True), (fun _ => False)⟩, ⟨(fun _ => False), (fun _ => False)⟩, ?_⟩,
          ⟨⟨(fun _ => True), (fun _ => False)⟩, ⟨(fun _ => True), (fun _ => True)⟩, rfl, ?_⟩⟩
  · -- residue-part: ⊥ ⊑c ⊤
    intro h hh; exact absurd hh (by simp)
  · -- reference-part: ⊥ h₀ → ⊥ h₀
    intro h; exact h
  · -- ⟨⊥,⊥⟩ ≠ ⟨⊤,⊥⟩ (cT differs)
    intro he
    have : (fun _ : Hold dest => False) = (fun _ => True) := congrArg Lab.cT he
    have := congrFun this h₀
    exact absurd this (by simp)
  · -- ¬ (⟨⊤,⊥⟩ ≤ ⟨⊥,⊥⟩) : residue-part ⊤ ⊑c ⊥ fails at h₀
    rintro ⟨hcT, _⟩
    exact absurd (hcT h₀ (by simp)) (by simp)
  · -- ¬ (⟨⊤,⊥⟩ ≤ ⟨⊤,⊤⟩) : the ANTITONE reference clause fails (⊤ h₀ → ⊥ h₀, non-vacuous), same cT
    rintro ⟨_, href⟩
    exact href trivial

end Series13.WS1
