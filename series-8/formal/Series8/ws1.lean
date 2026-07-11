/-
`series-8/formal/Series8/ws1.lean`

WS1 — **The perspective primitive and the no-god's-eye theorem.** Series 8, the blocking spine.

This file is SELF-CONTAINED: it transcribes (re-namespaced `Series8.WS1`) the plain `P_κ` /
bisimulation machinery, the labelled/face machinery, and the collapse from Series 7 —
nothing is imported from `series-7/`, `series-4/`, or `archive/`. It fixes the carrier and the
hold primitive `x↾(x,y)` (ambient for WS2–WS6) and establishes the central negative: the node
that holds all faces symmetrically is a recoverable-face coalgebra, hence collapses to the One
by the engine, hence does not exist as a relationally-identified node.

Design doc: `series-8/spec/ws1-design.md`; shared objects `series-8/spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Mathlib

universe u

namespace Series8.WS1

open Cardinal

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (transcribed from Series 7 `ws1`) -/

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

/-- **Behavioral identity = no imported atom** (README §2). -/
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

lemma twoLoop_true_bisim (hinf : ℵ₀ ≤ κ) :
    IsBisim (twoLoop hinf) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' _; exact ⟨y, by rw [twoLoop_val]; exact rfl, trivial⟩
  · intro y' _; exact ⟨x, by rw [twoLoop_val]; exact rfl, trivial⟩

/-! ## The engine and the static collapse (transcribed) -/

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

/-- **The Import Theorem (static form).** A plain, behaviorally-identified, atomless coalgebra is a
subsingleton. -/
theorem ws2_import_theorem_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ⟨fun x y => ws1_recovers_static dest hbehav x y (hatom x) (hatom y)⟩

/-! ## The labelled (non-plain) functor and the recoverable/free face test (transcribed from `ws4`) -/

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

/-- **A recoverable label is NOT an import.** -/
theorem ws4_recoverable_not_import {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (x y : X)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
    ∃ R, IsBisimL dest R ∧ R x y :=
  let ⟨R, hR, hxy⟩ := h
  ⟨R, hrec R hR, hxy⟩

/-- **The recoverable-label collapse (the engine of the spine).** A recoverable label imports
nothing, so behavioral identity on the labels forces it on the plain relating; with atomlessness,
`ws2_import_theorem_static` collapses the carrier. -/
theorem ws4_recoverable_atomless_collapses {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X :=
  ws2_import_theorem_static (plainOf dest)
    (fun R hR x y hxy => hbehav R (hrec R hR) x y hxy) hatom

/-! ## The free label (distributed perspective) and the symmetric label (god's-eye), transcribed -/

/-- The **free directed hold**: state `i` self-loops carrying its own index as the label. -/
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

/-- **The free label is a genuine import (semantic test).** Plain-bisimilar yet no label-bisimulation
relates them: the direction the relating does not carry. -/
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

/-- **The symmetric (god's-eye) face witness.** Two self-loops carrying the SAME constant label — a
label that is a function of the relating, not of identity. -/
noncomputable def facedLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Unit) (ULift.{u} Bool) :=
  fun i => toPk hinf {((⟨()⟩ : ULift.{u} Unit), i)}

@[simp] lemma facedLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (facedLoop hinf i).1 = {((⟨()⟩ : ULift.{u} Unit), i)} := rfl

/-- **The symmetric face is recoverable.** A constant, identity-independent label adds no constraint. -/
theorem ws4_facedLoop_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (facedLoop hinf) := by
  intro R _ x y hxy
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [facedLoop_val, Set.mem_singleton_iff] at hp; subst hp
    exact ⟨((⟨()⟩ : ULift.{u} Unit), y), by rw [facedLoop_val]; exact rfl, rfl, hxy⟩
  · intro q hq
    rw [facedLoop_val, Set.mem_singleton_iff] at hq; subst hq
    exact ⟨((⟨()⟩ : ULift.{u} Unit), x), by rw [facedLoop_val]; exact rfl, rfl, hxy⟩

/-! ## The hold primitive `x↾(x,y)` (Series 8, holding-first — charter §3) -/

/-- **A hold `x↾(x,y)`**: `x` restricting toward its successor `y`. Holding is primitive. -/
def Hold {X : Type u} (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }

/-- **What the hold affords**: the sub-field it turns toward (Series 4's face, forced by `dest`). -/
def afford {X : Type u} (dest : X → PkObj κ X) (h : Hold dest) : Set X :=
  { z | SReaches dest h.1.2 z }

/-! ## The WS1 deliverables -/

/-- **D5 — the hold is forced.** `afford` is the unique function of `dest`; holding refines the
carrier, it does not annotate it. (Series 4 `ws1_face_forced`, transcribed.) -/
theorem ws1_hold_forced {X : Type u} (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z } :=
  ⟨afford dest, fun _ => rfl, fun _g hg => funext fun h => hg h⟩

/-- **D2 — the symmetric hold is recoverable.** The paradigm god's-eye face is recoverable. -/
theorem ws1_symmetric_hold_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (facedLoop hinf) :=
  ws4_facedLoop_recoverable hinf

/-- **D1 — the no-god's-eye collapse (the spine, Impossibility proved).** A node holding all faces
symmetrically is a recoverable-face coalgebra; atomless and behaviorally identified, it is a
subsingleton — the totality annihilates its faces. -/
theorem ws1_no_gods_eye {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X :=
  ws4_recoverable_atomless_collapses dest hrec hbehav hatom

/-- **D4 — the Impossibility, headline phrasing.** No relationally-identified god's-eye node hosts a
plurality of faces. -/
theorem ws1_no_gods_eye_node {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : ¬ (∃ x y : X, x ≠ y) := by
  haveI := ws1_no_gods_eye dest hrec hbehav hatom
  rintro ⟨x, y, hxy⟩; exact hxy (Subsingleton.elim x y)

/-- **D3 — freeness is global.** The directed hold is NOT recoverable; and the totality that would
recover all faces at once is a `ws1_no_gods_eye` node, which does not exist. -/
theorem ws1_directed_hold_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

/-! ## The god's-eye collapse and its HONEST SCOPE (series-review-3 S1 — a Partial, obstruction precise)

Three review passes flagged the same point, and pass 3 is right: the collapse below is not the
charter's *independent* dramatic annihilation of a rich totality. It is honestly reported here as a
**Partial**, with the obstruction precise, per protocol §E and charter §5.5/§9 (which pre-registered
that the all-faces node might be "only heuristically" bisimilar to the trivial loop — the sharpest
risk). The precise situation, all theorems below:

1. **A positionless node collapses — but the collapse coincides with relational identity.** `Symmetric
   dest := ∀ x y, dest x = dest y` makes all states label-bisimilar (`ws1_symmetric_states_bisimilar`),
   so `ws1_gods_eye_collapses` is behavioral identity applied to that bisimulation. The coincidence
   rule (protocol §5) FAILS here: "forced collapse" unfolds to "relational identity on a symmetric
   coalgebra." This is a genuine theorem but NOT an independent derivation of no-god's-eye from
   relational identity — it *is* relational identity, wearing the perspectival reading.

2. **No genuine multi-face symmetric totality exists to collapse (the obstruction, made a theorem).**
   On an atomless field a genuine face-distinction is FREE, never recoverable
   (`ws1_distinct_faces_atomless_not_recoverable`): a node with two states carrying genuinely distinct
   faces is not a symmetric/recoverable totality at all. So the charter's "rich all-faces symmetric
   totality" is an EMPTY class on atomless — there is nothing to collapse, because genuine plurality of
   faces forces freeness (asymmetry). The `symLoop` witness confirms it from the other side: a
   constant ≥2-face node is *not* relationally identified (`ws1_symLoop_not_behav`).

Honest status: **Impossibility proved for the recoverable/symmetric case** (`ws1_no_gods_eye`) and
**genuine plurality ⟹ free** (`ws1_distinct_faces_atomless_not_recoverable`); the charter-strength
*independent* spine (a rich totality collapsing as a fact over and above relational identity) is a
**Partial** — it provably reduces to relational identity. This does NOT hand victory to monism: the
plurality is real and distributed (WS2, `ws1_freeness_needs_two_positions`); what is not achieved is
making no-god's-eye a fact separate from the Series 7 collapse. See `charter-status.md` (pass 3) and
`ws1-design.md`. -/

/-- **The positionless property.** Every position relates identically — the strongest form of "no
asymmetry anywhere." (NB: this is `∀ x y, dest x = dest y`, all-nodes-identical, which is why the
collapse below coincides with relational identity — see the section note.) -/
def Symmetric {Q X : Type u} (dest : X → LkObj κ Q X) : Prop := ∀ x y, dest x = dest y

/-- **On a positionless coalgebra the all-true relation is a label-bisimulation** — every position
matches every other's faces (identical), so all states are label-bisimilar. -/
theorem ws1_symmetric_bisim_trivial {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) : IsBisimL dest (fun _ _ => True) := by
  intro x y _
  refine ⟨fun p hp => ⟨p, ?_, rfl, trivial⟩, fun q hq => ⟨q, ?_, rfl, trivial⟩⟩
  · rw [← hsym x y]; exact hp
  · rw [hsym x y]; exact hq

/-- **The coincidence, owned (series-review-3 S1).** On a positionless coalgebra ANY two states are
label-bisimilar. Hence the collapse below is behavioral identity applied to THIS bisimulation — not an
independent fact. This is disclosed, not hidden: the spine's honest content is relational identity. -/
theorem ws1_symmetric_states_bisimilar {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) (x y : X) : ∃ R, IsBisimL dest R ∧ R x y :=
  ⟨fun _ _ => True, ws1_symmetric_bisim_trivial dest hsym, trivial⟩

/-- **The positionless collapse (a theorem; scope: coincides with relational identity — see note).** A
positionless, relationally-identified node is a subsingleton: all its states are label-bisimilar
(`ws1_symmetric_states_bisimilar`), so behavioral identity forces them equal. Honestly this is
relational identity on a symmetric coalgebra (the coincidence rule fails), NOT the charter's
independent collapse of a rich totality — reported as a Partial in `charter-status.md`. -/
theorem ws1_gods_eye_collapses {Q X : Type u} (dest : X → LkObj κ Q X)
    (hsym : Symmetric dest) (hbehav : BehaviorallyIdentifiedL dest) : Subsingleton X :=
  ⟨fun x y => hbehav (fun _ _ => True) (ws1_symmetric_bisim_trivial dest hsym) x y trivial⟩

/-- **S1 — the ≥2-face symmetric witness (the collapse bites on a genuine multi-face totality).**
`symLoop` is the positionless node with TWO faces (labels `⟨true⟩`, `⟨false⟩`), held identically at
every position — a genuine `|Q| = 2` all-faces node, not the degenerate one-face `facedLoop`. -/
noncomputable def symLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Bool) (ULift.{u} Bool) :=
  fun _ => toPk hinf {((⟨true⟩ : ULift.{u} Bool), (⟨true⟩ : ULift.{u} Bool)),
                      ((⟨false⟩ : ULift.{u} Bool), (⟨false⟩ : ULift.{u} Bool))}

theorem ws1_symLoop_symmetric (hinf : ℵ₀ ≤ κ) : Symmetric (symLoop hinf) := fun _ _ => rfl

/-- **S1 — a symmetric ≥2-face node CANNOT host relationally-identified plurality.** Its two states
are label-bisimilar (symmetry: the all-true relation is a label-bisimulation), so behavioral identity
would force them equal — but they are distinct. Hence to carry plurality a positionless all-faces node
must DROP relational identity: the totality cannot be both all-faces-symmetric and a genuine many. -/
theorem ws1_symLoop_not_behav (hinf : ℵ₀ ≤ κ) : ¬ BehaviorallyIdentifiedL (symLoop hinf) := by
  intro hb
  exact absurd
    (hb (fun _ _ => True) (ws1_symmetric_bisim_trivial (symLoop hinf) (ws1_symLoop_symmetric hinf))
      ⟨true⟩ ⟨false⟩ trivial)
    (by decide)

/-- **S1 — the surviving plural node is NOT symmetric (the Failed condition does not arise).**
`labelLoop` (WS2's distributed perspective) has position-DEPENDENT faces: `dest ⟨true⟩ ≠ dest ⟨false⟩`.
So it is not a positionless god's-eye node — the plurality that survives is genuinely distributed
(asymmetric), never a symmetric totality that escaped collapse. -/
theorem ws1_labelLoop_not_symmetric (hinf : ℵ₀ ≤ κ) : ¬ Symmetric (labelLoop hinf) := by
  intro hsym
  have h : (labelLoop hinf ⟨true⟩).1 = (labelLoop hinf ⟨false⟩).1 :=
    congrArg Subtype.val (hsym ⟨true⟩ ⟨false⟩)
  rw [labelLoop_val, labelLoop_val] at h
  have hmem : ((⟨true⟩ : ULift.{u} Bool), (⟨true⟩ : ULift.{u} Bool)) ∈
      ({((⟨false⟩ : ULift.{u} Bool), (⟨false⟩ : ULift.{u} Bool))} :
        Set (ULift.{u} Bool × ULift.{u} Bool)) := by
    rw [← h]; exact Set.mem_singleton_iff.mpr rfl
  rw [Set.mem_singleton_iff] at hmem
  exact absurd hmem (by decide)

/-! ## Supporting facts (freeness as a distributed, two-position phenomenon) -/

/-- **Genuine face-distinctions on an atomless field are FREE, not recoverable.** The engine relates
any two atomless states by a plain bisimulation; if they are not label-bisimilar, recoverability would
upgrade that plain bisimulation to a label one — contradiction. So a plurality of faces on an atomless
field is free. -/
theorem ws1_distinct_faces_atomless_not_recoverable {Q X : Type u} (dest : X → LkObj κ Q X)
    (hatom : ∀ z, SHNE (plainOf dest) z) (x y : X)
    (hdistinct : ¬ ∃ R, IsBisimL dest R ∧ R x y) : ¬ Recoverable dest := by
  intro hrec
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim (plainOf dest) x y (hatom x) (hatom y)
  exact hdistinct ⟨R, hrec R hR, hxy⟩

/-- **Freeness is irreducibly a between-two-positions phenomenon.** `¬ Recoverable` unfolds to the
existence of a plain bisimulation that fails to be a label bisimulation — a relation `R` between
positions whose faces disagree where the plain relating identifies them. Freeness lives in the
disagreement of faces across `R`-related positions; it is never a property of one isolated node. This
is why the surviving plural node is *distributed* perspective, not a lone free totality: the free face
IS the difference between two positions' holds. -/
theorem ws1_freeness_needs_two_positions {Q X : Type u} (dest : X → LkObj κ Q X)
    (hfree : ¬ Recoverable dest) :
    ∃ R, IsBisim (plainOf dest) R ∧ ¬ IsBisimL dest R := by
  unfold Recoverable at hfree
  push_neg at hfree
  exact hfree

/-- **The ≥2-face free witness (`labelLoop`), for contrast with the symmetric collapse.** Genuinely
distinct faces, atomless, not recoverable, and (`ws1_labelLoop_not_symmetric`) NOT symmetric. -/
theorem ws1_plural_faces_free_witness (hinf : ℵ₀ ≤ κ) :
    (∀ z, SHNE (plainOf (labelLoop hinf)) z)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ ¬ Recoverable (labelLoop hinf)
  ∧ ¬ Symmetric (labelLoop hinf) :=
  ⟨labelLoop_atomless hinf, ws4_label_survives_quotient hinf,
   ws1_distinct_faces_atomless_not_recoverable (labelLoop hinf) (labelLoop_atomless hinf)
     ⟨true⟩ ⟨false⟩ (ws4_label_survives_quotient hinf),
   ws1_labelLoop_not_symmetric hinf⟩

end Series8.WS1
