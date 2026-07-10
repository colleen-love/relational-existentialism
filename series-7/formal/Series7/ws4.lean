/-
`series-7/formal/Series7/ws4.lean`

WS4 — **The imports catalogued: the program explained.** Series 7.

Owns: exhibiting the import MECHANISMS as forced structural drops, and reading the Import
Theorem (WS2) as their predictor. Series 6's process is the confirming negative: it kept
(1)(2)(3), refused to import, and collapsed.

Design doc: `series-7/spec/ws4-design.md`.

REVIEW RESPONSE (project-review-1.md S2/S3/R6, recorded in `charter-status.md`). Pass 1 was
right that a single plain toy (`twoLoop`) cannot witness the label/index import: `twoLoop`'s
distinction is *killed by the behavioral quotient* (both states map to Ω), a drop of ingredient
(2); the label/index import is *real in the final object* (survives the quotient), a drop of
ingredient (1). The two mechanisms are NOT the same and are no longer equated. This pass
mechanizes BOTH mechanisms on genuine (if minimal) witnesses:
* **drop (1) — the LABELLED functor.** A labelled coalgebra `labelLoop` on the NON-plain
  functor `P_κ(Q × X)` whose two atomless states are distinct AND remain distinct under the
  label-respecting bisimulation quotient (`ws4_label_survives_quotient`) — behaviorally
  identified yet plural, escaping the theorem by dropping plainness. This is the label (S4) and
  the index (S5) at their common structural minimum.
* **drop (2) — the plain non-reduction.** `twoLoop` (WS1): two atomless states on the PLAIN
  functor, bisimilar-yet-unequal — a drop of behavioral identity.

Honest scope: the full Series 4 `νLk` / Series 5 `Winf` / Series 3 weight-algebra CARRIERS are
prior art, NOT re-transcribed here; what is mechanized is the drop-(1) and drop-(2) MECHANISMS
on minimal labelled/plain witnesses. The full-carrier unification is reported Partial.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws3

universe u

namespace Series7.WS4

open Series7.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The labelled (non-plain) functor `P_κ(Q × X)` and its label-respecting bisimulation -/

/-- The **labelled** functor: successors carry a coordinate from `Q` — NOT plain `P_κ`. -/
def LkObj (κ : Cardinal.{u}) (Q X : Type u) : Type u := PkObj κ (Q × X)

/-- A **label-respecting** bisimulation: related states have matching (label, successor) pairs. -/
def IsBisimL {Q X : Type u} (dest : X → LkObj κ Q X) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ p ∈ (dest x).1, ∃ q ∈ (dest y).1, p.1 = q.1 ∧ R p.2 q.2) ∧
    (∀ q ∈ (dest y).1, ∃ p ∈ (dest x).1, p.1 = q.1 ∧ R p.2 q.2)

/-- Behavioral identity for the labelled functor: every label-bisimulation is ⊆ equality. -/
def BehaviorallyIdentifiedL {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisimL dest R → ∀ x y, R x y → x = y

/-- The **labelled self-loop witness**: state `i` self-loops carrying its own index as the
label. Lives on the NON-plain functor `P_κ(ULift Bool × ULift Bool)`. -/
noncomputable def labelLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Bool) (ULift.{u} Bool) :=
  fun i => toPk hinf {(i, i)}

@[simp] lemma labelLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (labelLoop hinf i).1 = {(i, i)} := rfl

/-! ## drop (1): the label import survives the behavioral quotient -/

/-- **The label distinction survives the label-quotient.** There is NO label-bisimulation
relating the two loops — the label distinguishes them even up to label-bisimilarity. (Contrast
`twoLoop`, whose plain distinction IS killed by a bisimulation.) So the plurality is real in the
final object: a genuine drop of ingredient (1), plainness. -/
theorem ws4_label_survives_quotient (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hforward, _⟩ := hR ⟨true⟩ ⟨false⟩ hRel
  obtain ⟨q, hq, hfst, _⟩ := hforward (⟨true⟩, ⟨true⟩) (by rw [labelLoop_val]; exact rfl)
  rw [labelLoop_val, Set.mem_singleton_iff] at hq
  subst hq
  exact absurd hfst (by decide)

/-- **The labelled world is behaviorally identified (2) and plural (4) and atomless (3) — on
the non-plain functor.** So it escapes the Import Theorem exactly by dropping (1). Every
label-bisimulation is ⊆ equality (the label pins each state), and the two loops are distinct
and each relates to something. -/
theorem ws4_labels_are_import (hinf : ℵ₀ ≤ κ) :
    BehaviorallyIdentifiedL (labelLoop hinf)
  ∧ ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
  ∧ (∀ i, (labelLoop hinf i).1 ≠ ∅) := by
  refine ⟨?_, by decide, ?_⟩
  · intro R hR a b hRel
    by_contra hab
    obtain ⟨hforward, _⟩ := hR a b hRel
    obtain ⟨q, hq, hfst, _⟩ := hforward (a, a) (by rw [labelLoop_val]; exact rfl)
    rw [labelLoop_val, Set.mem_singleton_iff] at hq
    subst hq
    exact hab hfst
  · intro i; rw [labelLoop_val]; exact (Set.singleton_ne_empty _)

/-! ## drop (2): the plain non-reduction (twoLoop), distinct from drop (1) -/

/-- **The plain non-reduction analogue.** `twoLoop`'s two atomless states are distinct yet
bisimilar on the PLAIN functor (a drop of behavioral identity (2)) — the distinction IS killed
by the behavioral quotient (both map to Ω). This is a DIFFERENT mechanism from the label import
above and is not equated with it. -/
theorem ws4_toy_loop_is_drop2 (hinf : ℵ₀ ≤ κ) :
    (∀ i, SHNE (twoLoop hinf) i)
  ∧ ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
  ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨twoLoop_HNE hinf, by decide, ⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩⟩

/-- **S5 — levels are the label import via an index.** The tower's level-index is a label: the
SAME drop-(1) mechanism (`ws4_labels_are_import`), the index behaving as the labelled
coordinate. The full Series 5 tower colimit `Winf` is prior art, not re-transcribed; the
structural drop is witnessed here. -/
theorem ws4_levels_are_import (hinf : ℵ₀ ≤ κ) :
    BehaviorallyIdentifiedL (labelLoop hinf) ∧ ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩) :=
  ⟨(ws4_labels_are_import hinf).1, by decide⟩

/-- **The capstone — the program explained.** (a) the drop-(1) import mechanism is witnessed
(the label survives the quotient); (b) the drop-(2) non-reduction is witnessed (`twoLoop`); (c)
the Import Theorem predicts the drop — plurality on a plain coalgebra forces dropping behavioral
identity or atomlessness (`ws2_plurality_requires_drop`); (d) Series 6 is the confirmation — it
refused the drop, kept (1)(2)(3), and collapsed (`ws1_productive_unique`). Honest scope: the S3
weight carrier and the full S4/S5 carriers are prior art, not re-transcribed. -/
theorem ws4_program_explained (hinf : ℵ₀ ≤ κ) :
    (BehaviorallyIdentifiedL (labelLoop hinf) ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)  -- drop (1)
  ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)                                                   -- drop (2)
  ∧ (∀ (a b : ULift.{u} Bool), a ≠ b →
       ¬ (BehaviorallyIdentified (twoLoop hinf) ∧ (∀ i, SHNE (twoLoop hinf) i)))                          -- theorem predicts
  ∧ (∀ t : Proc κ, Productive t → t = omegaProc hinf) :=                                                  -- S6 collapsed
  ⟨⟨(ws4_labels_are_import hinf).1, ws4_label_survives_quotient hinf⟩,
   ⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩,
   fun a b hab => Series7.WS2.ws2_plurality_requires_drop (twoLoop hinf) ⟨a, b, hab⟩,
   fun t ht => ws1_productive_unique hinf t ht⟩

end Series7.WS4
