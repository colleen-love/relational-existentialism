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

REVIEW RESPONSE (project-review-2/pass-2 S1/S2/R2, recorded in `charter-status.md`). The
alignment pass showed the deeper problem: "labelled" (a `Q` in the signature) is not the charter's
"import" (a coordinate NOT carried by the relating). Two things are added/disclosed below:
(i) the charter-strength SEMANTIC import test — `ws4_free_label_is_import`: the label is an import
iff the plain (label-forgetting) relating cannot recover it (plain-bisimilar states carry distinct
labels) — and `ws4_recoverable_not_import`: a recoverable label is NOT an import; (ii) the honest
FAITHFULNESS disclosure — `labelLoop` is a FREE-label witness (a genuine import); the Series 4 face
`x↾(x,y)` is an ENDOGENOUS RESTRICTION (recoverable, hence NOT an import — a leaf/faced-boundary),
and Series 4 reached plurality only by ESCALATING the restriction into a free label. So the minimal
witness and the paradigm S4 carrier are NOT the same kind; the reclassification is stated below and
routed to WS3 (the faced-boundary is the candidate fourth kind) and WS7 (the audit certifies the
free-label import, not that the S4 restriction is one).

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

/-- **The labelled world is behaviorally identified (2) and plural (4) and first-level nonempty —
on the non-plain functor.** So it escapes the Import Theorem exactly by dropping (1). Every
label-bisimulation is ⊆ equality (the label pins each state), and the two loops are distinct and
each relates to something. (Interim-review C3: ingredient (3) here is the MINIMAL first-level-nonempty
witness `(labelLoop i).1 ≠ ∅`, not a hereditary `SHNE` — enough to show the labelled functor
evades the theorem; `Q = X = ULift Bool` is the minimal alphabet.) -/
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

/-! ## The SEMANTIC import test (project-review-2/pass-2 S1/S2/R3)

Pass 2 was right: "labelled" (a `Q` in the functor signature) is NOT the charter's "import" (a
coordinate NOT carried by the relating, §4.1). The genuine test is **recoverability**: a label is
an import iff it is not determined by the plain, label-forgetting relating — iff two states the
plain relating cannot tell apart nonetheless carry different labels. `ws4_label_survives_quotient`
alone (survival under the label-MATCHING bisimulation) is the weaker, near-syntactic fact; the
charter-strength predicate is below. -/

/-- Forget the label, keep the target: the plain (label-forgetting) coalgebra. -/
noncomputable def plainOf {Q X : Type u} (dest : X → LkObj κ Q X) : X → PkObj κ X :=
  fun x => PkMap κ Prod.snd (dest x)

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

/-- **`ws4_free_label_is_import` — the charter-strength (semantic) import.** The plain,
label-forgetting relating CANNOT tell the two loops apart (they are plain-bisimilar), yet the
label DOES distinguish them (no label-bisimulation relates them). So the label carries a
distinction the relating does not determine — it is NOT recoverable — a genuine import (§4.1),
not merely "a label at all". -/
theorem ws4_free_label_is_import (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩,
   ws4_label_survives_quotient hinf⟩

/-- A label is **recoverable** if every plain (label-forgetting) bisimulation is already a
label-bisimulation — the labels add no constraint the relating does not already impose. -/
def Recoverable {Q X : Type u} (dest : X → LkObj κ Q X) : Prop :=
  ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R

/-- **`ws4_recoverable_not_import` — a recoverable label is NOT an import (S2).** If the label is
recoverable (a function of the relating, as the Series 4 restriction `x↾(x,y)` is), then
plain-bisimilar states are label-bisimilar: the label distinguishes nothing the relating does not.
So a recoverable label fails the import test — it is carried by the relating. (Hence the Series 4
FACE, a restriction of the relatum, is not an import; see the reclassification note below.) -/
theorem ws4_recoverable_not_import {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (x y : X)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
    ∃ R, IsBisimL dest R ∧ R x y :=
  let ⟨R, hR, hxy⟩ := h
  ⟨R, hrec R hR, hxy⟩

/-! ## RECLASSIFICATION of Series 4 (project-review-2/pass-2 S2, recorded in `charter-status.md`)

Pass 3 correctly identified that the charter's paradigm import — the Series 4 face `x↾(x,y)` — is a
RESTRICTION of the relatum, hence a FUNCTION of the relata, hence `Recoverable`, hence NOT an import
by `ws4_recoverable_not_import`. It is a **leaf** (a descent boundary, drop of ingredient (3)) — or,
more precisely, a *faced boundary*: a leaf that also carries a distinguishing quality, a cell the
leaf/import dichotomy does not enumerate (a named open, see `ws3.lean`). Series 4 reached plurality
only by ESCALATING the restriction into a FREE label on `νLk` (`loopState q` with arbitrary `q`) —
replacing the non-import with an import and keeping the name. So the honest catalogue reading is:
Series 4's *faithful* restriction is a leaf that collapses; Series 4's *plurality* is a free-label
escalation, which IS a genuine import (`ws4_free_label_is_import`). The two objects are different.
This corrects `ws4_program_explained`'s "S4 dropped (1)": what dropped (1) is the escalated free
label, not the restriction. The full `νLk` face is prior art, not re-transcribed. -/

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

/-- **S5 — the level-index REUSES the label mechanism.** (Interim-review C1: renamed and strengthened —
the term reuses the FULL drop-(1) label witness, including survives-quotient, and does NOT touch
`Winf`.) The tower's level-index is a label: the SAME drop-(1) mechanism, the index behaving as the
labelled coordinate. The full Series 5 tower colimit `Winf` is prior art, NOT re-transcribed — the
index-is-a-label identification is stated (prose), the structural drop witnessed via the label
mechanism. -/
theorem ws4_index_reuses_label_mechanism (hinf : ℵ₀ ≤ κ) :
    BehaviorallyIdentifiedL (labelLoop hinf)
  ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨(ws4_labels_are_import hinf).1, ws4_label_survives_quotient hinf⟩

/-- **The capstone — the program explained.** (a) the drop-(1) import mechanism is witnessed by a
genuine (semantic) FREE-label import (`ws4_free_label_is_import`: plain-bisimilar yet
label-distinct); (b) the drop-(2) non-reduction is witnessed (`twoLoop`); (c) the Import Theorem
predicts the drop — plurality on a plain coalgebra forces dropping behavioral identity or
atomlessness (`ws2_plurality_requires_drop`); (d) Series 6 is the confirmation — it refused the
drop, kept (1)(2)(3), and collapsed (`ws1_productive_unique`). Honest scope (pass-2 S2): this
explains the program *for the free-label imports*; the ENDOGENOUS cases (the S4 restriction, and
possibly the S5 index if the index is endogenous to the level structure) are recoverable, hence
leaves/faced-boundaries not imports — Series 4's plurality is a free-label ESCALATION of its
restriction, reclassified above. The full `νLk`/`Winf`/weight carriers are prior art. -/
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
