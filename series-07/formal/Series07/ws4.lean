/-
`series-07/formal/Series07/ws4.lean`

WS4 — **The imports catalogued: the program explained.** Series 07.

Owns: exhibiting the import MECHANISMS as forced structural drops, and reading the Import
Theorem (WS2) as their predictor. Series 06's process is the confirming negative: it kept
(1)(2)(3), refused to import, and collapsed.

Design doc: `series-07/spec/ws4-design.md`.

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

Honest scope: the full Series 04 `νLk` / Series 05 `Winf` / Series 03 weight-algebra CARRIERS are
prior art, NOT re-transcribed here; what is mechanized is the drop-(1) and drop-(2) MECHANISMS
on minimal labelled/plain witnesses. The full-carrier unification is reported Partial.

REVIEW RESPONSE (project-review-2/pass-2 S1/S2/R2, recorded in `charter-status.md`). The
alignment pass showed the deeper problem: "labelled" (a `Q` in the signature) is not the charter's
"import" (a coordinate NOT carried by the relating). Two things are added/disclosed below:
(i) the charter-strength SEMANTIC import test — `ws4_free_label_is_import`: the label is an import
iff the plain (label-forgetting) relating cannot recover it (plain-bisimilar states carry distinct
labels) — and `ws4_recoverable_not_import`: a recoverable label is NOT an import; (ii) the honest
FAITHFULNESS disclosure — `labelLoop` is a FREE-label witness (a genuine import); the Series 04 face
`x↾(x,y)` is an ENDOGENOUS RESTRICTION (recoverable, hence NOT an import — a leaf/faced-boundary),
and Series 04 reached plurality only by ESCALATING the restriction into a free label. So the minimal
witness and the paradigm S4 carrier are NOT the same kind; the reclassification is stated below and
routed to WS3 (the faced-boundary is the candidate fourth kind) and WS7 (the audit certifies the
free-label import, not that the S4 restriction is one).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series07.ws3

universe u

namespace Series07.WS4

open Series07.WS1 Cardinal

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
witness `(labelLoop i).1 ≠ ∅`; `ws4_label_drop_atomless` below strengthens this to full hereditary
`SHNE` on `plainOf (labelLoop)`, meeting ingredient (3) at the theorem's own strength — `Q = X =
ULift Bool` is the minimal alphabet.) -/
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

/-- **The drop-1 witness's plain relating is HEREDITARILY atomless (R1, series-review-3).** The label
self-loop's plain reduct never bottoms out — its successor set is always the singleton `{i}` — so it
meets the theorem's own ingredient (3), `SHNE`, not merely the first-level nonemptiness recorded in
`ws4_labels_are_import`. Mirrors `twoLoop_HNE`. -/
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

/-- **The drop-1 witness at full ingredient-(3) strength (R1).** The labelled world is behaviorally
identified (2), plural (4), its plain relating is HEREDITARILY atomless (3, `SHNE` on `plainOf`), and
it escapes by dropping (1): the free label survives the label quotient. This strengthens
`ws4_labels_are_import`'s first-level-nonempty conjunct to the theorem's own atomlessness, so the
drop-1 row of the catalogue meets ingredient (3) at the theorem's strength. -/
theorem ws4_label_drop_atomless (hinf : ℵ₀ ≤ κ) :
    BehaviorallyIdentifiedL (labelLoop hinf)
  ∧ ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
  ∧ (∀ i, SHNE (plainOf (labelLoop hinf)) i)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨(ws4_labels_are_import hinf).1, by decide, labelLoop_atomless hinf,
   ws4_label_survives_quotient hinf⟩

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
recoverable (a function of the relating, as the Series 04 restriction `x↾(x,y)` is), then
plain-bisimilar states are label-bisimilar: the label distinguishes nothing the relating does not.
So a recoverable label fails the import test — it is carried by the relating. (Hence the Series 04
FACE, a restriction of the relatum, is not an import; see the reclassification note below.) -/
theorem ws4_recoverable_not_import {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (x y : X)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
    ∃ R, IsBisimL dest R ∧ R x y :=
  let ⟨R, hR, hxy⟩ := h
  ⟨R, hrec R hR, hxy⟩

/-! ## The recoverable label COLLAPSES; the free label IMPORTS (pass-2 S2, mechanized)

Two theorems close the conditional. First (`ws4_recoverable_atomless_collapses`) the abstract
collapse: a recoverable label imports nothing, so if the plain relating it forgets to is
behaviorally identified and atomless, the whole labelled carrier is a subsingleton — a recoverable
label can NEVER be the atom that rescues atomless plurality. Second, the two sides are witnessed:
`labelLoop` (a FREE label, the state's own identity) is proved NOT recoverable
(`ws4_labelLoop_not_recoverable`) — a genuine import; `facedLoop` (a RESTRICTION label, a function of
the relating, the shadow of `x↾(x,y)` on collapse-equal states) is proved `Recoverable`, and its
plurality is a DROP of behavioral identity, not an import. This is the Series 04 reclassification
mechanized on minimal witnesses (the drop MECHANISMS, as elsewhere in WS4); the literal `νLk` carrier
stays prior art, but "the restriction is recoverable, hence collapses" is now a theorem, not prose. -/

/-- **The recoverable-label collapse (abstract, general).** A recoverable label imports nothing: it
turns every plain bisimulation into a label bisimulation, so behavioral identity on the labels forces
behavioral identity on the plain relating; with atomlessness, `ws2_import_theorem_static` collapses
the carrier. This is the theorem the Series 04 restriction falls under — it CANNOT rescue atomless
plurality. -/
theorem ws4_recoverable_atomless_collapses {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X :=
  Series07.WS2.ws2_import_theorem_static (plainOf dest)
    (fun R hR x y hxy => hbehav R (hrec R hR) x y hxy) hatom

/-- **A recoverable label cannot rescue plurality.** If the label is recoverable, plurality forces
dropping behavioral identity or atomlessness of the plain relating — never an import. -/
theorem ws4_recoverable_plurality_requires_drop {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (h4 : ∃ x y : X, x ≠ y) :
    ¬ (BehaviorallyIdentifiedL dest ∧ (∀ x, SHNE (plainOf dest) x)) := by
  rintro ⟨hb, ha⟩
  obtain ⟨x, y, hxy⟩ := h4
  haveI := ws4_recoverable_atomless_collapses dest hrec hb ha
  exact hxy (Subsingleton.elim x y)

/-- **The free label is NOT recoverable — a genuine import.** The plain relating cannot tell the two
loops apart (`plainOf_labelLoop_true_bisim`), yet no label-bisimulation relates them
(`ws4_label_survives_quotient`); so `Recoverable`, which would turn the former into the latter, fails.
This is the escalation `x↾(x,y) ⤳ loopState q`: the coordinate the relating does not carry. -/
theorem ws4_labelLoop_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) := by
  intro hrec
  exact ws4_label_survives_quotient hinf
    ⟨fun _ _ => True, hrec _ (plainOf_labelLoop_true_bisim hinf), trivial⟩

/-- **The faced (restriction) witness.** Two self-loops carrying the SAME constant label — a label
that is a function of the relating, not of the state's identity: the restriction `x↾(x,y)` seen on
collapse-equal states, where it cannot tell them apart. Lives on the non-plain `P_κ(Unit × Bool)`. -/
noncomputable def facedLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (ULift.{u} Unit) (ULift.{u} Bool) :=
  fun i => toPk hinf {((⟨()⟩ : ULift.{u} Unit), i)}

@[simp] lemma facedLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (facedLoop hinf i).1 = {((⟨()⟩ : ULift.{u} Unit), i)} := rfl

@[simp] lemma plainOf_facedLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (plainOf (facedLoop hinf) i).1 = {i} := by
  show Prod.snd '' ({((⟨()⟩ : ULift.{u} Unit), i)} : Set (ULift.{u} Unit × ULift.{u} Bool)) = {i}
  rw [Set.image_singleton]

/-- **The restriction label is recoverable.** A constant (identity-independent) label adds no
constraint the plain relating does not already impose: every related pair matches labels for free. -/
theorem ws4_facedLoop_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (facedLoop hinf) := by
  intro R _ x y hxy
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [facedLoop_val, Set.mem_singleton_iff] at hp; subst hp
    exact ⟨((⟨()⟩ : ULift.{u} Unit), y), by rw [facedLoop_val]; exact rfl, rfl, hxy⟩
  · intro q hq
    rw [facedLoop_val, Set.mem_singleton_iff] at hq; subst hq
    exact ⟨((⟨()⟩ : ULift.{u} Unit), x), by rw [facedLoop_val]; exact rfl, rfl, hxy⟩

lemma plainOf_facedLoop_reaches (hinf : ℵ₀ ≤ κ) (i j : ULift.{u} Bool) :
    SReaches (plainOf (facedLoop hinf)) i j → j = i := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rw [plainOf_facedLoop_val, Set.mem_singleton_iff] at hbc
      rw [hbc]; exact ih

lemma facedLoop_atomless (hinf : ℵ₀ ≤ κ) : ∀ i, SHNE (plainOf (facedLoop hinf)) i := by
  intro i v hv
  rw [plainOf_facedLoop_reaches hinf i v hv, plainOf_facedLoop_val]
  exact Set.singleton_ne_empty i

/-- The two faced states ARE label-bisimilar (the constant label matches) — so `facedLoop`'s
plurality is a drop of behavioral identity, not an import. -/
lemma facedLoop_true_bisimL (hinf : ℵ₀ ≤ κ) :
    IsBisimL (facedLoop hinf) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [facedLoop_val, Set.mem_singleton_iff] at hp; subst hp
    exact ⟨((⟨()⟩ : ULift.{u} Unit), y), by rw [facedLoop_val]; exact rfl, rfl, trivial⟩
  · intro q hq
    rw [facedLoop_val, Set.mem_singleton_iff] at hq; subst hq
    exact ⟨((⟨()⟩ : ULift.{u} Unit), x), by rw [facedLoop_val]; exact rfl, rfl, trivial⟩

/-- **The restriction collapses; only the escalation imports — the S4 reclassification, mechanized.**
Left: the faced (restriction) label is `Recoverable` and atomless, yet its two states are
label-bisimilar, so its plurality is a DROP of behavioral identity — by
`ws4_recoverable_atomless_collapses` a recoverable label is import-free and cannot rescue atomless
plurality. Right: the free label (`labelLoop`) is NOT recoverable — a genuine import. The Series 04
face is the former; Series 04's plurality is the latter (the free-label escalation). -/
theorem ws4_restriction_collapses_escalation_imports (hinf : ℵ₀ ≤ κ) :
    (Recoverable (facedLoop hinf)
      ∧ (∀ i, SHNE (plainOf (facedLoop hinf)) i)
      ∧ (∃ R, IsBisimL (facedLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
  ∧ (¬ Recoverable (labelLoop hinf)) :=
  ⟨⟨ws4_facedLoop_recoverable hinf, facedLoop_atomless hinf,
     ⟨fun _ _ => True, facedLoop_true_bisimL hinf, trivial⟩⟩,
   ws4_labelLoop_not_recoverable hinf⟩

/-! ## RECLASSIFICATION of Series 04 (project-review-2/pass-2 S2, recorded in `charter-status.md`)

Pass 2 correctly identified that the charter's paradigm import — the Series 04 face `x↾(x,y)` — is a
RESTRICTION of the relatum, hence a FUNCTION of the relata, hence `Recoverable`, hence NOT an import
by `ws4_recoverable_not_import`. It is a **leaf** (a descent boundary, drop of ingredient (3)) — or,
more precisely, a *faced boundary*: a leaf that also carries a distinguishing quality, a cell the
leaf/import dichotomy does not enumerate (a named open, see `ws3.lean`). Series 04 reached plurality
only by ESCALATING the restriction into a FREE label on `νLk` (`loopState q` with arbitrary `q`) —
replacing the non-import with an import and keeping the name. So the honest catalogue reading is:
Series 04's *faithful* restriction is a leaf that collapses; Series 04's *plurality* is a free-label
escalation, which IS a genuine import (`ws4_free_label_is_import`). The two objects are different.
This corrects `ws4_program_explained`'s "S4 dropped (1)": what dropped (1) is the escalated free
label, not the restriction. This reclassification is now MECHANIZED (above): the restriction's
collapse is `ws4_recoverable_atomless_collapses` (recoverable ⇒ import-free ⇒ cannot rescue atomless
plurality), witnessed by `facedLoop` (`ws4_facedLoop_recoverable`); the escalation's import is
`ws4_labelLoop_not_recoverable`. The literal `νLk` carrier stays prior art — what remains prose is
only the identification of the actual face with the recoverable class, a modeling claim, not the
collapse itself. -/

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
labelled coordinate. The full Series 05 tower colimit `Winf` is prior art, NOT re-transcribed — the
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
atomlessness (`ws2_plurality_requires_drop`); (d) Series 06 is the confirmation — it refused the
drop, kept (1)(2)(3), and collapsed (`ws1_productive_unique`). Honest scope (pass-2 S2): this
explains the program *for the free-label imports*; the ENDOGENOUS cases (the S4 restriction, and
possibly the S5 index if the index is endogenous to the level structure) are recoverable, hence
leaves/faced-boundaries not imports — Series 04's plurality is a free-label ESCALATION of its
restriction, reclassified above. The full `νLk`/`Winf`/weight carriers are prior art. -/
theorem ws4_program_explained (hinf : ℵ₀ ≤ κ) :
    (BehaviorallyIdentifiedL (labelLoop hinf) ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)  -- drop (1)
  ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)                                                   -- drop (2)
  ∧ (∀ (a b : ULift.{u} Bool), a ≠ b →
       ¬ (BehaviorallyIdentified (twoLoop hinf) ∧ (∀ i, SHNE (twoLoop hinf) i)))                          -- theorem predicts
  ∧ (∀ t : Proc κ, Productive t → t = omegaProc hinf) :=                                                  -- S6 collapsed
  ⟨⟨(ws4_labels_are_import hinf).1, ws4_label_survives_quotient hinf⟩,
   ⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩,
   fun a b hab => Series07.WS2.ws2_plurality_requires_drop (twoLoop hinf) ⟨a, b, hab⟩,
   fun t ht => ws1_productive_unique hinf t ht⟩

/-! ## SUBSET-OF-A-RESTRICTION: does the collapse eat a distinction with no atom in it?

A probe of the tightness of `ws2_import_theorem`'s `atomless` hypothesis. A restriction `x↾(x,y)` is
recoverable and collapses; a free tag `q` is an atom and imports. A **subset of a restriction** sits
between: its material is entirely endogenous (made of the relata), so there is no atom in the
material. The question is whether the SELECTION of which sub-part to expose is fixed by the relating
(Case A) or free per state (Case B).

The engine `ws1_atomless_bisim` decides it, and the deciding fact is that atomlessness makes ALL
states plainOf-bisimilar. So the selection has nowhere to hide: either it agrees across that
bisimulation (Case A — collapses) or it does not (Case B — then it is a coordinate the relating does
not carry, i.e. an import, no matter that its values are endogenous subsets). The atom, when Case B
survives, is not in the material but in the free CHOOSING. There is no third option. -/

/-- **Case A engine — a relating-determined selection cannot distinguish (atomless + recoverable).**
On an atomless recoverable carrier every pair of states is label-bisimilar: `ws1_atomless_bisim`
already relates them plainly, and recoverability lifts that to the labels. A subset chosen by the
relating exposes nothing new; with behavioral identity this is the collapse. -/
theorem ws4_atomless_recoverable_all_bisimL {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hatom : ∀ x, SHNE (plainOf dest) x) (x y : X) :
    ∃ R, IsBisimL dest R ∧ R x y := by
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim (plainOf dest) x y (hatom x) (hatom y)
  exact ⟨R, hrec R hR, hxy⟩

/-- **Case B decisive — on an atomless carrier, any surviving label distinction IS an import.**
If two states are not label-bisimilar yet the carrier is atomless, `ws1_atomless_bisim` makes them
plainOf-bisimilar, so recoverability would force a label-bisimulation between them — contradiction.
Hence the carrier is not recoverable: the distinction is a coordinate the relating does not carry
(§4.1), an import — regardless of what the label is MADE of. Atomlessness is exactly what forbids a
non-importing per-state distinction; the hypothesis is tight. -/
theorem ws4_atomless_label_distinction_imports {Q X : Type u} (dest : X → LkObj κ Q X)
    (hatom : ∀ x, SHNE (plainOf dest) x) (x y : X)
    (hsurv : ¬ ∃ R, IsBisimL dest R ∧ R x y) : ¬ Recoverable dest := by
  intro hrec
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim (plainOf dest) x y (hatom x) (hatom y)
  exact hsurv ⟨R, hrec R hR, hxy⟩

/-! ### The concrete Case B carrier: labels are literal subsets of the state space -/

/-- The exposed sub-part at state `i`: the singleton `{i}` — a subset of the endogenous state space
(the "restriction material"), NOT an element of an external alphabet. Distinct states expose distinct
sub-parts (`{⟨true⟩} ≠ {⟨false⟩}`), a free per-state selection over fully endogenous material. -/
def subsetLabel (i : ULift.{u} Bool) : Set (ULift.{u} Bool) := {i}

/-- **Case B carrier.** Two atomless self-loops whose labels are honest subsets of the state space,
freely chosen per state. Lives on the non-plain `P_κ(𝒫(Bool) × Bool)`. -/
noncomputable def subsetLoop (hinf : ℵ₀ ≤ κ) :
    ULift.{u} Bool → LkObj κ (Set (ULift.{u} Bool)) (ULift.{u} Bool) :=
  fun i => toPk hinf {(subsetLabel i, i)}

@[simp] lemma subsetLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (subsetLoop hinf i).1 = {(subsetLabel i, i)} := rfl

@[simp] lemma plainOf_subsetLoop_val (hinf : ℵ₀ ≤ κ) (i : ULift.{u} Bool) :
    (plainOf (subsetLoop hinf) i).1 = {i} := by
  show Prod.snd '' ({(subsetLabel i, i)} : Set (Set (ULift.{u} Bool) × ULift.{u} Bool)) = {i}
  rw [Set.image_singleton]

lemma plainOf_subsetLoop_true_bisim (hinf : ℵ₀ ≤ κ) :
    IsBisim (plainOf (subsetLoop hinf)) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' _; exact ⟨y, by rw [plainOf_subsetLoop_val]; exact rfl, trivial⟩
  · intro y' _; exact ⟨x, by rw [plainOf_subsetLoop_val]; exact rfl, trivial⟩

lemma plainOf_subsetLoop_reaches (hinf : ℵ₀ ≤ κ) (i j : ULift.{u} Bool) :
    SReaches (plainOf (subsetLoop hinf)) i j → j = i := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rw [plainOf_subsetLoop_val, Set.mem_singleton_iff] at hbc
      rw [hbc]; exact ih

lemma subsetLoop_atomless (hinf : ℵ₀ ≤ κ) : ∀ i, SHNE (plainOf (subsetLoop hinf)) i := by
  intro i v hv
  rw [plainOf_subsetLoop_reaches hinf i v hv, plainOf_subsetLoop_val]
  exact Set.singleton_ne_empty i

/-- The distinction survives at the label level: no label-bisimulation relates the two states,
because the exposed sub-parts `{⟨true⟩}` and `{⟨false⟩}` are different subsets. -/
theorem subsetLoop_survives (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (subsetLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hforward, _⟩ := hR ⟨true⟩ ⟨false⟩ hRel
  obtain ⟨q, hq, hfst, _⟩ :=
    hforward (subsetLabel ⟨true⟩, ⟨true⟩) (by rw [subsetLoop_val]; exact rfl)
  rw [subsetLoop_val, Set.mem_singleton_iff] at hq
  subst hq
  dsimp only [subsetLabel] at hfst
  exact absurd (Set.singleton_injective hfst) (by decide)

/-- **The verdict on subset-of-a-restriction (Case B): it SURVIVES, but as an import — no
counterexample.** The two states are atomless (no leaf) and plainOf-bisimilar, and their labels are
honest subsets of the state space (`subsetLabel`, no external tag); yet no label-bisimulation relates
them, so the plurality survives. By `ws4_atomless_label_distinction_imports` the carrier is therefore
NOT recoverable — the free selection is a coordinate the relating does not carry, an import. The atom
is not in the endogenous MATERIAL but in the free CHOOSING. So atomless plurality still bought an
import; `ws2_import_theorem`'s hypothesis is tight (and this is not in its scope — it is labelled),
and the recoverable-collapse `ws4_recoverable_atomless_collapses` still holds (this carrier is not
recoverable). -/
theorem ws4_subset_selection_survives_as_import (hinf : ℵ₀ ≤ κ) :
    (∀ i, SHNE (plainOf (subsetLoop hinf)) i)                          -- atomless: no leaf
  ∧ (∃ R, IsBisim (plainOf (subsetLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)    -- plainOf-bisimilar
  ∧ (¬ ∃ R, IsBisimL (subsetLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)           -- survives at label level
  ∧ (¬ Recoverable (subsetLoop hinf)) :=                               -- the survival IS an import
  ⟨subsetLoop_atomless hinf,
   ⟨fun _ _ => True, plainOf_subsetLoop_true_bisim hinf, trivial⟩,
   subsetLoop_survives hinf,
   ws4_atomless_label_distinction_imports (subsetLoop hinf)
     (subsetLoop_atomless hinf) ⟨true⟩ ⟨false⟩ (subsetLoop_survives hinf)⟩

/-! ## CAPSTONE: separating atomless histories forces an exogenous distinguisher —
     a given (atom) or a choice (will)

The whole thread lands here. `ws1_productive_unique` gives EQUALITY, not mere bisimilarity: any two
atomless (productive) histories are the SAME thread, Ω. So any `att : Proc κ → Q` — attention as a
function of the history, however dynamic — returns the same value on both; a function cannot separate
equal inputs. Hence to separate two atomless histories the separator must read something the histories
do not contain: an argument exogenous to the relating.

To the FORMALISM that exogenous argument is a coordinate not carried by the relating — the §4.1
footprint of an import. But the footprint is all a proof can see, and two philosophically opposite
things leave the same one: a **given** (a pre-existing atom, moved in) and a **choice** (a distinction
freely originated). Type theory has no predicate for "freely chosen rather than given"; it proves only
that the separator is exogenous and is silent on which. That silence is the result, not a gap.

Read as the Parmenides collapse generalized: a groundless, atomless, faithfully-relational world that
is DETERMINED is the One (`ws1_productive_unique` — the determined process is Ω; Series 06's "failure"
seen rightly). Plurality requires a distinguisher not carried by the relating — an atom OR a will. The
theorem forces the disjunction and does not decide the disjunct. The undecided disjunct — choice — is
the fourth kind the leaf/import dichotomy could never name, because to the relating a free choice and
an imported atom are the same footprint. -/
theorem att_cannot_distinguish_atomless_histories {Q : Type*} (hinf : ℵ₀ ≤ κ)
    (att : Proc κ → Q) (x y : Proc κ) (hx : Productive x) (hy : Productive y) :
    att x = att y := by
  rw [ws1_productive_unique hinf x hx, ws1_productive_unique hinf y hy]

end Series07.WS4
