/-
`series-6/formal/ws2.lean`

WS2 — **The Static Collapse, and the forced answer.** Series 6, the intellectual spine.

Owns the motivating Impossibility: any *static* (behaviorally-identified fixed-point)
*genuinely* globally-atomless construction is a subsingleton. Every static plurality is
bought by an imported atom. Diagnoses the apparent escapes (labelled loops / an indexed
tower) as imports of a bare label/index.

Design doc: `series-6/spec/ws2-design.md`, candidate C2 (abstract `Static` +
non-circular `GenuinelyAtomless`). We take **behavioral identity as the DEFINING property
of "static"** (charter §3.1), so no terminal-coalgebra / QPF apparatus is needed: the
collapse is the maximal-hereditarily-nonempty-relation bisimulation argument run against
the assumed behavioral identity.

BUILD FINDING (routed to WS2/WS1 designs, recorded in `charter-status.md`). The
forced-answer's positive clause — "dynamism (the process `Proc`) is the escape" — is
**NOT delivered on the C2 carrier**: WS1 proves the stagewise process ALSO collapses
(`ws1_no_productive_plurality`). So on C2 the static collapse extends to the naive process;
the genuine escape is owed to the richer carrier home (metric C4 / guarded). `ws2_forced_answer`
reports this honestly: the collapse half (Discharged) and the not-yet-escaped half.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series6.ws1

universe u

namespace Series6.WS2

open Series6.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## Reachability and hereditary non-emptiness on an abstract coalgebra -/

/-- Reachability along a structure map. -/
def SReaches {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  Relation.ReflTransGen (fun a b => b ∈ (dest a).1)

/-- Hereditary non-emptiness: every reachable state has a nonempty successor set. -/
def SHNE {X : Type u} (dest : X → PkObj κ X) (x : X) : Prop :=
  ∀ v, SReaches dest x v → (dest v).1 ≠ ∅

lemma SHNE.ne_empty {X : Type u} {dest : X → PkObj κ X} {x : X}
    (hx : SHNE dest x) : (dest x).1 ≠ ∅ := hx x Relation.ReflTransGen.refl

lemma SHNE.succ {X : Type u} {dest : X → PkObj κ X} {x w : X}
    (hx : SHNE dest x) (hw : w ∈ (dest x).1) : SHNE dest w :=
  fun v hv => hx v (Relation.ReflTransGen.head hw hv)

/-! ## Bisimulation and behavioral identity (the definition of "static") -/

/-- A `P_κ`-bisimulation (set-relator form): related states have matching successor sets. -/
def IsBisim {X : Type u} (dest : X → PkObj κ X) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ x' ∈ (dest x).1, ∃ y' ∈ (dest y).1, R x' y') ∧
    (∀ y' ∈ (dest y).1, ∃ x' ∈ (dest x).1, R x' y')

/-- **Behavioral identity**: every bisimulation is contained in equality. This is the
defining property of a *static* construction (charter §3.1); it is what makes "an object
is its relating" exact, and it is exactly what collapses under global atomlessness. -/
def BehaviorallyIdentified {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ (R : X → X → Prop), IsBisim dest R → ∀ x y, R x y → x = y

/-- A **static construction**: a coalgebra whose behavioral equivalence is identity.
Covers the single carrier, the labelled carrier's *quotient*, and the tower colimit as
instances (any finished object with behavioral identity). -/
structure Static (κ : Cardinal.{u}) where
  X : Type u
  dest : X → PkObj κ X
  behav : BehaviorallyIdentified dest

/-! ## The genuine-atomlessness predicates -/

/-- Hereditarily atomless: no leaf anywhere. -/
def HereditarilyAtomless (S : Static κ) : Prop := ∀ x, SHNE S.dest x

/-- **No imported atom**: the distinction between objects is carried by the relating
itself — the coalgebra is genuinely behaviorally identified, so every distinction is a
descent distinction (there is no bare label/index doing the distinguishing). -/
def NoImportedAtom {X : Type u} (dest : X → PkObj κ X) : Prop := BehaviorallyIdentified dest

/-- Genuinely globally atomless: hereditarily atomless AND importing no external atom. -/
def GenuinelyAtomless (S : Static κ) : Prop := HereditarilyAtomless S ∧ NoImportedAtom S.dest

/-! ## The Static Collapse Theorem -/

/-- The maximal "both hereditarily nonempty" relation. -/
def hneRel {X : Type u} (dest : X → PkObj κ X) : X → X → Prop :=
  fun x y => SHNE dest x ∧ SHNE dest y

/-- The hereditarily-nonempty relation is a bisimulation: nobody is ever empty, so each
side can always answer the other. -/
lemma hneRel_isBisim {X : Type u} (dest : X → PkObj κ X) : IsBisim dest (hneRel dest) := by
  rintro x y ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · intro x' hx'
    obtain ⟨y', hy'⟩ := Set.nonempty_iff_ne_empty.mpr hy.ne_empty
    exact ⟨y', hy', hx.succ hx', hy.succ hy'⟩
  · intro y' hy'
    obtain ⟨x', hx'⟩ := Set.nonempty_iff_ne_empty.mpr hx.ne_empty
    exact ⟨x', hx', hx.succ hx', hy.succ hy'⟩

/-- **The Static Collapse Theorem (Impossibility proved — the motivating success).** In any
static, genuinely globally atomless construction, the world is a subsingleton: any two
objects are equal. Genuine global atomlessness, staticness, and plurality cannot all three
hold. Every static plurality is bought by an imported atom. -/
theorem ws2_static_collapse (S : Static κ) (hgen : GenuinelyAtomless S) : Subsingleton S.X :=
  ⟨fun x y => S.behav (hneRel S.dest) (hneRel_isBisim S.dest) x y ⟨hgen.1 x, hgen.1 y⟩⟩

/-! ## The apparent escapes are imports

A concrete label/index-distinguished plurality: two self-loops at indices `⟨true⟩, ⟨false⟩ : ULift Bool`.
Both are hereditarily nonempty (atomless), and distinct — but they are NOT behaviorally
identified (the label-blind "everything is bisimilar" relation identifies them), so their
distinction is carried by the imported index `ULift Bool`, a bare atom moved into the alphabet.
This is `νLk`'s labelled loops and the tower's index, in their essential shape. -/

/-- Two indexed self-loops: `dest i = {i}`. -/
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

/-- **The diagnosis (the decidable check WS2 stands on).** The indexed loops are
hereditarily nonempty and distinct, yet fail `NoImportedAtom`: their plurality is carried
by the imported index, not by the relating. So `GenuinelyAtomless` is non-circular —
refuted by a real construction, not by fiat — and the collapse's breadth is earned. -/
theorem ws2_escapes_are_imports (hinf : ℵ₀ ≤ κ) :
    ¬ NoImportedAtom (twoLoop hinf)
  ∧ (∀ i, SHNE (twoLoop hinf) i)
  ∧ (∃ a b : ULift.{u} Bool, a ≠ b) := by
  refine ⟨?_, twoLoop_HNE hinf, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩
  intro hbi
  have h01 : (⟨true⟩ : ULift.{u} Bool) = ⟨false⟩ :=
    hbi (fun _ _ => True) (twoLoop_true_bisim hinf) ⟨true⟩ ⟨false⟩ trivial
  exact absurd h01 (by decide)

/-! ## Subsumptions and the forced answer -/

/-- **Subsumes Parmenides** on the honest plain carrier: the productive core of the
stagewise process `Proc` (over the honestly atom-free carrier) is a subsingleton — the
single self-relating point Ω. (WS1's `ws1_productive_unique`; the finished object and the
naive process collapse alike.) -/
theorem ws2_subsumes_parmenides (hinf : ℵ₀ ≤ κ) :
    ∀ x y : Proc κ, Productive x → Productive y → x = y := by
  intro x y hx hy
  rw [ws1_productive_unique hinf x hx, ws1_productive_unique hinf y hy]

/-- **Subsumes the tower.** Any behaviorally-identified hereditarily-atomless static —
including a colimit/tower — collapses; its cross-level plurality is carried by an imported
index (the analogue of `twoLoop`'s label), not by the relating. -/
theorem ws2_subsumes_tower (S : Static κ) (h : HereditarilyAtomless S) : Subsingleton S.X :=
  ws2_static_collapse S ⟨h, S.behav⟩

/-- **The forced answer (honest, obstructed on C2).** (i) Every genuinely atomless static
collapses. (ii) The naive dynamic escape does NOT deliver on the C2 carrier: the stagewise
process ALSO collapses (`ws1_no_productive_plurality`). So the static collapse extends to
the naive process; the genuine non-importing escape is owed to the richer carrier home
(metric C4 / guarded), not witnessed here. Essential-uniqueness of the forced answer stays
the pre-registered heuristic ceiling (charter §9). -/
theorem ws2_forced_answer (hinf : ℵ₀ ≤ κ) :
    (∀ S : Static κ, HereditarilyAtomless S → Subsingleton S.X)
  ∧ (¬ ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y) :=
  ⟨fun S h => ws2_static_collapse S ⟨h, S.behav⟩, ws1_no_productive_plurality hinf⟩

end Series6.WS2
