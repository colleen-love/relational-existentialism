/-
`series-7/formal/Series7/ws1.lean`

WS1 — **Atomless behavior is unique.** Series 7, the blocking engine.

This file is SELF-CONTAINED: it transcribes (re-namespaced `Series7.WS1`) the `P_κ` /
bisimulation machinery and the finite-approximation process from Series 4/6 — nothing is
imported from `series-6/`, `series-5/`, `series-4/`, or `archive/`. It first-classes the
general lemma that on ANY plain `P_κ`-coalgebra, all hereditarily-non-empty states are
related by a bisimulation (the "both-atomless" relation), and recovers the program's two
existing collapses as instances.

Design doc: `series-7/spec/ws1-design.md`; shared predicates `series-7/spec/readme.md` §2.

REALIZATION NOTE (recorded in `charter-status.md`, routed to the WS1/WS4 designs). The
static instance is realized in its ABSTRACT form — over any `BehaviorallyIdentified` plain
coalgebra — rather than tied to the specific terminal carrier `νPk`; the terminal coalgebra
is one such coalgebra, so the abstract form subsumes `ws2_collapse` without transcribing the
heavy QPF `νPk` construction. This is a faithful reframing (the signature "behavioral
identity turns the engine into equality" is met), not a retargeting.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` /
`Quot.sound`.
-/
import Mathlib

universe u

namespace Series7.WS1

open Cardinal

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

/-! ## The finite-approximation tower (transcribed from Series 6) -/

def Approx (κ : Cardinal.{u}) : ℕ → Type u
  | 0     => PUnit.{u+1}
  | (n+1) => PkObj κ (Approx κ n)

def trunc (κ : Cardinal.{u}) : (n : ℕ) → Approx κ (n+1) → Approx κ n
  | 0     => fun _ => PUnit.unit
  | (n+1) => fun s => PkMap κ (trunc κ n) s

instance : Finite (Approx κ 0) := by show Finite PUnit.{u+1}; infer_instance
instance : Subsingleton (Approx κ 0) := by show Subsingleton PUnit.{u+1}; infer_instance

instance approx_finite : ∀ n, Finite (Approx κ n)
  | 0 => by show Finite PUnit.{u+1}; infer_instance
  | (n+1) => by
      haveI : Finite (Approx κ n) := approx_finite n
      haveI : Finite (Set (Approx κ n)) := inferInstance
      show Finite (PkObj κ (Approx κ n))
      exact Finite.of_injective (fun s : PkObj κ (Approx κ n) => s.1)
        (fun a b h => Subtype.ext h)

noncomputable def toPk (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) : PkObj κ X :=
  ⟨s, by
    haveI : Finite (↥s) := Subtype.finite
    exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite (↥s)) hinf⟩

@[simp] lemma toPk_val (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) :
    (toPk hinf s).1 = s := rfl

/-! ## The process carrier `Proc` (transcribed from Series 6) -/

def Proc (κ : Cardinal.{u}) : Type u :=
  { x : (n : ℕ) → Approx κ n // ∀ n, trunc κ n (x (n+1)) = x n }

theorem proc_ext (x y : Proc κ) : x = y ↔ ∀ n, x.1 n = y.1 n := by
  constructor
  · rintro rfl n; rfl
  · intro h; exact Subtype.ext (funext h)

theorem ws1_no_collapse (x y : Proc κ) (n : ℕ) (h : x.1 n ≠ y.1 n) : x ≠ y := by
  intro he; exact h (by rw [he])

noncomputable def omegaApprox (hinf : ℵ₀ ≤ κ) : (n : ℕ) → Approx κ n
  | 0     => PUnit.unit
  | (n+1) => ⟨{omegaApprox hinf n}, mk_singleton_lt hinf _⟩

lemma omegaApprox_succ (hinf : ℵ₀ ≤ κ) (n : ℕ) :
    (omegaApprox hinf (n+1) : Approx κ (n+1)) = ⟨{omegaApprox hinf n}, mk_singleton_lt hinf _⟩ :=
  rfl

theorem omega_compat (hinf : ℵ₀ ≤ κ) :
    ∀ n, trunc κ n (omegaApprox hinf (n+1)) = omegaApprox hinf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show PkMap κ (trunc κ n) (omegaApprox hinf (n+2)) = omegaApprox hinf (n+1)
      apply Subtype.ext
      rw [omegaApprox_succ, PkMap_val]
      show (trunc κ n) '' ({omegaApprox hinf (n+1)} : Set (Approx κ (n+1))) = {omegaApprox hinf n}
      rw [Set.image_singleton, ih]

noncomputable def omegaProc (hinf : ℵ₀ ≤ κ) : Proc κ :=
  ⟨omegaApprox hinf, omega_compat hinf⟩

/-! ## Genuine every-moment atomlessness (transcribed) -/

def allNonempty (κ : Cardinal.{u}) : (n : ℕ) → Approx κ n → Prop
  | 0,     _ => True
  | (n+1), s => s.1.Nonempty ∧ ∀ t ∈ s.1, allNonempty κ n t

def Productive (x : Proc κ) : Prop := ∀ n, allNonempty κ n (x.1 n)

theorem omega_allNonempty (hinf : ℵ₀ ≤ κ) :
    ∀ n, allNonempty κ n (omegaApprox hinf n) := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [omegaApprox_succ]; exact ⟨omegaApprox hinf n, rfl⟩
      · intro t ht
        rw [omegaApprox_succ] at ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact ih

theorem ws1_omega_process (hinf : ℵ₀ ≤ κ) : Productive (omegaProc hinf) :=
  omega_allNonempty hinf

/-- The load-bearing uniqueness: the only hereditarily-nonempty depth-`n` approximation is Ω's. -/
theorem allNonempty_unique (hinf : ℵ₀ ≤ κ) :
    ∀ (n) (s : Approx κ n), allNonempty κ n s → s = omegaApprox hinf n := by
  intro n
  induction n with
  | zero => intro s _; exact Subsingleton.elim (α := Approx κ 0) s (omegaApprox hinf 0)
  | succ n ih =>
      rintro s ⟨hne, hall⟩
      apply Subtype.ext
      rw [omegaApprox_succ]
      apply Set.Subset.antisymm
      · intro t ht; rw [Set.mem_singleton_iff]; exact ih t (hall t ht)
      · intro t ht
        rw [Set.mem_singleton_iff] at ht; subst ht
        obtain ⟨t₀, ht₀⟩ := hne
        rw [← ih t₀ (hall t₀ ht₀)]; exact ht₀

/-- **The dynamic collapse (transcribed).** Ω is the unique productive thread. -/
theorem ws1_productive_unique (hinf : ℵ₀ ≤ κ) (x : Proc κ) (hx : Productive x) :
    x = omegaProc hinf := by
  rw [proc_ext]; intro n
  exact allNonempty_unique hinf n (x.1 n) (hx n)

theorem ws1_no_productive_plurality (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y := by
  rintro ⟨x, y, hne, hx, hy⟩
  exact hne (by rw [ws1_productive_unique hinf x hx, ws1_productive_unique hinf y hy])

/-! ## The atom process — a permanent leaf (a non-productive thread) -/

noncomputable def emptyApprox (hinf : ℵ₀ ≤ κ) : (n : ℕ) → Approx κ n
  | 0     => PUnit.unit
  | (n+1) => toPk hinf (∅ : Set (Approx κ n))

theorem empty_compat (hinf : ℵ₀ ≤ κ) :
    ∀ n, trunc κ n (emptyApprox hinf (n+1)) = emptyApprox hinf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n _ =>
      show PkMap κ (trunc κ n) (emptyApprox hinf (n+2)) = emptyApprox hinf (n+1)
      apply Subtype.ext
      show (trunc κ n) '' (∅ : Set (Approx κ (n+1))) = (∅ : Set (Approx κ n))
      rw [Set.image_empty]

noncomputable def emptyProc (hinf : ℵ₀ ≤ κ) : Proc κ :=
  ⟨emptyApprox hinf, empty_compat hinf⟩

/-- The atom process carries a finite-stage leaf: at stage 1 its successor set is empty. -/
theorem empty_leafy (hinf : ℵ₀ ≤ κ) : ¬ allNonempty κ 1 ((emptyProc hinf).1 1) := by
  intro h
  have hne : ((emptyApprox hinf 1).1).Nonempty := h.1
  simp only [emptyApprox, toPk_val] at hne
  exact Set.not_nonempty_empty hne

/-- The atom process is NOT productive — it is a permanent atom, not a limit-atomless thread. -/
theorem empty_not_productive (hinf : ℵ₀ ≤ κ) : ¬ Productive (emptyProc hinf) :=
  fun hp => empty_leafy hinf (hp 1)

theorem omega_ne_empty (hinf : ℵ₀ ≤ κ) : omegaProc hinf ≠ emptyProc hinf := by
  apply ws1_no_collapse (omegaProc hinf) (emptyProc hinf) 1
  intro h
  change omegaApprox hinf 1 = emptyApprox hinf 1 at h
  have hv := congrArg Subtype.val h
  rw [omegaApprox_succ] at hv
  simp only [emptyApprox, toPk_val] at hv
  exact (Set.singleton_ne_empty (omegaApprox hinf 0)) hv

/-! ## Bisimulation, behavioral identity, and the "both-atomless" bisimulation (transcribed) -/

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

/-- **Behavioral identity = no imported atom** (the same predicate, README §2). -/
def BehaviorallyIdentified {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ (R : X → X → Prop), IsBisim dest R → ∀ x y, R x y → x = y

def NoImportedAtom {X : Type u} (dest : X → PkObj κ X) : Prop := BehaviorallyIdentified dest

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

/-! ## The abstract static object (transcribed) -/

structure Static (κ : Cardinal.{u}) where
  X : Type u
  dest : X → PkObj κ X
  behav : BehaviorallyIdentified dest

def HereditarilyAtomless (S : Static κ) : Prop := ∀ x, SHNE S.dest x
def GenuinelyAtomless (S : Static κ) : Prop := HereditarilyAtomless S ∧ NoImportedAtom S.dest

/-! ## The escapes are imports: two indexed self-loops (transcribed) -/

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

/-! ## The WS1 deliverables -/

/-- **D1 — the engine.** On any plain coalgebra, any two atomless states are related by a
bisimulation, namely the "both-atomless" relation. Weaker than equality (no behavioral
identity assumed), hence general — it reaches beyond the terminal object. -/
theorem ws1_atomless_bisim {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y :=
  ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩

/-- **D2 — the static instance.** Behavioral identity turns the engine into equality: any
plain, behaviorally-identified coalgebra collapses its atomless states. (The terminal
coalgebra `νPk` is one such; this abstract form subsumes `ws2_collapse`.) -/
theorem ws1_recovers_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) :
    x = y := by
  obtain ⟨R, hR, hxy⟩ := ws1_atomless_bisim dest x y hx hy
  exact hbehav R hR x y hxy

/-- **D3 — the dynamic instance.** The unique productive thread of the process is Ω — the
same idea (atomless ⇒ unique behavior) on the founded approximations. -/
theorem ws1_recovers_dynamic (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht

end Series7.WS1
