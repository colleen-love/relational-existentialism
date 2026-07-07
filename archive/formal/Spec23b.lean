/-
Spec 2.3b — Run the Trials (B1, the Forcing Lemma, and the anti-Mirror spot-check).

Normative source: `series-2/2-3.md` §5 (The Trials, R4) — the protocol, the
candidates made precise (§5.1), the pre-registered battery (§5.2), and the FROZEN
predictions (§5.3) — plus §4 (D20/D21). Specs win; discrepancies reported in the
mapping table at the foot.

This file is an experiment's lab notebook. The predictions in 2.3 §5.3 were frozen
at that revision's commit; this file makes each one true or false and every theorem's
doc-comment says which prediction it CONFIRMS or REFUTES. A surprised prediction is
the trial working; no refutation is softened.

Builds on `Spec21a` (the `Raw` signature), `Spec21c` (`G`), and `Spec23a`
(`G_unit_subsingleton`, and the `Subsingleton (Sym2 PUnit)` instance). Spec23a
transitively imports Spec21a/b/c/d/202, so a single import suffices; the work order's
`Spec21a`/`Spec21c` are named for the reader.
-/
import Spec21a
import Spec21c
import Spec23a

namespace RelEx.Trials

/-- Finite nonempty subsets, as the standing subtype (2.3 §2 shorthand). -/
def PfNe (α : Type) : Type := {S : Set α // S.Finite ∧ S.Nonempty}

/-! ## The two forcing atoms

Over a subsingleton aspect-space, the two individuating resources drawn from the
carrier or pattern are both pinned: nonemptiness forces `= univ`, properness forces
`= ∅`. These are the content of the Forcing Lemma (§3); every B1 collapse below is
one or both of them. -/

/-- Over a subsingleton, a nonempty set is forced to `univ`: the only nonempty set. -/
theorem forced_univ {α : Type} [Subsingleton α] {S : Set α} (h : S.Nonempty) :
    S = Set.univ :=
  Set.eq_univ_of_forall fun p => by
    obtain ⟨q, hq⟩ := h; rwa [Subsingleton.elim p q]

/-- Over a subsingleton, a proper subset is forced to `∅`: the only proper subset of
the (nonempty, hence `univ`) whole. A nonempty `T ⊆ S` would already be all of `S`. -/
theorem forced_empty {α : Type} [Subsingleton α] {S T : Set α} (h : T ⊂ S) :
    T = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x hx
  exact absurd
    (Set.eq_of_subset_of_subset h.subset (fun y _ => by rwa [Subsingleton.elim y x]))
    h.ne

/-- Over a subsingleton, `PfNe` is itself a subsingleton (every member forced to
`univ`). Powers `B1_A_pattern` and the `PfNe (Sym2 PUnit)` collapse. -/
instance PfNe.subsingleton {α : Type} [Subsingleton α] : Subsingleton (PfNe α) := by
  constructor
  rintro ⟨_, _, hNa⟩ ⟨_, _, hNb⟩
  exact Subtype.ext ((forced_univ hNa).trans (forced_univ hNb).symm)

/-! ## FL — the Forcing Lemma (class-level; 2.3 §5.3, §5.4)

Stated first because the (A)/(B) collapses below are its instances. It is a theorem
about a **class** of functors, not checked instance-wise, so the (A)/(B) eliminations
cannot be artifacts of provisional definitions (2.3 §5.4): any variant evading the
hypotheses is invited to re-enter — as A2 did. The class: a `Σ`-over-`Π` of set-valued
division data over a subsingleton aspect-space `α`, with the base pinned by nonemptiness
(⇒ `univ`) and every part pinned by properness inside the base (⇒ `∅`). `P` is an
arbitrary proof-irrelevant side-predicate (here carrying the `Finite` clause), `ι` an
arbitrary index family (here `↥S`, the pattern's members). Moral (2.3 §5.3): derived
division-material as such is forced over the point — it was never nonemptiness
specifically. The escapes are exactly relational self-reference (C) and the forbidden
coin (A2). -/

/-- The class of division data the Forcing Lemma pins: a nonempty base together with an
arbitrary indexed family of proper-subset parts of it. -/
def DivisionData (α : Type) (P : Set α → Prop) (ι : Set α → Type) : Type :=
  Σ S : {S : Set α // P S ∧ S.Nonempty}, ∀ _ : ι S.1, {T : Set α // T ⊂ S.1}

/-- FL — the Forcing Lemma. Over a subsingleton aspect-space, every division datum is
unique: the base is forced to `univ` (nonemptiness) and every part to `∅` (properness),
so nothing is left to vary. `B1_A` is a literal instance (`P := Set.Finite`, `ι := ↥`);
`B1_B` derives via `attBToDiv`. This generality is the acceptance test of 2.3 §5.3/§5.4
— not the two instances in a trenchcoat, but the class both are instances of. -/
theorem forcing_lemma (α : Type) [Subsingleton α]
    (P : Set α → Prop) (ι : Set α → Type) :
    Subsingleton (DivisionData α P ι) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨Sa, hPa, hNa⟩, fa⟩ := a
  obtain ⟨⟨Sb, hPb, hNb⟩, fb⟩ := b
  have hSab : Sa = Sb := (forced_univ hNa).trans (forced_univ hNb).symm
  subst hSab
  have hf : fa = fb :=
    funext fun r =>
      Subtype.ext ((forced_empty (fa r).2).trans (forced_empty (fb r).2).symm)
  subst hf
  rfl

/-! ## B1 — the F(1)/Parmenides gate (D20), run symmetrically on every entrant

B1-G (control): the collapsed G fails B1 by `G_unit_subsingleton` (Spec23a) — cited,
not reproved. Every gate it passes has no discriminating power (2.3 §5.1). -/

/-! ### B1-A — pure (A), division over the pattern -/

/-- Candidate (A), evaluated at the one-point pair (2.3 §5.1(A)): the relation sort is
`Sym2 PUnit`, a subsingleton. Charitable-to-(A) reading: the division is defined **on
the pattern's members** (`↥S.1`), not as a total function on all of `Sym2 PUnit`, so
off-member junk cannot manufacture a fake pass. See the mapping table for the
restatement. -/
def AttA : Type :=
  Σ S : PfNe (Sym2 PUnit), ∀ _r : ↥S.1, {T : Set (Sym2 PUnit) // T ⊂ S.1}

/-- B1-A — CONFIRMS 2.3 §5.3's Forcing Conjecture for (A): **fails by collapse.**
`S.1` is nonempty inside a subsingleton, hence `= univ` (the singleton); each `T ⊂ S.1`
is forced to `∅`; everything is pinned, so `AttA` is a subsingleton. Derived as a
literal instance of the Forcing Lemma (`forcing_lemma`, §3) — its acceptance test. -/
theorem B1_A : Subsingleton AttA :=
  forcing_lemma (Sym2 PUnit) Set.Finite (fun S => ↥S)

/-- B1-A lifted to the pattern level (optional per the work order; `B1_A` is the
load-bearing fact). Over a collapsed relation sort even the space of patterns is a
point. -/
theorem B1_A_pattern : Subsingleton (PfNe AttA) := by
  haveI := B1_A; infer_instance

/-! ### B1-B and B1-Bs — (B), functorial proper inclusion -/

/-- Candidate (B), T possibly empty (2.3 §5.1(B)): the seen `p.2` inside the had
`p.1`. -/
def AttB : Type := { p : Set (Sym2 PUnit) × Set (Sym2 PUnit) //
  p.1.Finite ∧ p.1.Nonempty ∧ p.2 ⊂ p.1 }

/-- Candidate (B)-strict: both sides nonempty. -/
def AttBs : Type := { p : Set (Sym2 PUnit) × Set (Sym2 PUnit) //
  p.1.Finite ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ p.2 ⊂ p.1 }

/-- The single-part shape of (B), as a `DivisionData` with a one-point index — the
degenerate case of the Forcing Lemma from which `B1_B` is derived. -/
noncomputable def attBToDiv (a : AttB) :
    DivisionData (Sym2 PUnit) Set.Finite (fun _ => PUnit) :=
  ⟨⟨a.1.1, a.2.1, a.2.2.1⟩, fun _ => ⟨a.1.2, a.2.2.2⟩⟩

/-- B1-B — CONFIRMS 2.3 §5.3's Forcing Conjecture for (B): **fails by collapse.**
`S` forced to the singleton; `T ⊂ S` forces `T = ∅`; one element. Derived from the
Forcing Lemma: `attBToDiv` injects (B) into the class the lemma pins, so equal images
force equal originals — the second half of the acceptance test. -/
theorem B1_B : Subsingleton AttB := by
  haveI : Subsingleton (DivisionData (Sym2 PUnit) Set.Finite (fun _ => PUnit)) :=
    forcing_lemma _ _ _
  refine ⟨fun a b => ?_⟩
  have h : attBToDiv a = attBToDiv b := Subsingleton.elim _ _
  have hS : a.1.1 = b.1.1 := congrArg (fun d => d.1.1) h
  have hT : a.1.2 = b.1.2 := congrArg (fun d => (d.2 PUnit.unit).1) h
  exact Subtype.ext (Prod.ext_iff.mpr ⟨hS, hT⟩)

/-- B1-Bs — CONFIRMS 2.3 §5.3's prediction for (B)-strict: **fails by emptiness** —
*the arrow cannot turn.* A nonempty set strictly inside a (nonempty subset of a)
subsingleton is impossible: austere properness forbids the One from attending at all,
and a universe built on strict inclusion alone is *empty* at the fiber where the
self-loop is demanded. `T ⊂ S` forces `T = ∅`, contradicting `T.Nonempty`. The second
B-failure mode (emptiness, distinct from collapse) is thereby on record. -/
theorem B1_Bs_empty : IsEmpty AttBs := by
  constructor
  rintro ⟨⟨_, _⟩, _, _, hTne, hT⟩
  rw [forced_empty hT] at hTne
  exact Set.not_nonempty_empty hTne

/-! ### B1-C — (C), the tower, relations over `Sym2 (O ⊕ R)` -/

/-- B1-C — CONFIRMS 2.3 §5.3's Tower Conjecture: (C) **passes** B1. Over the One the
relation sort is `Sym2 (PUnit ⊕ PUnit)`, and it already distinguishes the self-relation
`s(inl ⋆, inl ⋆)` from *the bearing on the self-relation* `s(inl ⋆, inr ⋆)`:
sort-composition of endpoints is observable structure, and F(1)'s inhabitants are the
different ways the One can turn upon its own turning. Separated by membership: the
right endpoint `inr ⋆` lies in the second pair, not the first. (The tower's infinitude
is a spec-level remark; not chased here.) -/
theorem B1_C : ¬ Subsingleton (Sym2 (PUnit ⊕ PUnit)) := by
  intro h
  haveI := h
  have heq : (s(Sum.inl PUnit.unit, Sum.inl PUnit.unit) : Sym2 (PUnit ⊕ PUnit))
           = s(Sum.inl PUnit.unit, Sum.inr PUnit.unit) := Subsingleton.elim _ _
  have hmem : (Sum.inr PUnit.unit : PUnit ⊕ PUnit) ∈
      (s(Sum.inl PUnit.unit, Sum.inr PUnit.unit) : Sym2 (PUnit ⊕ PUnit)) :=
    Sym2.mem_iff.mpr (Or.inr rfl)
  rw [← heq, Sym2.mem_iff] at hmem
  rcases hmem with h1 | h1 <;> simp at h1

/-! ### B1-A2 — the evasion-clause entrant -/

/-- Candidate (A2), loss-mandatory / grasp-optional (2.3 §5.1(A2)): `p.1 = H` (grasp,
may be `∅`), `p.2 = M` (remainder, mandatory nonempty). -/
def AttA2 (X : Type) : Type :=
  { p : Set (Sym2 X) × Set (Sym2 X) // p.1.Finite ∧ p.2.Finite ∧ p.2.Nonempty }

/-- B1-A2 — CONFIRMS 2.3 §5.3's prediction: (A2) **passes** B1 — but **powered by ∅.**
The two witnesses `⟨(∅, {r̂})⟩` and `⟨({r̂}, {r̂})⟩` differ *only* in the first component,
and their entire difference is emptiness: the ∅/nonempty bit is the individuating
resource, which the framework's own D4 analysis names the **primordial atom**. This is
evidence *for* A2's predicted elimination at B7 (parsimony: no new atoms, ∅ included),
not a victory for A2. Read the witnesses: the (A)-family buys plurality only with the
forbidden coin. -/
theorem B1_A2 : ¬ Subsingleton (AttA2 PUnit) := by
  intro h
  let r : Sym2 PUnit := s(PUnit.unit, PUnit.unit)
  have heq :
      (⟨(∅, {r}), Set.finite_empty, Set.finite_singleton r, Set.singleton_nonempty r⟩ :
        AttA2 PUnit)
      = ⟨({r}, {r}), Set.finite_singleton r, Set.finite_singleton r,
          Set.singleton_nonempty r⟩ :=
    @Subsingleton.elim (AttA2 PUnit) h _ _
  have hne : (∅ : Set (Sym2 PUnit)) = {r} := congrArg (fun a => a.1.1) heq
  have hr : r ∈ ({r} : Set (Sym2 PUnit)) := rfl
  rw [← hne] at hr
  exact Set.not_mem_empty r hr

/-! ## B2-C — the anti-Mirror spot-check, run *before* any (C)-development

Per the wantability hazard (2.3 §5.4): (C) is the owner's original axiom returning, so
both collaborators want it — therefore it is scrutinized first. The Mirror was one
hand-check-caught collapse; there is no budget for a machine-caught second. -/

/-- Candidate (C)'s raw shape: endpoints drawn from either sort. Coherence and parthood
design are OPEN (2.3 O-2-3-1b); this structure exists only to run the anti-Mirror
check on raw behavior. -/
structure RawC where
  O : Type
  R : Type
  endpoints : R → Sym2 (O ⊕ R)
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty

/-- Depth-1 invariant: some pattern-member bears on a relation (has an `inr` endpoint).
The theorem the collapsed universe could not have — a sort-composition invariant at
depth 1. -/
def HasMetaBearing (A : RawC) (x : A.O) : Prop :=
  ∃ r ∈ A.pat x, ∃ q : A.R, Sum.inr q ∈ A.endpoints r

/-- The two-state (C) witness: `true` meta-bears, `false` does not. -/
def RawC_sep : RawC where
  O := Bool
  R := Bool
  endpoints := fun b => match b with
    | true => s(Sum.inl true, Sum.inr false)   -- the meta-bearing
    | false => s(Sum.inl true, Sum.inl false)  -- an ordinary object-object relation
  pat := fun b => {b}
  pat_nonempty := fun b => Set.singleton_nonempty b

/-- B2-C — CONFIRMS 2.3 §5.3/§5.4: (C) admits two states separated by a depth-1
sort-composition invariant — *the theorem the collapsed universe could not have*,
checked for (C) **before** any (C)-development per the wantability clause. `true`'s sole
pattern-member (`endpoints true`) has an `inr` endpoint; `false`'s (`endpoints false`)
has both endpoints in `inl`, so it cannot meta-bear. -/
theorem B2_C_separation :
    ∃ (A : RawC) (x y : A.O), HasMetaBearing A x ∧ ¬ HasMetaBearing A y := by
  refine ⟨RawC_sep, true, false, ⟨true, rfl, false, ?_⟩, ?_⟩
  · -- inr false ∈ endpoints true = s(inl true, inr false)
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  · rintro ⟨r, hr, q, hq⟩
    -- r ∈ RawC_sep.pat false is defeq to r = false
    have hrfl : r = false := hr
    subst hrfl
    -- endpoints false = s(inl true, inl false): no inr endpoint
    rw [show RawC_sep.endpoints false = s(Sum.inl true, Sum.inl false) from rfl,
        Sym2.mem_iff] at hq
    rcases hq with h | h <;> simp at h

end RelEx.Trials

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Trials
#print axioms B1_A
#print axioms B1_B
#print axioms B1_Bs_empty
#print axioms B1_C
#print axioms B1_A2
#print axioms forcing_lemma
#print axioms B2_C_separation
end AxiomAudit

/-
================================================================================
2.3 §5.3 predictions ↔ outcomes  (see 2.3 §5.6 Results for the prose transcript)
================================================================================
-- Forcing (A):   B1_A            Subsingleton   — predicted fail-by-collapse   → CONFIRMED
-- Forcing (B):   B1_B            Subsingleton   — predicted fail-by-collapse   → CONFIRMED
-- Arrow:         B1_Bs_empty     IsEmpty        — predicted fail-by-emptiness  → CONFIRMED
-- Tower:         B1_C            ¬Subsingleton  — predicted PASS               → CONFIRMED
-- Evader:        B1_A2           ¬Subsingleton  — predicted pass (∅-powered)   → CONFIRMED
-- Forcing Lemma: forcing_lemma   class-level    — SHOULD-strong                → DELIVERED
-- Anti-Mirror:   B2_C_separation separation     — predicted separation         → CONFIRMED
--
-- All seven predictions confirmed; nothing refuted. The fork narrows to (C) by
-- elimination — twice over for the (A)-family: (A)/(B) collapse (Forcing Lemma),
-- (B)-strict empties, (A2) passes only on the forbidden coin (∅, B7-eliminable).
--
-- Entrant ↔ Lean name:
--   B1-G   (control)          = RelEx.TwoSorted.G_unit_subsingleton  (Spec23a, cited)
--   B1-A   (pure A)           = RelEx.Trials.AttA, B1_A, B1_A_pattern
--   B1-B   (B, T possibly ∅)  = RelEx.Trials.AttB, B1_B
--   B1-Bs  (B-strict)         = RelEx.Trials.AttBs, B1_Bs_empty
--   B1-C   (tower)            = RelEx.Trials.B1_C
--   B1-A2  (evasion clause)   = RelEx.Trials.AttA2, B1_A2
--   FL     (Forcing Lemma)    = RelEx.Trials.DivisionData, forcing_lemma
--   B2-C   (anti-Mirror)      = RelEx.Trials.RawC, HasMetaBearing, RawC_sep, B2_C_separation
--
-- Deviations from 2-3-mechanization-b.md:
--   * B1-A's division is defined on `↥S.1` (the pattern's members), the charitable
--     reading the work order requests, not as a total function on `Sym2 PUnit`.
--   * The Forcing Lemma (`forcing_lemma`) is stated over a `DivisionData` class with an
--     arbitrary proof-irrelevant side-predicate `P` and index family `ι`. B1_A is a
--     literal (defeq) instance; B1_B is derived through `attBToDiv`. The B2-C stretch
--     goal (`IsBisimC` / Egli–Milner) is dropped per the work order's "drop freely"
--     clause: the separation-by-invariant is the load-bearing content, and full
--     bisimulation machinery belongs to (C)'s own spec if it wins.
--   * Registered as a ninth Lake library root (`Spec23b`).
-/
