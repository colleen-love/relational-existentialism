/-
Spec 2.02 — Reveal, Internal, and the C1 conditional.

Normative sources: `scratch/spec/2-00.md` (with D17/D18 and R3-revised D9),
`scratch/spec/2-01.md`, `scratch/spec/2-02.md`. Builds on `Spec201`/`Spec201b`
(imported): `Model`, `ctx`, `ContainedIn`/`Touches`/`MutualPartial`, `boolWitness`,
`StepR`/`Connected`, `Model.toRaw`.

Series 2's design questions are closed (R1 π as sub-pattern; R2 threefold
witnessing; R3 scarcity as self-insufficiency). This file mechanizes what those
rulings made design-ready. The star is **C1c** — in a connected universe with no
total object, every object has a boundary: the fish ruling and the monad
conjecture are one fact, and "we are born as bridges" is two discharged
hypotheses (C2, T16) from unconditional.

Deliverables (work order 2-02-mechanization.md §1):
  RVL    Reveal + lemmas + containers_co_attend
  P1b2   reveals_differ                        (barrier two, existence form)
  T13b   received + bounds + received_can_be_proper
  INT    Internal, Windowless, holdDepth + lemmas
  C1c    no_windowless_of_connected_of_no_total   ★
  T14a   piPart + iff-lemmas + preorder
  T14b   containedIn_antisymm_fails
  T14c   mutualPartial_witness
  T14d   comparative fish/partner witness      — DROPPED (SHOULD; see mapping table)
-/
import Spec201
import Spec201b
import Mathlib.Logic.Relation

namespace RelEx
namespace TwoSorted

universe u

/-! ## Part A — Reveal (RVL, P1b2, T13b) -/

/-- Spec 2-02 §3 (R2 formalized): the canonical payload of an attending — the
relation together with its bearing-structure in the observer. Threefold reading
(2-00 D17): (i) the relation; (ii) the self, clarified — `ctx` IS the observer's
own bearings, so self-knowledge is the medium of the act, not a side effect;
(iii) the world through oneself — shared members of the aperture open hearsay
channels. Introspective by construction: the payload is a sub-pattern of the
observer. What Reveal deliberately does NOT contain: any element of
`pat y \ pat x` — the barriers of 2-00 §2.4 are structural, not assumed. -/
def Reveal (M : Model) (x : M.O) (r : M.R) : Set M.R :=
  insert r (ctx M x r)

theorem reveal_subset (M : Model) (x : M.O) (r : M.R) (hr : r ∈ M.pat x) :
    Reveal M x r ⊆ M.pat x :=
  Set.insert_subset_iff.mpr ⟨hr, ctx_subset M x r⟩

theorem mem_reveal_self (M : Model) (x : M.O) (r : M.R) : r ∈ Reveal M x r :=
  Set.mem_insert _ _

/-- Spec 2-00 D17, containers co-attend (static form): a bearing shared into a
container `w` is payload-material for `w` wherever it is payload for `x` — one act
of attention deposits aperture-material in every containing whole. The formal home
of "I learn about myself and all of the things that contain me through our
relation"; per-act restatement of T12's flow. -/
theorem containers_co_attend (M : Model) (x w : M.O) (r s : M.R)
    (hs : s ∈ ctx M x r) (hw : s ∈ M.pat w) :
    s ∈ Reveal M x r ∩ M.pat w :=
  ⟨Set.mem_insert_of_mem _ hs, hw⟩

/-- Spec 2-02 §3 / general P1, barrier two (existence form): one shared relation,
two different payloads. What each side receives of the SAME relation is assembled
from its OWN context — `boolWitness` already carries the difference (its private
bearing `false` sits in x's payload and cannot sit in y's). The general form — no
chain of x's attendings ever assembles y's pattern AS y's — awaits T4's profile
machinery; this witness establishes that the barrier is real, not vacuous. -/
theorem reveals_differ :
    ∃ (M : Model.{0}) (r : M.R) (x y : M.O),
      r ∈ M.pat x ∧ r ∈ M.pat y ∧ Reveal M x r ≠ Reveal M y r := by
  refine ⟨boolWitness, true, true, false, Set.mem_univ _, rfl, ?_⟩
  intro heq
  have hin : (false : Bool) ∈ Reveal boolWitness true true :=
    Set.mem_insert_of_mem _ ⟨Set.mem_univ _, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  rw [heq] at hin
  simp only [Reveal, Set.mem_insert_iff] at hin
  rcases hin with h | h
  · exact absurd h (by decide)
  · exact absurd h.1 (by simp [boolWitness])

/-- Spec 2-02 §3, T13 hearsay bounds. What arrives from `z` through the shared `s`
is `received := Reveal x r ∩ Reveal z s`. The ACQUAINTANCE BOUND is the left
projection: nothing arrives beyond x's own payload on the shared boundary. The
right projection bounds it by z's assembly. "Some of what you attend to":
generically proper in both — witnessed below. -/
def received (M : Model) (x z : M.O) (r s : M.R) : Set M.R :=
  Reveal M x r ∩ Reveal M z s

theorem received_acquaintance_bound (M : Model) (x z : M.O) (r s : M.R) :
    received M x z r s ⊆ Reveal M x r := Set.inter_subset_left

theorem received_source_bound (M : Model) (x z : M.O) (r s : M.R) :
    received M x z r s ⊆ Reveal M z s := Set.inter_subset_right

/-- Spec 2-02 §3, T13: the received payload can be a PROPER part of the source's —
"some of what you attend to," not all. Witness: `boolWitness`, x = false receiving
across the shared relation from z = true, whose payload holds the private bearing
`false` that x cannot receive. -/
theorem received_can_be_proper :
    ∃ (M : Model.{0}) (x z : M.O) (r s : M.R),
      received M x z r s ⊂ Reveal M z s := by
  refine ⟨boolWitness, false, true, true, true, ?_⟩
  refine (Set.ssubset_iff_of_subset (received_source_bound _ _ _ _ _)).mpr
    ⟨(false : Bool), ?_, ?_⟩
  · exact Set.mem_insert_of_mem _ ⟨Set.mem_univ _, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · intro hmem
    have h : (false : Bool) ∈ Reveal boolWitness false true := hmem.1
    simp only [Reveal, Set.mem_insert_iff] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact absurd h.1 (by simp [boolWitness])

/-! ## Part B — Internal, holdDepth, and the C1 conditional -/

/-- Spec 2-02 §4: the internal part of a pattern — relations all of whose endpoints
the object contains (pattern-inclusion, the ratified parthood). The complement
within `pat x` is x's BOUNDARY: the relating that crosses to what x does not
contain. -/
def Internal (M : Model) (x : M.O) : Set M.R :=
  { r ∈ M.pat x | ∀ z ∈ M.endpoints r, ContainedIn M z x }

theorem internal_subset (M : Model) (x : M.O) : Internal M x ⊆ M.pat x :=
  fun _ h => h.1

/-- A windowless object: no boundary at all — every relation held entirely among
contained parts. C1 conjectures these impossible; C1c below proves it
conditionally. -/
def Windowless (M : Model) (x : M.O) : Prop := Internal M x = M.pat x

/-- Spec 2-02 §6 (R3): the depth of x's hold on r — the internalized part of the
aperture. Scarcity's measure: attention is as rich as its neighborhood is woven in,
and never total because closure never completes. Growth, healing, and T12's flow
are movements along this gradient. -/
def holdDepth (M : Model) (x : M.O) (r : M.R) : Set M.R :=
  { s ∈ ctx M x r | ∀ z ∈ M.endpoints s, ContainedIn M z x }

theorem holdDepth_subset_ctx (M : Model) (x : M.O) (r : M.R) :
    holdDepth M x r ⊆ ctx M x r := fun _ h => h.1

/-- A total object: one whose pattern is everything. T16 conjectures none exist;
here totality is a hypothesis to be discharged there. -/
def Total (M : Model) (x : M.O) : Prop := M.pat x = Set.univ

/-- Every `Sym2` is inhabited: it has at least one member. -/
theorem sym2_exists_mem {α : Type*} (z : Sym2 α) : ∃ a, a ∈ z := by
  induction z using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- Spec 2-02 §6 / 2-00 C1 — THE C1 CONDITIONAL. In a connected universe with no
total object, there are no windowless objects: every object is open to otherness.
Windowlessness propagates containment along connection — if x is windowless, any
object reachable from x has its pattern inside x's (each step's relation is in x's
pattern by coherence + the inductive containment, so its far endpoint is contained
by windowlessness); connectivity then reaches every object, every relation lands in
`pat x` through its endpoints, and x is total. You cannot seal yourself off in a
universe where everything touches: the fish ruling and the monad conjecture are ONE
FACT. Hypotheses discharge at C2 (connectivity of Ω) and T16 (no total object);
with them, "we are born as bridges" goes unconditional. -/
theorem no_windowless_of_connected_of_no_total (M : Model)
    (hconn : Connected M.toRaw)
    (hnt : ∀ z : M.O, ¬ Total M z) :
    ∀ x : M.O, ¬ Windowless M x := by
  intro x hw
  have hweq : Internal M x = M.pat x := hw
  -- Containment invariant: everything reachable from x lies within x's pattern.
  have inv : ∀ y, Relation.ReflTransGen (StepR M.toRaw) x y → M.pat y ⊆ M.pat x := by
    intro y hy
    induction hy with
    | refl => exact subset_rfl
    | tail _ hstep ih =>
        obtain ⟨r', hp, hq⟩ := hstep
        have hr'x : r' ∈ M.pat x := ih (M.coherent r' _ hp)
        have hr'int : r' ∈ Internal M x := by rw [hweq]; exact hr'x
        exact hr'int.2 _ hq
  -- Hence x is total, contradicting no-total.
  apply hnt x
  show M.pat x = Set.univ
  refine Set.eq_univ_of_forall (fun s => ?_)
  obtain ⟨w, hw'⟩ := sym2_exists_mem (M.endpoints s)
  exact inv w (hconn x w) (M.coherent s w hw')

/-! ## Part C — T14: the comparative laws and witnesses -/

/-- Spec 2-02 §1 (R1): π ratified — the shared part AS A SUB-PATTERN OF THE
OBSERVER. Not a number: the same underlying set serves both directions; direction
is the embedding (same part, different wholes — the sharing doctrine at the
mereological level); comparison is inclusion within one observer, A3-local by type.
Numeric proportions are representation-layer shorthand only. -/
def piPart (M : Model) (x y : M.O) : Set M.R := M.pat x ∩ M.pat y

/-- One part, two embeddings: the asymmetry of π(x→y) vs π(y→x) lives in whose
pattern it is weighed within, not in the set. -/
theorem piPart_comm_set (M : Model) (x y : M.O) :
    piPart M x y = piPart M y x := Set.inter_comm _ _

theorem containedIn_iff_piPart (M : Model) (x y : M.O) :
    ContainedIn M x y ↔ piPart M x y = M.pat x := Set.inter_eq_left.symm

theorem touches_iff_piPart (M : Model) (x y : M.O) :
    Touches M x y ↔ (piPart M x y).Nonempty := Iff.rfl

theorem containedIn_refl (M : Model) (x : M.O) : ContainedIn M x x := subset_rfl

theorem containedIn_trans (M : Model) {x y z : M.O}
    (h₁ : ContainedIn M x y) (h₂ : ContainedIn M y z) : ContainedIn M x z :=
  h₁.trans h₂

/-- Spec 2-02 §5: ANTISYMMETRY FAILS at the interface — two distinct objects with
identical patterns. Whether pattern-equality forces identity is exactly T7's
question in mereological clothes: in Ω, bisimilarity may identify these; interface
models need not. Witness: two objects, one relation between them, both patterns the
whole. -/
theorem containedIn_antisymm_fails :
    ∃ (M : Model.{0}) (x y : M.O),
      x ≠ y ∧ ContainedIn M x y ∧ ContainedIn M y x := by
  refine ⟨{ O := Bool, R := PUnit, endpoints := fun _ => s(true, false),
            pat := fun _ => Set.univ, pat_nonempty := fun _ => ⟨PUnit.unit, trivial⟩,
            coherent := fun _ _ _ => Set.mem_univ _, dy := fun _ => true },
          true, false, by decide, subset_rfl, subset_rfl⟩

/-- Endpoints for the musicianship model: relation 0 is shared between the two
objects, relation 1 is private to `true`, relation 2 private to `false`. -/
def mpEndpoints : Fin 3 → Sym2 Bool
  | 0 => s(true, false)
  | 1 => s(true, true)
  | 2 => s(false, false)

/-- Spec 2-00 §2.5, the musicianship corner: mutual partiality — each object holds a
private relation, they share one. Also serves as the qualitative fish corner
(touching without containment); the fish/musicianship distinction is comparative
(T14d), not qualitative. Patterns are the endpoint-preimages, so coherence holds
definitionally. -/
theorem mutualPartial_witness :
    ∃ (M : Model.{0}) (x y : M.O), MutualPartial M x y := by
  refine ⟨{ O := Bool, R := Fin 3, endpoints := mpEndpoints,
            pat := fun x => { r | x ∈ mpEndpoints r },
            pat_nonempty := fun x => ⟨0, by cases x <;> simp [mpEndpoints, Sym2.mem_iff]⟩,
            coherent := fun _ _ hx => hx, dy := fun _ => true },
          true, false, ?_, ?_, ?_⟩
  · -- Touches: relation 0 is shared
    exact ⟨0, by simp [mpEndpoints, Sym2.mem_iff], by simp [mpEndpoints, Sym2.mem_iff]⟩
  · -- ¬ ContainedIn true false: relation 1 is private to `true`
    intro hsub
    have h1 : (1 : Fin 3) ∈ { r | (false : Bool) ∈ mpEndpoints r } :=
      hsub (show (1 : Fin 3) ∈ { r | (true : Bool) ∈ mpEndpoints r } by
        simp [mpEndpoints, Sym2.mem_iff])
    simp [mpEndpoints, Sym2.mem_iff] at h1
  · -- ¬ ContainedIn false true: relation 2 is private to `false`
    intro hsub
    have h2 : (2 : Fin 3) ∈ { r | (true : Bool) ∈ mpEndpoints r } :=
      hsub (show (2 : Fin 3) ∈ { r | (false : Bool) ∈ mpEndpoints r } by
        simp [mpEndpoints, Sym2.mem_iff])
    simp [mpEndpoints, Sym2.mem_iff] at h2

end TwoSorted
end RelEx

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms reveal_subset
#print axioms mem_reveal_self
#print axioms containers_co_attend
#print axioms reveals_differ
#print axioms received_acquaintance_bound
#print axioms received_source_bound
#print axioms received_can_be_proper
#print axioms internal_subset
#print axioms holdDepth_subset_ctx
#print axioms no_windowless_of_connected_of_no_total
#print axioms piPart_comm_set
#print axioms containedIn_iff_piPart
#print axioms touches_iff_piPart
#print axioms containedIn_refl
#print axioms containedIn_trans
#print axioms containedIn_antisymm_fails
#print axioms mutualPartial_witness
end AxiomAudit

/-
-- Specs 2-00 / 2-01 / 2-02 ↔ scratch/formal/Spec202.lean
-- Reveal (R2)             = RelEx.TwoSorted.Reveal (+ reveal_subset, mem_reveal_self)
-- Containers co-attend    = RelEx.TwoSorted.containers_co_attend
-- P1 barrier two (exist.) = RelEx.TwoSorted.reveals_differ
-- T13 bounds              = RelEx.TwoSorted.received (+ *_bound, received_can_be_proper)
-- Internal / Windowless   = RelEx.TwoSorted.Internal, Windowless (+ internal_subset)
-- holdDepth (R3)          = RelEx.TwoSorted.holdDepth (+ holdDepth_subset_ctx)
-- C1 conditional (STAR)   = RelEx.TwoSorted.no_windowless_of_connected_of_no_total (+ Total)
-- π ratified (R1)         = RelEx.TwoSorted.piPart (+ piPart_comm_set, iff lemmas)
-- T14 preorder            = RelEx.TwoSorted.containedIn_refl/trans
-- T14 antisym failure     = RelEx.TwoSorted.containedIn_antisymm_fails
-- T14 corners             = RelEx.TwoSorted.mutualPartial_witness
--
-- Deviations from 2-02-mechanization.md:
--   * File registered as a fifth Lake library root (`Spec202`).
--   * T14d (comparative fish/partner witness) DROPPED per its SHOULD/droppable
--     clause; T14a/b/c (the MUST corners and laws) are delivered.
--   * `mutualPartial_witness` defines `pat` as the endpoint-preimage
--     (`{ r | x ∈ mpEndpoints r }`), so coherence holds definitionally
--     (`fun _ _ hx => hx`) — a simplification, mathematically equivalent to the
--     work order's explicit {0,1}/{0,2} patterns.
-/
