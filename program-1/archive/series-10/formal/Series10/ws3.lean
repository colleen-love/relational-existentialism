/-
`series-10/formal/Series10/ws3.lean`

WS3 — **The reification tower and its order.** Series 10, the engine of the tower (the seed).

Genuinely new Lean: `reifyStep`, `towerN`, `prec`, the (NL) preservation, and the endogenous order.

**Design realization note (recorded in `charter-status.md`).** The design's "ordinal-indexed tower"
(`Ordinal → Set X`) is realized as (i) the index-free **reachability** `prec := ReflTransGen reifyStep`
— which is exactly "reached by reification sequences," the endogenous order, needing no ordinal — plus
(ii) a concrete ℕ-indexed iterate `towerN` for the monotonicity witnesses. The endogenous order and the
close-or-fold predicate (WS4) are stated on `reifyStep`/`prec` and are index-free; the transfinite/limit
behavior (which only matters for the fold's UNIVERSAL form) is deferred to WS5/WS6/Series 11, consistent
with the fold-universal already being deferred. No signature's meaning changes: `reifyStep` and `prec`
are unchanged; only the tower's concrete index is ℕ, not `Ordinal`.

The carrier `(dest, reify, insp)` is a HYPOTHESIS (parameterized), never an exhibited witness — the
theorems hold for ANY reifying carrier. The existence of a model (a type with a section of `dest`) is a
standard large-κ cardinal fact (`λ = λ^{<κ}`), NOT mechanized here and NOT needed: the universal
theorems do not depend on it (recorded in `charter-status.md` as a scope item, charter §5.3).

Depends on WS1. Design doc: `series-10/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws1

universe u

namespace Series10.WS3

open Series10.WS1 Cardinal

-- `dest` is carried through `reifyStep`/`towerN`/`prec` for signature uniformity with the rest of the
-- carrier (the step lives on the coalgebra `(dest, reify)`), though the set-union step itself does not
-- read `dest`. Silence the term-level unused-binder linter for this file.
set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **One reification step.** Adjoin every relatum reifiable from a non-empty κ-bounded pattern drawn
from `Ωα`. The carrier EXTENDS; nothing is recorded on the side. -/
def reifyStep {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }

lemma reifyStep_superset {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) :
    Ωα ⊆ reifyStep dest reify Ωα := fun _ hx => Or.inl hx

/-- The reified relatum of a reifiable non-empty pattern lands in the next stage. -/
lemma reify_mem_reifyStep {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    {Ωα : Set X} {s : PkObj κ X} (hsub : s.1 ⊆ Ωα) (hne : s.1 ≠ ∅) :
    reify s ∈ reifyStep dest reify Ωα := Or.inr ⟨s, hsub, hne, rfl⟩

/-- A concrete ℕ-indexed iterate of the tower (monotonicity witnesses). -/
def towerN {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) : ℕ → Set X
  | 0 => Ω₀
  | n + 1 => reifyStep dest reify (towerN dest reify Ω₀ n)

/-- **THE TOWER ORDER, derived once.** `prec a b` iff `b` is reached by a reification sequence from `a` —
the reflexive-transitive closure of `reifyStep`, from `reify` alone, no external index. -/
def prec {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Set X → Set X → Prop :=
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)

/-- A single reification step is a `prec` step. -/
lemma prec_step {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) :
    prec dest reify Ωα (reifyStep dest reify Ωα) :=
  Relation.ReflTransGen.single rfl

/-- **D1 — (NL) reification preserves `SHNE`.** A reified non-empty hereditarily-non-empty pattern yields
a hereditarily-non-empty relatum: `dest (reify s) = s`, so `reify s` has successors and every reachable
state does too. A full relatum with its own relating, never a leaf. -/
theorem ws3_reify_preserves_SHNE {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) := by
  intro v hv
  rcases Relation.ReflTransGen.cases_head hv with heq | ⟨w, hw, hwv⟩
  · subst heq; rw [h s]; exact hs
  · rw [h s] at hw
    exact hsucc w hw v hwv

/-- **D2 — the tower is growing subcarriers.** The ℕ-iterate is monotone: each stage extends the last,
the carrier EXTENDS (not an external `List`). -/
theorem ws3_tower_step_subset {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X)
    (n : ℕ) : towerN dest reify Ω₀ n ⊆ towerN dest reify Ω₀ (n + 1) :=
  reifyStep_superset dest reify _

theorem ws3_tower_monotone {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X)
    {m n : ℕ} (hmn : m ≤ n) : towerN dest reify Ω₀ m ⊆ towerN dest reify Ω₀ n := by
  induction hmn with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (ws3_tower_step_subset dest reify Ω₀ _)

/-- **D3 — the ONE endogenous order.** `prec` IS the reification-step closure (`Iff.rfl`), from `reify`
alone — no imported ordinal clock. -/
theorem ws3_order_endogenous {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (a b : Set X) :
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b := Iff.rfl

/-- **D4 — the imported-order branch refuted.** `prec` is a GENERATED reachability (`Iff.rfl`-equal to the
reify-closure), NOT a pre-assigned linear counter severable from `reify`: a stage relates to another iff
a reification sequence connects them. The order is endogenous by definition, not a stamp. (Unlike Series
09's cycle-based refutation, the tower is monotone, so the refutation is endogeneity-of-definition.) -/
theorem ws3_imported_order_refuted {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω₀ : Set X) :
    prec dest reify Ω₀ (reifyStep dest reify Ω₀)
  ∧ (∀ a b, prec dest reify a b ↔
       Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b) :=
  ⟨prec_step dest reify Ω₀, fun a b => ws3_order_endogenous dest reify a b⟩

/-- **D5 — the tower is a monotone family of genuine objects (series-review-1 C1, honestly named).** Each
stage is a `Set X` (a genuine object, by type), and the family is monotone, so the tower is well-defined
and never a proper-class abuse — the κ-bound keeps each `reifyStep` a `PkObj κ`-adjunction (the
scaffolding's job, marked for κ-removal in Series 11, no result relies on κ being SMALL). **This is
monotonicity of the family, NOT well-foundedness of `≺` (which is not claimed and not needed at ℕ-index;
the transfinite case is deferred).** -/
theorem ws3_tower_monotone_family {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (Ω₀ : Set X) : ∀ m n : ℕ, m ≤ n → towerN dest reify Ω₀ m ⊆ towerN dest reify Ω₀ n :=
  fun _ _ hmn => ws3_tower_monotone dest reify Ω₀ hmn

end Series10.WS3
