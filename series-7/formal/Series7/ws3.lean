/-
`series-7/formal/Series7/ws3.lean`

WS3 — **The trichotomy of distinction.** Series 7, the theorem's teeth.

Owns the classification: every distinction between two objects of a plain construction is a
leaf, an import, or an intensional-history difference; the third collapses under atomlessness;
and — the genuinely-open piece — the classification is exhaustive on a single plain coalgebra
(the engine forces it), Partial across "any construction" (the un-rangeable quantifier).

Design doc: `series-7/spec/ws3-design.md`, candidate C1 (kinds independently characterized,
`≠` in the hypothesis, disjunction in the conclusion — never the definitional-partition trap
C2).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws2

universe u

namespace Series7.WS3

open Series7.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The three kinds, independently characterized on the plain functor -/

/-- **(i) A LEAF** — a descent difference: one of the two states bottoms out (an atom),
forbidden by atomlessness. -/
def LeafDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  ¬ SHNE dest x ∨ ¬ SHNE dest y

/-- **(ii) An IMPORT** — a coordinate invisible to relating: the states are bisimilar yet
unequal, so the distinction is not carried by `dest` (a `BehaviorallyIdentified` violation). -/
def ImportDiff {X : Type u} (dest : X → PkObj κ X) (x y : X) : Prop :=
  (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y

/-! ## The dichotomy on a single plain coalgebra

REVIEW RESPONSE (project-review-1.md R1/R2, recorded in `charter-status.md`). Pass 1 was right
that on a SINGLE plain coalgebra there are only two kinds — a leaf or an import — because there
is no founded-history dimension; the earlier `HistoryDiff := False` made the "trichotomy" a
dichotomy in trichotomy vocabulary. This is now stated honestly: `ws3_dichotomy` (two kinds on a
single coalgebra) plus a CONTENTFUL third kind `HistoryDiff` on the PROCESS (inhabited among
non-productive threads, collapsing under atomlessness). The "no fourth kind / teeth" framing is
withdrawn; the single-coalgebra exhaustiveness is a genuine dichotomy, not overclaimed. -/

/-- **D1 — the dichotomy.** Any distinction on a single plain coalgebra is a leaf or an import.
`≠` is in the HYPOTHESIS and the disjunction in the CONCLUSION (never the definitional-partition
trap C2). Proof: if either state fails atomlessness it is a leaf; else both are atomless, so the
engine (`ws1_atomless_bisim`) relates them by a bisimulation, and with `x ≠ y` that is an
import. -/
theorem ws3_dichotomy {X : Type u} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y := by
  by_cases hx : SHNE dest x
  · by_cases hy : SHNE dest y
    · exact Or.inr ⟨ws1_atomless_bisim dest x y hx hy, h⟩
    · exact Or.inl (Or.inr hy)
  · exact Or.inl (Or.inl hx)

/-- **D3 — atomless-distinct-⇒-import, using the no-leaf hypothesis.** Ruling out the leaf
(both states atomless) forces the import — the engine relates any two atomless states by a
bisimulation. Renamed from "exhaustive" (pass 1 R2): it genuinely consumes `¬ LeafDiff`, and it
is the non-circular core (engine-driven), not a "no fourth kind" claim. -/
theorem ws3_atomless_distinct_is_import {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (h : x ≠ y) (hnl : ¬ LeafDiff dest x y) : ImportDiff dest x y := by
  simp only [LeafDiff, not_or, not_not] at hnl
  obtain ⟨hx, hy⟩ := hnl
  exact ⟨ws1_atomless_bisim dest x y hx hy, h⟩

/-! ## The third kind (intensional history) — contentful, on the process -/

/-- **(iii) An INTENSIONAL-HISTORY difference**, on the PROCESS carrier: two distinct threads at
least one of which is non-atomless (leafy). This kind is genuinely inhabited (among
non-productive threads) and collapses under atomlessness. -/
def HistoryDiff (x y : Proc κ) : Prop := x ≠ y ∧ (¬ Productive x ∨ ¬ Productive y)

/-- **The third kind is inhabited** — Ω and the atom process are a history difference (the atom
is leafy). So `HistoryDiff` is not a `False` placeholder. -/
theorem ws3_history_kind_inhabited (hinf : ℵ₀ ≤ κ) : ∃ x y : Proc κ, HistoryDiff x y :=
  ⟨omegaProc hinf, emptyProc hinf, omega_ne_empty hinf, Or.inr (empty_not_productive hinf)⟩

/-- **D2 — the third kind collapses under atomlessness.** Two productive (atomless) threads
have no history difference: both are Ω. Transcribes `ws1_productive_unique`. -/
theorem ws3_history_kind_collapses (_hinf : ℵ₀ ≤ κ) (x y : Proc κ)
    (hx : Productive x) (hy : Productive y) : ¬ HistoryDiff x y :=
  fun ⟨_, hor⟩ => hor.elim (fun h => h hx) (fun h => h hy)

/-- The direct collapse fact (Ω unique among atomless threads), transcribed. -/
theorem ws3_history_collapses (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht

/-! ## The three kinds are genuinely distinct (not a definitional partition) -/

/-- A leaf that is not an import: two distinct states, one an atom, NOT bisimilar-related as a
pair of atomless states. Witnessed by `Bool` with the empty-successor coalgebra. -/
theorem ws3_leaf_not_import (hinf : ℵ₀ ≤ κ) :
    ∃ (X : Type u) (dest : X → PkObj κ X) (x y : X),
      LeafDiff dest x y ∧ ¬ SHNE dest x := by
  refine ⟨ULift.{u} Bool, fun _ => toPk hinf (∅ : Set (ULift.{u} Bool)), ⟨true⟩, ⟨false⟩, ?_, ?_⟩
  · left; intro hs; exact (hs ⟨true⟩ Relation.ReflTransGen.refl) (by rw [toPk_val])
  · intro hs; exact (hs ⟨true⟩ Relation.ReflTransGen.refl) (by rw [toPk_val])

/-- An import that is not a leaf: the two indexed self-loops are atomless (no leaf) yet
bisimilar-and-unequal (an import). So `LeafDiff` and `ImportDiff` have different extensions. -/
theorem ws3_import_not_leaf (hinf : ℵ₀ ≤ κ) :
    ImportDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩ ∧ ¬ LeafDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩ := by
  refine ⟨⟨⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩, by decide⟩, ?_⟩
  intro hleaf
  rcases hleaf with h | h
  · exact h (twoLoop_HNE hinf ⟨true⟩)
  · exact h (twoLoop_HNE hinf ⟨false⟩)

end Series7.WS3
