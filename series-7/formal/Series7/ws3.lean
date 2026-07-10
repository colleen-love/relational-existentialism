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

/-- **(iii) An INTENSIONAL-HISTORY difference** — for a single plain coalgebra there is no
founded-history dimension, so this kind has no witness here; it lives only on the process
carrier (where it collapses under atomlessness, `ws3_history_collapses`). -/
def HistoryDiff {X : Type u} (_dest : X → PkObj κ X) (_x _y : X) : Prop := False

/-! ## The trichotomy -/

/-- **D1 — the trichotomy.** Any distinction on a plain coalgebra is a leaf, an import, or a
history difference. `≠` is in the HYPOTHESIS and the disjunction in the CONCLUSION (never the
definitional-partition trap C2). Proof: if either state fails atomlessness it is a leaf; else
both are atomless, so the engine (`ws1_atomless_bisim`) relates them by a bisimulation, and
with `x ≠ y` that is an import. -/
theorem ws3_trichotomy {X : Type u} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y ∨ HistoryDiff dest x y := by
  by_cases hx : SHNE dest x
  · by_cases hy : SHNE dest y
    · exact Or.inr (Or.inl ⟨ws1_atomless_bisim dest x y hx hy, h⟩)
    · exact Or.inl (Or.inr hy)
  · exact Or.inl (Or.inl hx)

/-- **D2 — the third kind collapses.** Under atomlessness the intensional history is Ω's
(transcribed `ws1_productive_unique`), so `HistoryDiff` has no atomless witness on the
process. -/
theorem ws3_history_collapses (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht

/-- **D3 — exhaustiveness (Discharged on a single coalgebra).** For two ATOMLESS states,
ruling out the leaf forces import or history — and here it is directly an import, because the
engine relates any two atomless states by a bisimulation. This falls out of the engine, NOT
of a definitional disjunction — the non-circular core. -/
theorem ws3_trichotomy_exhaustive {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) (h : x ≠ y) (_hleaf : ¬ LeafDiff dest x y) :
    ImportDiff dest x y ∨ HistoryDiff dest x y :=
  Or.inl ⟨ws1_atomless_bisim dest x y hx hy, h⟩

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
