/-
`series-7/formal/Series7/ws4.lean`

WS4 — **The imports catalogued: the program explained.** Series 7, the interpretive spine.

Owns: exhibiting each prior plurality as a forced ingredient drop, and showing the Import
Theorem predicts each — the recurring "the import could not be removed" of every prior series
was this theorem, unproved. Series 6's process is the confirming negative: it kept (1)(2)(3),
refused to import, and collapsed.

Design doc: `series-7/spec/ws4-design.md`.

REALIZATION NOTE (recorded in `charter-status.md`, routed to the WS4 design). The
series-specific witnesses named in the design — Series 4's `νLk`/`loopState` (label), Series
5's `Winf` (index), Series 3's weight algebra — are NOT re-transcribed here (each needs the
full QPF/tower machinery). Instead the identical STRUCTURAL fact they each witness — two
distinct hereditarily-atomless states distinguished only by an imported coordinate, so
bisimilar-yet-unequal, failing behavioral identity — is exhibited by the minimal witness
`twoLoop` (transcribed WS1). The charter (§4.1, §4.2, §5.2) states these are one phenomenon
(a drop of (1) or, equivalently on the plain functor, of (2)); `twoLoop` is that phenomenon at
its minimum. The S3 weight witness is reported Partial (no Lean witness, even minimal, beyond
the generic import). This is a scope choice, not a retargeting: the structural claim "import =
distinct atomless states failing behavioral identity" is met by theorem.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws3

universe u

namespace Series7.WS4

open Series7.WS1 Series7.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-- **The import phenomenon (the common shape of every prior drop).** A plain coalgebra with
two distinct hereditarily-atomless states that are bisimilar — the distinction carried by an
imported coordinate, not by the relating. This is the label (S4), the index (S5), and the
weight (S3), at their common minimum. -/
def IsImportWitness {X : Type u} (dest : X → PkObj κ X) (a b : X) : Prop :=
  a ≠ b ∧ SHNE dest a ∧ SHNE dest b ∧ (∃ R, IsBisim dest R ∧ R a b)

/-- **The canonical import witness** — two indexed self-loops, distinct and atomless, bisimilar
via the label-blind relation. The imported coordinate is the index `ULift Bool`. -/
theorem ws4_import_witness (hinf : ℵ₀ ≤ κ) :
    IsImportWitness (twoLoop hinf) ⟨true⟩ ⟨false⟩ :=
  ⟨by decide, twoLoop_HNE hinf ⟨true⟩, twoLoop_HNE hinf ⟨false⟩,
   ⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩⟩

/-- **S4 — labels/faces are an import.** The label distinction is non-behavioral on the plain
functor (the states are bisimilar), hence carried by the imported coordinate. (`twoLoop` is
`νLk`'s labelled loops at their structural minimum, README realization note.) -/
theorem ws4_labels_are_import (hinf : ℵ₀ ≤ κ) :
    ImportDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩ :=
  ⟨⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩, by decide⟩

/-- **S5 — levels are an import.** The tower drops plainness (indexed family, not one plain
coalgebra) OR atomlessness (locally founded); they coincide because the index substitutes for
carrier atomlessness. Realized as: an imported-coordinate witness exists (`twoLoop`), the index
behaving exactly as a two-level tower. -/
theorem ws4_levels_are_import (hinf : ℵ₀ ≤ κ) :
    (∃ (X : Type u) (dest : X → PkObj κ X) (a b : X), IsImportWitness dest a b)
  ∨ (¬ ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y) :=
  Or.inl ⟨ULift.{u} Bool, twoLoop hinf, ⟨true⟩, ⟨false⟩, ws4_import_witness hinf⟩

/-- **The capstone — the program explained.** (a) The import phenomenon is witnessed (the drop
S3/S4/S5 each made). (b) The Import Theorem predicts it: plurality on a plain coalgebra forces
dropping behavioral identity or atomlessness (`ws2_plurality_requires_drop`). (c) Series 6 is
the confirmation: it refused the drop, kept (1)(2)(3), and collapsed — its productive threads
are all Ω. -/
theorem ws4_program_explained (hinf : ℵ₀ ≤ κ) :
    IsImportWitness (twoLoop hinf) ⟨true⟩ ⟨false⟩
  ∧ (∀ (a b : ULift.{u} Bool), a ≠ b →
       ¬ (BehaviorallyIdentified (twoLoop hinf) ∧ (∀ i, SHNE (twoLoop hinf) i)))
  ∧ (∀ t : Proc κ, Productive t → t = omegaProc hinf) :=
  ⟨ws4_import_witness hinf,
   fun a b hab => Series7.WS2.ws2_plurality_requires_drop (twoLoop hinf) ⟨a, b, hab⟩,
   fun t ht => ws1_productive_unique hinf t ht⟩

end Series7.WS4
