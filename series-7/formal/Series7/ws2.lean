/-
`series-7/formal/Series7/ws2.lean`

WS2 — **The Import Theorem, and its non-circularity.** Series 7, the spine.

Owns the four-ingredient impossibility: plain relating ∧ behavioral identity ∧ genuine
every-moment atomlessness ⇒ ¬plurality, for static and dynamic constructions, and the
non-circularity proof — the ingredients are the program's founding commitments and the
escapes are refuted as theorems, not excluded by fiat.

Design doc: `series-7/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws1

universe u

namespace Series7.WS2

open Series7.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The Import Theorem -/

/-- **The static form (C1).** A plain, behaviorally-identified, atomless coalgebra is a
subsingleton — any two atomless states are bisimilar (WS1) hence equal (`hbehav`). -/
theorem ws2_import_theorem_static {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ⟨fun x y => ws1_recovers_static dest hbehav x y (hatom x) (hatom y)⟩

/-- **The Import Theorem (C2, headline — Impossibility proved).** No plain coalgebra is
behaviorally-identified, atomless, and plural. (Plainness is the ambient `dest : X → PkObj κ X`;
the three conjuncts are (2), (3), (4).) -/
theorem ws2_import_theorem {X : Type u} (dest : X → PkObj κ X) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y)) := by
  rintro ⟨hb, ha, x, y, hxy⟩
  haveI := ws2_import_theorem_static dest hb ha
  exact hxy (Subsingleton.elim x y)

/-- **The corollary (C3, WS4-facing).** Plurality forces dropping behavioral identity or
atomlessness (or, off-type, plainness). -/
theorem ws2_plurality_requires_drop {X : Type u} (dest : X → PkObj κ X)
    (h4 : ∃ x y : X, x ≠ y) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x)) := by
  rintro ⟨hb, ha⟩
  obtain ⟨x, y, hxy⟩ := h4
  haveI := ws2_import_theorem_static dest hb ha
  exact hxy (Subsingleton.elim x y)

/-- **The dynamic instance (cited parallel).** The unique productive thread is Ω. -/
theorem ws2_dynamic_instance (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht

/-! ## Non-circularity

The theorem is a discovery only if the ingredients are not rigged. NC1: ingredient (2)
behavioral identity is LITERALLY the "no imported atom" predicate (the program's founding
principle, not an exclusion). NC3: the escapes are refuted as THEOREMS — the indexed loops
are hereditarily atomless and distinct yet not behaviorally identified, so their plurality is
carried by the imported index, refuted by `ws2_escapes_are_imports`, not by a rigged
"atomless". -/

/-- **NC3 — the escape is refuted by theorem.** The two indexed self-loops are atomless and
distinct yet fail behavioral identity: an import, by theorem. -/
theorem ws2_escapes_are_imports (hinf : ℵ₀ ≤ κ) :
    ¬ NoImportedAtom (twoLoop hinf)
  ∧ (∀ i, SHNE (twoLoop hinf) i)
  ∧ (∃ a b : ULift.{u} Bool, a ≠ b) := by
  refine ⟨?_, twoLoop_HNE hinf, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩
  intro hbi
  have h01 : (⟨true⟩ : ULift.{u} Bool) = ⟨false⟩ :=
    hbi (fun _ _ => True) (twoLoop_true_bisim hinf) ⟨true⟩ ⟨false⟩ trivial
  exact absurd h01 (by decide)

/-- **The non-circularity (D3).** (NC1) behavioral identity IS the no-import predicate; (NC3)
the escape is refuted as a theorem (distinct atomless states failing behavioral identity),
not excluded by fiat. -/
theorem ws2_non_circular (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X), NoImportedAtom dest ↔ BehaviorallyIdentified dest)
  ∧ (¬ NoImportedAtom (twoLoop hinf)
      ∧ (∀ i, SHNE (twoLoop hinf) i)
      ∧ (∃ a b : ULift.{u} Bool, a ≠ b)) :=
  ⟨fun _ => Iff.rfl, ws2_escapes_are_imports hinf⟩

end Series7.WS2
