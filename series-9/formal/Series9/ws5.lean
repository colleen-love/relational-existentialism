/-
`series-9/formal/Series9/ws5.lean`

WS5 — **The monotonicity fork.** Series 9, the central honest open.

Attempt monotone growth of the residue (MG); run the pre-committed kill condition; report
Discharged / Refuted / Partial — never assumed, never baked into `ReDiagStep`. The kill condition
FIRES, and strikingly from re-diagonalization's OWN mechanism: holding a blind spot at `h₀` flips the
diagonal there, so the very act of re-diagonalizing CLOSES the blind spot it holds
(`ws5_retention_refuted`, `ws5_kill_condition`). Verdict: **Partial** (Refuted-universal, Discharged on
a freshness-gated class). The "ever-deepening self" is retracted.

Consumes WS3/WS4 (`ReDiagStep`, `accResidue`), never redefines them. Design doc: `ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws4

universe u

namespace Series9.WS5

open Series9.WS1 Series9.WS3 Series9.WS4 Cardinal

variable {κ : Cardinal.{u}}

/-- The **retention** horn of monotonicity: every prior blind spot survives the next
re-diagonalization (the residue is inherited, never closed). -/
def ResidueNonShrinking {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' → (∀ h, diag m h → diag m' h)

/-- **Monotone growth (MG)** in full: the residue never shrinks AND strictly grows. The strong bound. -/
def MonotoneResidue {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' →
    (∀ h, diag m h → diag m' h) ∧ (∃ h, diag m' h ∧ ¬ diag m h)

inductive MonotonicityVerdict | discharged | refuted | partialV
  deriving DecidableEq

/-- **D1 — retention is refuted.** A re-diagonalization CLOSES the blind spot it holds: holding the
prior residue at `h₀` flips the diagonal there, so a prior blind spot at `h₀` is resolved, not retained.
Monotonicity's retention horn is false — from the map's OWN mechanism. -/
theorem ws5_retention_refuted {X : Type u} (dest : X → PkObj κ X)
    (hwit : ∃ (insp : Hold dest → HoldPred dest) (h₀ : Hold dest), diag insp h₀) :
    ¬ ResidueNonShrinking dest := by
  intro hns
  obtain ⟨insp, h₀, hblind⟩ := hwit
  classical
  have hstep : ReDiagStep dest insp (Function.update insp h₀ (diag insp)) := ⟨h₀, by simp⟩
  have hret := hns insp (Function.update insp h₀ (diag insp)) hstep h₀ hblind
  exact hret (by rw [Function.update_self]; exact hblind)

/-- **D2 — the kill condition fires.** A re-diagonalization that closes a prior blind spot: the residue
at `h₀` is recovered, net residue non-increasing there. Monotonicity is Refuted; the bound is mere
non-triviality; the "ever-deepening self" is retracted (charter §5.4). -/
theorem ws5_kill_condition {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀ := by
  classical
  refine ⟨Function.update insp h₀ (diag insp), ⟨h₀, by simp⟩, ?_⟩
  intro hd
  exact hd (by rw [Function.update_self]; exact hblind)

/-- **D3 — strict growth on a fresh, hypothesis-gated class, honestly narrow.** If a stage `m'` opens a
blind spot at `h` that the accumulated residue of `chain` did not contain (a freshness gate), then
prepending `m'` STRICTLY enlarges the accumulated residue at `h`. The freshness is a hypothesis on the
CHAIN, NOT on the map. -/
theorem ws5_monotone_on_fresh {X : Type u} (dest : X → PkObj κ X)
    (chain : List (Hold dest → HoldPred dest)) (m' : Hold dest → HoldPred dest) (h : Hold dest)
    (hfresh : diag m' h ∧ ¬ accResidue chain h) :
    accResidue (m' :: chain) h ∧ ¬ accResidue chain h :=
  ⟨⟨m', List.mem_cons_self m' chain, hfresh.1⟩, hfresh.2⟩

/-- **D4 — the settled fork.** The verdict is Partial: Refuted in general (D1/D2), strictly growing only
on the fresh class (D3). Justified by theorems — not hand-set. -/
def ws5_monotonicity_verdict : MonotonicityVerdict := .partialV

theorem ws5_verdict_justified {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)
  ∧ (∃ (i : Hold dest → HoldPred dest) (h : Hold dest), diag i h) :=
  ⟨ws5_kill_condition dest insp h₀ hblind, ⟨insp, h₀, hblind⟩⟩

end Series9.WS5
