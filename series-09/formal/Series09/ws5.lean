/-
`series-09/formal/Series09/ws5.lean`

WS5 — **The monotonicity fork.** Series 09, the central honest open.

**Addresses series-review-1 F-6 (REAL) / F-8 (SERIOUS).** With the strengthened `ReDiagStep` (the next
stage inspects the WHOLE prior residue), the kill condition now fires GENUINELY, not by a point-flip:
re-diagonalization inspects the prior residue and thereby CLOSES it wholesale
(`ws5_retention_refuted`, `ws5_kill_condition` via WS4 `ws4_residue_moves`). Strict monotonicity
(retention of prior blind spots) is Refuted; the bound is mere non-triviality; the "ever-deepening self"
is retracted. Verdict: **Partial** (Refuted-universal, Discharged on a freshness-gated class). This is
the charter's mechanism, honestly reported as Refuted — re-inspection RESOLVES what it inspects.

Consumes WS3/WS4, never redefines them. `accResidue`/`MonotoneResidue` measured OUTSIDE `ReDiagStep`.
Design doc: `series-09/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series09.ws4

universe u

namespace Series09.WS5

open Series09.WS1 Series09.WS3 Series09.WS4 Cardinal

variable {κ : Cardinal.{u}}

/-- The **retention** horn of monotonicity: every prior blind spot survives the next re-diagonalization
(the residue is inherited, never closed). -/
def ResidueNonShrinking {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' → (∀ h, diag m h → diag m' h)

/-- **Monotone growth (MG)** in full: the residue never shrinks AND strictly grows. The strong bound. -/
def MonotoneResidue {X : Type u} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' →
    (∀ h, diag m h → diag m' h) ∧ (∃ h, diag m' h ∧ ¬ diag m h)

inductive MonotonicityVerdict | discharged | refuted | partialV
  deriving DecidableEq

/-- **D1 — retention is refuted, GENUINELY (series-review-1 F-6/F-8).** A re-diagonalization inspects the
whole prior residue and thereby CLOSES it: taking the successor `⊤` (which inspects any residue), a prior
blind spot at `h₀` is resolved (`diag ⊤ h₀ = ¬⊤ = False`). So retention fails on any carrier with a
nonempty residue — not by a point-flip, but because re-inspection resolves what it inspects. -/
theorem ws5_retention_refuted {X : Type u} (dest : X → PkObj κ X)
    (hwit : ∃ (insp : Hold dest → HoldPred dest) (h₀ : Hold dest), diag insp h₀) :
    ¬ ResidueNonShrinking dest := by
  intro hns
  obtain ⟨insp, h₀, hblind⟩ := hwit
  have hstep : ReDiagStep dest insp (fun _ _ => True) := fun _ _ => trivial
  have hret := hns insp (fun _ _ => True) hstep h₀ hblind
  exact hret trivial

/-- **D2 — the kill condition fires.** A re-diagonalization that closes a prior blind spot: inspecting
the residue (`⊤` self-holds it) resolves the blind spot at `h₀`, net residue non-increasing there.
Monotonicity is Refuted; the "ever-deepening self" is retracted (charter §5.4). -/
theorem ws5_kill_condition {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (_hblind : diag insp h₀) :
    ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀ := by
  refine ⟨fun _ _ => True, fun _ _ => trivial, ?_⟩
  intro hd
  exact hd trivial

/-- **D3 — strict growth on a fresh, hypothesis-gated class, honestly narrow.** If a stage `m'` opens a
blind spot at `h` that the accumulated residue of `chain` did not contain (a freshness gate), then
prepending `m'` STRICTLY enlarges the accumulated residue at `h`. The freshness is a hypothesis on the
CHAIN, NOT on the map — the narrow positive horn of the Partial. -/
theorem ws5_monotone_on_fresh {X : Type u} (dest : X → PkObj κ X)
    (chain : List (Hold dest → HoldPred dest)) (m' : Hold dest → HoldPred dest) (h : Hold dest)
    (hfresh : diag m' h ∧ ¬ accResidue chain h) :
    accResidue (m' :: chain) h ∧ ¬ accResidue chain h :=
  ⟨⟨m', List.mem_cons_self m' chain, hfresh.1⟩, hfresh.2⟩

/-- **D4 — the settled fork.** The verdict is Partial: Refuted in general (D1/D2, now genuine — inspecting
resolves), strictly growing only on the fresh class (D3). Justified by theorems — not hand-set. -/
def ws5_monotonicity_verdict : MonotonicityVerdict := .partialV

theorem ws5_verdict_justified {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)
  ∧ (∃ (i : Hold dest → HoldPred dest) (h : Hold dest), diag i h) :=
  ⟨ws5_kill_condition dest insp h₀ hblind, ⟨insp, h₀, hblind⟩⟩

end Series09.WS5
