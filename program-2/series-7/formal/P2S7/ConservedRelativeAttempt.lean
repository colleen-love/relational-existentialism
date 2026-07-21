/-
`program-2/series-7/formal/P2S7/ConservedRelativeAttempt.lean`

ON-RECORD ATTEMPT at CONSERVED-RELATIVE (requested by the Tier-1 landing review before accepting MONOTONE-ONLY).
NOT part of the P2S7 build (not imported by the `P2S7` aggregator); it is a checkable record of the search.

The Tier-1 bar for a genuine CONSERVED-RELATIVE was TWO-part:
  (1) a measure conserved by the tick because reification is genuinely LOSSLESS — a Q-preserving re-encoding proven
      Q-specifically, NOT "the two states are bisimilar" (the collapse costume that sank the first landing); AND
  (2) a free-lunch fork where the DIAGONAL actually decides Q (not a `Finset.card` counter beside it).

RESULT: requirement (1) is MET (`attempt_ws2_lossless`, `attempt_ws1_content_apart` below); requirement (2) is REFUTED
(`attempt_diagonal_always_creates`). So CONSERVED-RELATIVE is NOT earned, and the honest verdict is MONOTONE-ONLY.

The measure here is `Qout := out-degree` (the realized content of a relatum). It is conserved by the tick VIA THE
SECTION (`attendsC (reifyC s) = s`), lossless re-encoding — this is genuine, not the collapse. Its differences are
genuine imports (out-degree is not plain-bisimulation-invariant). BUT: (a) `Qout` conserves the pattern SIZE (a
lossless-encoding identity that strips to the section), not import-CONTENT — the charter's measure of distinction
(the count of non-recoverable distinctions, `rankM`) provably RISES; and decisively (b) the DIAGONAL cannot decide
`Qout` toward conservation, because the residue is ALWAYS free (`ws2_residue_free`): genuine self-reference always
CREATES a new non-recoverable content, never relocates. So a genuine diagonal-deciding-Q fork lands on creation, and
the "conserved/relocate" side is reachable ONLY by a disconnected counter — exactly the costume the first landing
used. Conservation-from-within is impossible: the diagonal is always a source.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import P2S6

universe u
namespace P2S7ConservedAttempt
open P1.Core P1.Reader P2S0 P2S1 Cardinal
set_option linter.unusedVariables false

/-- Carrier: bases a,b,c (out-degree 1, self-loops); r = reifyC{a,b} (out-degree 2); r1 = reifyC{a} (out-degree 1). -/
abbrev MC : Type := Fin 5
def a : MC := 0
def b : MC := 1
def c : MC := 2
def r : MC := 3    -- = reifyC {a,b}
def r1 : MC := 4   -- = reifyC {a}

def attendsC : MC → Finset MC := fun x =>
  if x = a then {a} else if x = b then {b} else if x = c then {c}
  else if x = r then {a, b} else {a}

/-- THE MEASURE Q := out-degree (the realized content of a relatum). Structural; no conservation clause. -/
def Qout : MC → ℕ := fun x => (attendsC x).card

def reifyC : Finset MC → MC := fun s => if s = {a, b} then r else if s = {a} then r1 else a

lemma sectionC_ab : attendsC (reifyC {a, b}) = {a, b} := by decide
lemma sectionC_a  : attendsC (reifyC {a})    = {a}    := by decide
lemma attendsC_nonempty : ∀ x : MC, (attendsC x).Nonempty := by decide

variable {κ : Cardinal.{0}}
lemma outDestC_ne (hinf : ℵ₀ ≤ κ) (x : MC) : (outDest hinf attendsC x).1 ≠ ∅ := by
  show (↑(attendsC x) : Set MC) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsC_nonempty x))
lemma SHNE_C (hinf : ℵ₀ ≤ κ) (x : MC) : SHNE (outDest hinf attendsC) x := fun v _ => outDestC_ne hinf v

lemma plainOf_rankLiftC (dest : MC → PkObj κ MC) (lab : MC → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp
lemma rankLiftC_val (dest : MC → PkObj κ MC) (lab : MC → ℕ) (x : MC) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1 := rfl

theorem sepC_general (dest : MC → PkObj κ MC) (lab : MC → ℕ) (x y : MC)
    (hlab : lab x ≠ lab y) (hne : (dest x).1 ≠ ∅) :
    ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR x y hRel
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hedge : ((⟨lab x⟩ : ULift.{0} ℕ), z) ∈ (rankLift dest lab x).1 := by
    rw [rankLiftC_val]; exact ⟨z, hz, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [rankLiftC_val] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  exact hlab (congrArg ULift.down hfst)

/-- The content lift: the label broadcasts Q = out-degree. -/
noncomputable def outLift (hinf : ℵ₀ ≤ κ) : MC → LkObj κ (ULift.{0} ℕ) MC :=
  rankLift (outDest hinf attendsC) Qout

/-- **REQUIREMENT (1), PART A — THE TICK CONSERVES Q, LOSSLESSLY, VIA THE SECTION.** Reification realizes exactly
the encoded content: `Qout (reifyC s) = s.card`, because `attendsC (reifyC s) = s` (the section). This is a genuine
Q-specific conservation resting on the SECTION (lossless re-encoding), NOT on the collapse engine. -/
theorem attempt_ws2_lossless :
    Qout (reifyC {a, b}) = (({a, b} : Finset MC)).card
  ∧ Qout (reifyC {a})    = (({a}   : Finset MC)).card := by
  refine ⟨?_, ?_⟩
  · show (attendsC (reifyC {a, b})).card = _; rw [sectionC_ab]
  · show (attendsC (reifyC {a})).card = _; rw [sectionC_a]

/-- **REQUIREMENT (1), PART B — Q IS NON-TRIVIAL AND ITS DIFFERENCES ARE IMPORTS.** `Qout r = 2 ≠ 1 = Qout a`, and
`r` (out-degree 2) is plain-bisimilar to `a` (out-degree 1) — the collapse engine — yet content-lift-separated:
out-degree is NOT recoverable from the plain relating, so the `Q`-difference is a genuine import. -/
theorem attempt_ws1_content_apart (hinf : ℵ₀ ≤ κ) :
    Qout r ≠ Qout a ∧ AttentionDistinguishes (outLift hinf) r a := by
  refine ⟨by decide, ?_, ?_⟩
  · show ∃ R, IsBisim (plainOf (outLift hinf)) R ∧ R r a
    rw [outLift, plainOf_rankLiftC]
    exact ws1_atomless_bisim (outDest hinf attendsC) r a (SHNE_C hinf r) (SHNE_C hinf a)
  · show ¬ ∃ R, IsBisimL (outLift hinf) R ∧ R r a
    exact sepC_general (outDest hinf attendsC) Qout r a (by decide) (outDestC_ne hinf r)

/-- **REQUIREMENT (2) IS REFUTED — THE DIAGONAL ALWAYS CREATES, NEVER RELOCATES.** For EVERY inspection the residue
(the P1 diagonal) is free — a genuinely new non-recoverable content produced from within (`ws2_residue_free`). So a
free-lunch fork in which the diagonal genuinely decides `Q` can only land on CREATION: there is NO genuine
relocate/conserved side for self-reference. The "conserved" side is reachable ONLY by a counter disconnected from the
diagonal (the costume the first landing used). Hence CONSERVED-RELATIVE cannot be earned; conservation-from-within is
impossible, and the honest verdict is MONOTONE-ONLY (the measure rises) — self-reference is a source, not a ledger. -/
theorem attempt_diagonal_always_creates (hinf : ℵ₀ ≤ κ) :
    ∀ insp : Hold (outDest hinf attendsC) → HoldPred (outDest hinf attendsC), ¬ ResidueRecoverable insp :=
  fun insp => ws2_residue_free (outDest hinf attendsC) insp

end P2S7ConservedAttempt
