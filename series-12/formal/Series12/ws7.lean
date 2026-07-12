/-
`series-12/formal/Series12/ws7.lean`

WS7 - The anti-circularity audit. Series 12, runs last.

Consumes WS1-WS6. The verdict `Series12Verdict` and the fork `ConvergenceFork`/`verdictOfFork` are WS5's
(README §3); WS7 assembles the mechanized `Audit` (the five checks as fields PLUS the WS4 fork) and computes
the verdict by BRANCHING on the fork (Finding 4), so it cannot be hand-set. The five promoted first-class
checks: no-evaluation (every compass-theorem parametric), the genuine model pair, the shape-honest
coincidence, the genuine (non-point-tag) inhabitation, and names-not-terms; plus the strip-test ledger and
the verdict falsifiability.

Design doc: `series-12/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws6

universe u

namespace Series12.WS7

open Series12.WS1 Series12.WS2 Series12.WS3 Series12.WS4 Series12.WS5 Series12.WS6 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The audit certificate (five checks + the WS4 fork), and the verdict branching on it -/

/-- `1 ≤ rankW bW` as a top-level lemma (the structure `where` context otherwise leaves a metavar). -/
lemma one_le_rank_bW : (1 : ℕ) ≤ rankW bW := by decide

/-- **The audit certificate.** Concrete-on-witness certificate fields PLUS the WS4 `fork`; the verdict
BRANCHES on the fork (Finding 4), never a returned constant. `Type u`-valued (carries the data-level fork).
The universally-quantified checks (coincidence, no-evaluation, compass-exogenous) are the separate check
theorems below (`ws7_strip_ledger`, `ws7_no_evaluation`); keeping them out of the structure keeps its
universe clean. -/
structure Audit (hinf : ℵ₀ ≤ κ) : Type u where
  opening     : Many (destWL hinf)                                        -- inhabitable (WS2)
  reify_lb    : cW = reifyW hinf (sW₂ hinf) ∧ 1 ≤ rankW bW                -- reification load-bearing (WS2)
  rank_noninj : rankW aW = rankW aW' ∧ aW ≠ aW'                           -- rank non-injective (Finding 1)
  fork        : ConvergenceFork (destW hinf) (reifyW hinf) aW bW          -- the WS4 fork (Finding 4)

/-- The concrete audit, every field a discharged WS1-WS4 payoff, the fork at `underdet`. -/
noncomputable def ws7_audit (hinf : ℵ₀ ≤ κ) : Audit hinf where
  opening := ws2_many_witness hinf
  reify_lb := ⟨(reifyW_sW₂ hinf).symm, one_le_rank_bW⟩
  rank_noninj := ws_witness_rank_noninjective
  fork := s12_fork hinf

/-- **The verdict BRANCHES on the certified fork (Finding 4).** -/
def verdict {hinf : ℵ₀ ≤ κ} (cert : Audit hinf) : Series12Verdict := verdictOfFork cert.fork

/-- The concrete verdict, computed from the `underdet` fork (a def whose universe is pinned by the fork). -/
noncomputable def ws7_verdict (hinf : ℵ₀ ≤ κ) : Series12Verdict := verdictOfFork (s12_fork hinf)

/-- `ws7_verdict = shapeDrawn` is a THEOREM (the fork is `underdet`, the model pair), not a definitional
constant. -/
theorem ws7_verdict_eq (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf = Series12Verdict.shapeDrawn := rfl

/-- The verdict computed FROM THE AUDIT (`verdict ∘ ws7_audit`) is `shapeDrawn`: the audit's fork is
`underdet`, so the verdict branches to `shapeDrawn`, never hand-set (Finding 4). -/
theorem ws7_audit_verdict (hinf : ℵ₀ ≤ κ) :
    verdict (ws7_audit hinf) = Series12Verdict.shapeDrawn := rfl

/-! ## The five promoted first-class checks -/

/-- **THE NO-EVALUATION CHECK (the central check, discipline 2).** The precise honest formulation
(series-review-1 SR1-1): the convergence relation is PARAMETRIC over the compass type (an `Iff` for ALL `c`,
the first conjunct), and NO compass-parametric obligation is discharged by evaluating a distinguished
compass; the only concrete compasses (`cHold`/`cFail` in WS4, the inline witnesses in WS3) occur solely as
model-pair / existential-witness constructions, never selected to prove a `∀`-compass statement. (This last
clause is meta-level and is the check this audit run performs by grep + unfold; the second conjunct here
records the exogeneity existential the check leans on.) -/
theorem ws7_no_evaluation (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
        (c : Compass dest reify Or) (x W : X),
        Converges dest reify c x W ↔ c.raise x W (c.orient x) = c.orient W)
  ∧ (∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)) (x y : WCar),
        (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y) :=
  ⟨fun {X} dest reify {Or} c x W => Iff.rfl, ws3_compass_exogenous hinf⟩

/-- **THE MODEL-PAIR CHECK (discipline 3).** Two non-degenerate inhabitants on one structure, the relation
holding in one and failing in the other. -/
theorem ws7_model_pair_genuine (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  (ws4_underdetermined hinf).2

/-- **THE INHABITATION CHECK (discipline 4, Finding 1).** The separated relatum `cW` is a reified relatum
carrying the reified constituent `bW` (rank 1), rank is NON-INJECTIVE, and the without-import side is genuine
Series 07; NOT a point-tag. -/
theorem ws7_inhabitation_genuine (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (cW = reifyW hinf (sW₂ hinf) ∧ bW ∈ (sW₂ hinf).1 ∧ 1 ≤ rankW bW)
  ∧ (rankW aW = rankW aW' ∧ aW ≠ aW')
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X),
        BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X) :=
  ⟨ws2_many_witness hinf, ⟨(reifyW_sW₂ hinf).symm, bW_mem_sW₂ hinf, by decide⟩,
   ws_witness_rank_noninjective, fun {X} dest hb ha => ws2_import_theorem_static dest hb ha⟩

/-- **THE NAMES-NOT-TERMS CHECK (discipline 5).** The neutrality theorem IS the object-level surrogate: the
`name` parameter is phantom (unused), so any name is a tagging that changes no payoff. The ENFORCEABLE check
is the meta-level grep over `formal/Series12/` for a proof term / definition named consciousness, God, choice,
or compass-as-content (run by series-review-1: clean); this theorem records that the payoffs are `name`-free
(SR1-7). -/
theorem ws7_names_not_terms {Name : Type u} (name : ULift.{u} Bool → Name) (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ws5_name_neutral name hinf

/-- **THE STRIP-TEST LEDGER.** The payoffs reduced to their bare facts: the coincidence to the two
non-recoverability facts (junk label AND the genuine tower witness); the plurality to the labelled-separation;
the convergence to the model pair, at BOTH the one-layer (`Converges`) and the layered (`ConvergesUp`, SR1-2)
relation. -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ResidueRecoverable insp)
  ∧ (¬ Recoverable (labelLoop hinf))
  ∧ Many (destWL hinf)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        ConvergesUp (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ ConvergesUp (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws4_labelLoop_not_recoverable hinf,
   ws2_many_witness hinf, ws4_underdetermined_pair hinf, ws4_underdetermined_up hinf⟩

/-! ## The verdict falsifiability and the pre-registered branches -/

/-- Any audit's verdict is never a breach-verdict (`verdictOfFork` lands only in `{shapeDrawn,
convergenceDecided}`). -/
theorem ws7_verdict_not_circular {hinf : ℵ₀ ≤ κ} (cert : Audit hinf) : verdict cert ≠ .Circular := by
  cases h : cert.fork <;> simp [verdict, verdictOfFork, h]

theorem ws7_verdict_not_partial {hinf : ℵ₀ ≤ κ} (cert : Audit hinf) : verdict cert ≠ .Partial := by
  cases h : cert.fork <;> simp [verdict, verdictOfFork, h]

/-- The concrete verdict is `shapeDrawn` and not `convergenceDecided`, BECAUSE its fork is `underdet`. -/
theorem ws7_verdict_not_decided (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf ≠ .convergenceDecided := by
  rw [ws7_verdict_eq hinf]; decide

/-- **The terminal verdict: SHAPE-DRAWN.** Computed from the audit (never hand-set), via the `underdet` fork. -/
theorem ws7_verdict_is_shapeDrawn (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf = Series12Verdict.shapeDrawn :=
  ws7_verdict_eq hinf

end Series12.WS7
