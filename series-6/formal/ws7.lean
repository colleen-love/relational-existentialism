/-
`series-6/formal/ws7.lean`

WS7 — **The anti-trivialization audit.** Series 6, runs last; emits the typed verdict.

Aggregates WS3–WS6 and computes the `ProgramVerdict` from three mechanized inputs. The
honest reading of the whole series (recorded in `charter-status.md`):

* **The engine is genuine, not painted on** (`ws3_diagonal_drives`): `residue` is the sole
  definiens of the successor; the residue-law pins the transition uniquely. So
  `paintedOn = false` and the verdict is NOT `Trivialized`.
* **The payoffs do NOT all derive from the diagonal**, and the headline is worse than
  under-derivation: the achievement (atomless AND plural) is an **Impossibility** on C2
  (`ws6_atomless_and_plural_impossible`), the endogenous arrow FAILS the strip (imported
  depth axis, `ws4_arrow_has_first_moment`), and the causal order LAUNDERS (bare same-depth
  posethood, `ws5_incomparability_is_bare_poset`). So `allDerive = false`.
* **The distinctness anchors hold** (`ws7_distinctness_anchors`): the payoffs are genuinely
  distinct statements (groundlessness holds of Ω while productive plurality is impossible;
  strict-arrow-with-a-first-moment ≠ endogenous arrow; bare-poset incomparability ≠
  face-earned relativity). So `anchorsDistinct = true`.

Verdict: `verdict false false true = payoffsEstablished`. The central Series 6 finding is a
sharp negative that counts as success (charter §7/§8): the naive stagewise process over the
honestly atom-free carrier does NOT escape the Static Collapse — the collapse reaches into
every finite approximation — so genuine atomless plurality, the endogenous arrow, and earned
relativity are all owed to the richer carrier home (metric C4 / guarded). The diagonal engine
itself is genuine.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws2
import ws6

universe u

namespace Series6.WS7

open Series6.WS1 Series6.WS3 Series6.WS4 Series6.WS6 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The typed program verdict -/

/-- Series 6's three outcomes. -/
inductive ProgramVerdict
  | oneDiagonal          -- every §5.5 payoff DERIVED from the diagonal engine
  | payoffsEstablished   -- payoffs hold and are distinct where mechanized; origin argued
  | Trivialized          -- Δ painted on, OR the payoffs collapse to one definition
  deriving DecidableEq

/-- The verdict as a total function of three mechanized inputs. -/
def verdict (paintedOn allDerive anchorsDistinct : Bool) : ProgramVerdict :=
  if paintedOn || !anchorsDistinct then .Trivialized
  else if allDerive then .oneDiagonal
  else .payoffsEstablished

/-! ## The single fact under the payoffs -/

/-- **`ws7_one_incompletion`.** No moment is its own successor (the fixed-point-free source). -/
theorem ws7_one_incompletion (hinf : ℵ₀ ≤ κ) : ∀ m : Moment κ, stepM hinf m ≠ m :=
  ws3_fixed_point_free hinf

/-! ## The payoffs that hold (a conjunction, honestly) -/

/-- **`ws7_payoffs_hold`.** The genuinely delivered payoffs, conjoined: the engine identity
(incompleteness), groundlessness from the diagonal, no view from nowhere, agreement is the
collapse, and the Static Collapse itself. (This is a conjunction, not a derivation.) -/
theorem ws7_payoffs_hold (_hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, ¬ Function.Surjective (survey m))
  ∧ (∀ m : Moment κ, diagPred (survey m) ∉ Set.range (survey m))
  ∧ (∀ S : Series6.WS2.Static κ, Series6.WS2.HereditarilyAtomless S → Subsingleton S.X)
  ∧ ((∀ a b : Proc κ, Series6.WS5.Agree a b) ↔ Subsingleton (Proc κ)) :=
  ⟨ws3_incompleteness,
   fun m => ws6_groundlessness_from_diagonal m,
   fun S h => Series6.WS2.ws2_static_collapse S ⟨h, S.behav⟩,
   Series6.WS5.ws5_agreement_is_collapse⟩

/-! ## The engine is not painted on (paintedOn = false) -/

/-- **`ws7_engine_not_painted_on`.** The successor state IS the residue and the residue-law
pins the transition uniquely — the diagonal genuinely drives (WS3 D4). -/
theorem ws7_engine_not_painted_on (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, (stepM hinf m).2 = residue hinf m)
  ∧ (∀ step : Moment κ → Moment κ,
       (∀ m, step m = ⟨m.1 + 1, residue hinf m⟩) → step = stepM hinf) :=
  ws3_diagonal_drives hinf

/-! ## The distinctness anchors (anchorsDistinct = true) -/

/-- **`ws7_distinctness_anchors`.** Three genuine two-statement distinctness rows:
1. groundlessness holds of Ω (productive) while productive plurality is IMPOSSIBLE — the two
   payoffs are separated by a witness, not one definition;
2. the arrow is strict yet has a first moment — strict-directionality ≠ the endogenous arrow;
3. `≺`-incomparability is exhibited by bare same-depth posethood — bare incomparability ≠
   face-earned relativity. -/
theorem ws7_distinctness_anchors (hinf : ℵ₀ ≤ κ) :
    (Productive (omegaProc hinf)
      ∧ ¬ ∃ x y : Proc κ, Productive x ∧ Productive y ∧ x ≠ y)
  ∧ ((Irreflexive (prec hinf) ∧ Transitive (prec (κ := κ) hinf))
      ∧ ¬ ∃ m₀ : Moment κ, prec hinf m₀ (⟨0, PUnit.unit⟩ : Moment κ))
  ∧ (∃ m m' : Moment κ, m ≠ m' ∧ ¬ prec hinf m m' ∧ ¬ prec hinf m' m) :=
  ⟨⟨ws1_omega_process hinf, ws6_atomless_and_plural_impossible hinf⟩,
   ⟨ws4_arrow_strict hinf, (ws4_arrow_has_first_moment hinf).1⟩,
   Series6.WS5.ws5_incomparability_is_bare_poset hinf⟩

/-! ## The strip-test ledger (aggregated) -/

/-- **`ws7_strip_ledger`.** Aggregated strip outcomes:
* engine EARNED — the residue is the successor's only definiens (`ws3_diagonal_drives`);
* arrow endogeneity FLAGGED — a first moment exists, strictness rests on the depth counter
  (`ws4_arrow_has_first_moment`);
* relativity FLAGGED — incomparability is bare same-depth posethood, not face-earned
  (`ws5_incomparability_is_bare_poset`). -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    (∀ step : Moment κ → Moment κ,
       (∀ m, step m = ⟨m.1 + 1, residue hinf m⟩) → step = stepM hinf)   -- engine EARNED
  ∧ (¬ ∃ m₀ : Moment κ, prec hinf m₀ (⟨0, PUnit.unit⟩ : Moment κ))       -- arrow FLAGGED (first moment)
  ∧ (∃ m m' : Moment κ, m ≠ m' ∧ ¬ prec hinf m m' ∧ ¬ prec hinf m' m) := -- relativity FLAGGED (bare poset)
  ⟨(ws3_diagonal_drives hinf).2,
   (ws4_arrow_has_first_moment hinf).1,
   Series6.WS5.ws5_incomparability_is_bare_poset hinf⟩

/-! ## The central negative finding, and the typed verdict -/

/-- **`ws7_c2_collapses` — the central Series 6 finding (Impossibility, a success).** The naive
stagewise process over the honestly atom-free carrier does NOT escape the Static Collapse:
there is no productive plurality. Genuine atomless plurality is owed to a richer carrier home. -/
theorem ws7_c2_collapses (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y :=
  ws1_no_productive_plurality hinf

/-- **`ws7_verdict`.** `paintedOn = false` (engine genuine), `anchorsDistinct = true` (three
rows), `allDerive = false` (achievement Impossibility, arrow imported-axis, relativity
laundered). The verdict is the honest middle: `payoffsEstablished`. -/
theorem ws7_verdict :
    verdict (paintedOn := false) (allDerive := false) (anchorsDistinct := true)
      = ProgramVerdict.payoffsEstablished := rfl

/-- The verdict is not `Trivialized` (the engine is genuine) and not `oneDiagonal` (the
payoffs do not all derive; the achievement is obstructed). -/
theorem ws7_not_trivialized :
    verdict false false true ≠ ProgramVerdict.Trivialized := by decide

theorem ws7_verdict_eq :
    verdict false false true = ProgramVerdict.payoffsEstablished := rfl

end Series6.WS7
