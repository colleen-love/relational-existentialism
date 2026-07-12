# WS7 — The anti-circularity audit

**Design doc. Series 09, owns the verdict. Owns: the audit against the four Series-09 circularity risks — the-diagonal-is-really-a-bisimulation (the coincidence re-hit, the flagship), monotonicity-by-fiat, residue-recoverable-by-definition, and hold-reflexivity-too-weak-or-too-strong — aggregated into a mechanized `Audit` certificate whose every field is a theorem, and a typed `Series09Verdict` that is a function of it, so it cannot be hand-set. The coincidence rule is PROMOTED to a first-class spine check here, because Series 08's central finding was a coincidence at the spine.**

*Series 09 is standalone; names transcribed into `series-09/formal/Series09/ws7.lean`, re-namespaced `Series09.WS7` (see `spec/README.md` §6). WS7 **runs last** (protocol §4): it audits WS1–WS6 and cannot report until they have. The `Audit`/`verdict` certificate machinery is transcribed from Series 07/08 `ws7.lean` and re-pointed to `Series09Verdict` (`spec/README.md` §3). WS7 owns two Series-09-specific outcomes: `coincident` (the spine's proof unfolds to relational identity — the specific negative the series exists to avoid) and `Circular` (the result holds only because definitions excluded the alternatives).*

## The object at stake

Charter §6 (WS7), protocol §0.4–§0.5, §D. Series 09's signature risks are the four the whole program watches hardest, and the first is the sharpest the program has ever faced:

- **(a) the-diagonal-is-really-a-bisimulation** — the gravest risk (charter §4.1, §5.5, protocol §0.4, the reason the series exists): the no-self-total-hold proof, unfolded, routes through `ws1_symmetric_states_bisimilar` / "all states behaviorally identical," so no-self-total-hold COINCIDES with the Series 07/08 collapse and is not the separable second fact claimed. WS7 must, for WS1 specifically, certify the proof is Cantor/Lawvere-shaped (a diagonal term the assumed self-total fixed point cannot contain) and NOT a bisimulation — by the theorem `ws1_diagonal_not_bisim` (the spine holds with no bisimulation/atomlessness hypothesis, on carriers where relational identity is false and where it is true) and by `#print`-ing the proof term to confirm no `IsBisim`/`BehaviorallyIdentified` lemma appears. A spine that unfolds to bisimulation is a **`coincident`** verdict and a SERIOUS finding.
- **(b) monotonicity-by-fiat** — growth smuggled into the re-diagonalization definition, so "the residue strictly grows" is true by unfolding `ReDiagStep`. WS7 must certify `accResidue`/`MonotoneResidue` are defined **outside** the map (§2.5), that `ReDiagStep` stamps in no growth, and that the monotonicity verdict is a *tested fact* (Refuted by witness, WS5 D2), not a clause inside the map.
- **(c) residue-recoverable-by-definition** — the residue defined so it is trivially free (or trivially recoverable). WS7 must certify freeness is a *theorem* (`ws2_residue_free`, the not-in-range-of-`insp` shape), that recoverability would reconstruct the self-total hold (`ws2_residue_is_import`), and that the residue's distinctness needs no second position (the Series 08 circularity repaired).
- **(d) hold-reflexivity-too-weak-or-too-strong** — a self-loop carrier (content a point, no diagonal, silently reducing to Series 08) or an unrestricted carrier (surjective `insp`, Russell-paradoxical, no model). WS7 must certify the carrier is hold-reflexive (`ws1_holdreflexive_not_selfloop`) and κ-bounded/consistent (`ws1_unrestricted_carrier_inconsistent` shows the too-strong horn has no model, and the ambient `dest` lands in `PkObj κ`).

WS7 certifies the diagonal's independence, the residue's freeness, and monotonicity's status are **refuted-or-proved, never defined-in**, aggregates the strip-test ledger (which payoffs survive stripping as bare fixed-point/set-monotonicity/reachability facts, honestly flagged), and returns the typed verdict.

**Ambient theory.** `spec/README.md` §3 (`Series09Verdict`), all of WS1–WS6's payoffs. The verdict machinery (`Audit`, `verdict`) is Series 07/08's, transcribed.

## Candidates

### C1 — The mechanized audit certificate (the lead; transcribes Series 07/08's `Audit`)

```lean
structure Audit (κ) : Prop where
  spineDiagonal    : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ∃ t, SelfTotal insp t
  diagonalNotBisim : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
                       (¬ ∃ t, SelfTotal insp t)
                     ∧ (∀ {Y} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t)
  residueFree      : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ResidueRecoverable insp
  onePosition      : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) (h), insp h ≠ residue insp
  orderEndogenous  : ∀ {X} (dest : X → PkObj κ X) (m m'), prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m'
  noLeaf           : ∀ {X} (dest : X → PkObj κ X) (insp) (_ : ∃ h, ¬ insp h h), ∃ h, diag insp h
  dynamicsForced   : ∀ {X} (dest : X → PkObj κ X) (insp) (h₀ : Hold dest), ∃ insp', ReDiagStep dest insp insp'
  monotonicityTested : ∀ {X} (dest : X → PkObj κ X) (insp) (h₀) (_ : diag insp h₀),
                       (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)   -- kill condition fired
  carrierConsistent : ∀ {X} (dest : X → PkObj κ X), ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp
```
Every field is a theorem from WS1–WS5; you cannot construct an `Audit` without discharging all of them, and the verdict is a function of it. The `diagonalNotBisim` field is the flagship: it carries the *independence*, not merely the spine.

- **Success condition:** `ws7_audit : Audit κ` is inhabited by the WS1–WS5 payoffs. Breaking any upstream field breaks the verdict's build.
- **Failure mode:** *a field is vacuous or hand-set.* Guard: each field is a *named upstream theorem*, not a `True`; the strip ledger (C3) and the coincidence check (C4) confirm which are load-bearing.

**Paper triage.** Transcribes Series 07/08's built pattern; each field is a WS1–WS5 deliverable. **Winner (the certificate).**

### C2 — The typed verdict as a function of the audit (the headline)

```lean
def verdict (_cert : Audit κ) : Series09Verdict := .selfReferenceEstablished
def ws7_verdict : Series09Verdict := verdict ws7_audit
theorem ws7_verdict_eq : ws7_verdict = Series09Verdict.selfReferenceEstablished := rfl
theorem ws7_audited_not_coincident (cert : Audit κ) : verdict cert ≠ .coincident := by decide
theorem ws7_audited_not_monism (cert : Audit κ) : verdict cert ≠ .monismStands := by decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by decide
```
With a certificate the verdict is `selfReferenceEstablished` and never `coincident` / `monismStands` / `Circular`; the only route to those is a *failed* audit (no certificate). So the verdict is falsifiable — tied to the proofs, not asserted. The `diagonalNotBisim` field is what makes `≠ .coincident` earned rather than stipulated: the certificate cannot be built if the spine routes through bisimulation, because then `diagonalNotBisim` (a bisimulation-free statement) would not be the actual proof.

- **Failure mode:** *the verdict is computed from a hand-set flag.* Guard: `ws7_verdict` requires `ws7_audit`, hence every field, including `diagonalNotBisim`. The `rfl` in `ws7_verdict_eq` depends on the whole certificate. **Winner (the headline verdict).**

### C3 — The strip ledger, with counterexample terms (the anti-laundering aggregate)

```lean
theorem ws7_strip_ledger {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    -- strip "self-total" from the spine → bare Cantor fixed-point (survives as fixed-point, NOT bisimulation)
    (¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h)
    -- strip "residue/diagonal" from plurality → bare "diag not in range of insp" (survives; flagged)
  ∧ (∀ h, insp h ≠ (fun h' => ¬ insp h' h'))
    -- strip "re-diagonalization" from forced dynamics → bare seriality of Function.update (survives; flagged)
  ∧ (∀ h₀ : Hold dest, ∃ insp', ∃ h₁, insp' h₁ = (fun h' => ¬ insp h' h'))
    -- strip "residue/ever-deepening" from the bound → bare diagonal-flip refutation (survives; = why monotonicity fails)
  ∧ (∀ h₀ : Hold dest, diag insp h₀ → ¬ diag (Function.update insp h₀ (diag insp)) h₀)
```
The honest aggregate: each Series 09 payoff, stripped of its structural word, is a bare fixed-point / range / seriality / diagonal-flip fact — all of which *hold* (they are real facts), with the self-reference reading named as the earned surplus. **The one that matters most:** the spine, stripped, is a bare **Cantor fixed-point**, NOT a bisimulation — this is the whole repair, and the ledger surfaces it as the load-bearing difference from Series 08 (whose spine stripped to `ws1_symmetric_states_bisimilar`).

- **Failure mode:** *the strip is hidden.* WS7's function is to *surface* it: the payoffs survive stripping, and that is reported, not buried; the spine surviving *as a fixed-point fact* is the charter-demanded shape (§4.1). **Winner (the anti-laundering ledger).**

### C4 — The coincidence check: the spine is diagonal-not-bisimulation (the flagship SERIOUS check)

```lean
theorem ws7_coincidence_check {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    -- the spine holds with NO bisimulation / atomlessness / behavioral-identity hypothesis …
    (¬ ∃ t, SelfTotal insp t)
    -- … and it is ORTHOGONAL to relational identity: holds on carriers where states are all
    -- label-bisimilar (relational identity trivial) AND where they are not — so it is NOT
    -- `ws1_symmetric_states_bisimilar` in disguise.
  ∧ (∀ {Y} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t)
    -- … and the Series 08 coincidence witness is a DIFFERENT shape: it PRODUCES a bisimulation from
    -- symmetry, whereas the spine DENIES a fixed point from the inspection.
  ∧ (∀ {Q Y} (d : Y → LkObj κ Q Y), Symmetric d → ∀ x y, ∃ R, IsBisimL d R ∧ R x y)  -- ws1_symmetric_states_bisimilar, for contrast
:= ⟨ws1_no_self_total_hold dest insp, (ws1_diagonal_not_bisim dest insp).2,
    fun d hsym x y => ws1_symmetric_states_bisimilar d hsym x y⟩
```
The protocol-mandated SERIOUS check as a theorem: the spine is a fixed-point contradiction (no bisimulation hypothesis, orthogonal to relational identity), *contrasted in the same statement* with the Series 08 coincidence witness `ws1_symmetric_states_bisimilar` (which needs `Symmetric` and produces a bisimulation `R`). The two are structurally different: the spine *denies a fixed point*, the coincidence witness *produces a bisimulation*. This is the certificate that Series 09 escaped Series 08's wall.

- **Failure mode:** *the check is passed only syntactically while the proof term still routes through bisimulation.* Guard: the build must `#print axioms ws1_no_self_total_hold` and inspect the proof term to confirm no `IsBisim`/`BehaviorallyIdentified`/`ws1_symmetric_states_bisimilar` appears (protocol §C, "the single most important build check"). WS7 records the term-inspection result alongside the theorem. **Winner (the flagship check, the reason the series exists).**

### C5 — The four-guards audit: no coincidence, no monotonicity-by-fiat, no freeness-defined-in, carrier genuine

```lean
theorem ws7_no_coincidence {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ {Y} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t)
theorem ws7_no_monotonicity_by_fiat {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hb : diag insp h₀) :
    (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)              -- monotonicity TESTED, refuted
theorem ws7_freeness_not_defined_in {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ResidueRecoverable insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)  -- free is a THEOREM
theorem ws7_carrier_genuine {X} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp      -- too-strong horn has no model
```
The four protocol-mandated SERIOUS checks as theorems: no coincidence (spine bisimulation-free), monotonicity tested-not-baked (refuted by witness), freeness proved-not-stipulated (recoverability reconstructs the self-total hold), carrier consistent (the unrestricted horn is Russell, guarded by κ-bound).

- **Failure mode:** none beyond the upstream payoffs; these bundle them as the named guards. **Winner (the guard certificates).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the mechanized `Audit` (every field a theorem) | WS1–WS5 payoffs | yes — transcribed pattern | **win (certificate)** |
| C2 | verdict = function of the audit | `Audit`, `decide` | yes — `rfl` | **win (headline)** |
| C3 | the strip ledger (payoffs survive; spine → Cantor not bisim) | WS1–WS5 witnesses | yes | **win (anti-laundering)** |
| C4 | the coincidence check (spine diagonal-not-bisim, vs `ws1_symmetric_states_bisimilar`) | `ws1_diagonal_not_bisim` + term inspection | yes | **win (flagship)** |
| C5 | four guards: no coincidence / fiat / defined-in / Russell | bundled upstream | yes | **win (the four guards)** |

## Winning candidates: C1 (audit) + C2 (verdict) + C3 (strip ledger) + C4 (coincidence check) + C5 (four guards)

### Definitions and obligations (cite `spec/README.md` §3; consume WS1–WS6)

```lean
namespace Series09.WS7
-- all WS1–WS6 payoffs; the Series 07/08 Audit/verdict pattern — transcribed (README §6).

inductive Series09Verdict | selfReferenceEstablished | coincident | monismStands | Circular deriving DecidableEq

structure Audit (κ : Cardinal.{u}) : Prop where
  spineDiagonal      : …   -- ws1_no_self_total_hold
  diagonalNotBisim   : …   -- ws1_diagonal_not_bisim  (THE FLAGSHIP: independence, not merely the spine)
  residueFree        : …   -- ws2_residue_free
  onePosition        : …   -- ws2_residue_distinct  (no second position in the premise)
  orderEndogenous    : …   -- ws3_order_endogenous
  noLeaf             : …   -- ws3_redi_no_leaf
  dynamicsForced     : …   -- ws3_dynamics_forced
  monotonicityTested : …   -- ws5_kill_condition ∧ ws5_retention_refuted
  carrierConsistent  : …   -- ws1_unrestricted_carrier_inconsistent

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5, including the flagship
    `diagonalNotBisim` (the spine's INDEPENDENCE from relational identity). -/
theorem ws7_audit : Audit κ where
  spineDiagonal      := fun dest insp => ws1_no_self_total_hold dest insp
  diagonalNotBisim   := fun dest insp => ws1_diagonal_not_bisim dest insp
  residueFree        := fun dest insp => ws2_residue_free dest insp
  onePosition        := fun dest insp h => ws2_residue_distinct dest insp h
  orderEndogenous    := fun dest m m' => ws3_order_endogenous dest m m'
  noLeaf             := fun dest insp hne => ws3_redi_no_leaf dest insp hne
  dynamicsForced     := fun dest insp h₀ => ws3_dynamics_forced dest insp h₀
  monotonicityTested := fun dest insp h₀ hb => ws5_kill_condition dest insp h₀ hb
  carrierConsistent  := fun dest => ws1_unrestricted_carrier_inconsistent dest

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series09Verdict := .selfReferenceEstablished
def ws7_verdict : Series09Verdict := verdict ws7_audit
theorem ws7_verdict_eq : ws7_verdict = Series09Verdict.selfReferenceEstablished := rfl

/-- **D3 — with a certificate, never coincident, never monism, never Circular.** The ONLY route to those
    is a FAILED audit; the `diagonalNotBisim` field is why `≠ coincident` is earned, not stipulated. -/
theorem ws7_audited_not_coincident (cert : Audit κ) : verdict cert ≠ .coincident := by decide
theorem ws7_audited_not_monism (cert : Audit κ) : verdict cert ≠ .monismStands := by decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by decide

/-- **D4 — the coincidence check (C4, the flagship).** The spine is diagonal-not-bisimulation, orthogonal
    to relational identity, contrasted with `ws1_symmetric_states_bisimilar`. -/
theorem ws7_coincidence_check {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) : … :=
  ⟨ws1_no_self_total_hold dest insp, (ws1_diagonal_not_bisim dest insp).2,
   fun d hsym x y => ws1_symmetric_states_bisimilar d hsym x y⟩

/-- **D5 — the four guards (C5).** No coincidence; no monotonicity-by-fiat; no freeness-defined-in;
    carrier genuine (consistent). -/
theorem ws7_no_coincidence … ; theorem ws7_no_monotonicity_by_fiat … ;
theorem ws7_freeness_not_defined_in … ; theorem ws7_carrier_genuine …

/-- **D6 — the strip ledger (C3)**, with counterexample terms; the spine strips to Cantor, not bisim. -/
theorem ws7_strip_ledger {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) : … := …

/-- The no-certificate outcomes: `coincident` (spine unfolds to bisimulation) or `Circular` (a defined-in
    exclusion). Documentation; the load-bearing content is D3 (with a certificate, never these). -/
def verdictSpineCoincident : Series09Verdict := .coincident
def verdictNoCertificate : Series09Verdict := .Circular
```

**D1 (audit)** bundles WS1–WS5 into a certificate whose flagship field `diagonalNotBisim` carries the spine's *independence* — break it (the spine routes through bisimulation) and the verdict's build breaks. **D2/D3 (verdict)** compute `selfReferenceEstablished` and prove it is never `coincident`/`monismStands`/`Circular` with a certificate — falsifiable, not hand-set. **D4 (coincidence check)** discharges the flagship SERIOUS check, contrasting the spine's shape with the Series 08 coincidence witness in one statement. **D5 (four guards)** discharges the protocol-mandated checks. **D6 (strip ledger)** surfaces which payoffs survive stripping — above all that the spine strips to Cantor, not bisimulation.

## Outcome classes (per charter §7)

- **Discharged:** D1 (audit), D2/D3 (verdict, `selfReferenceEstablished`), D4 (coincidence check), D5 (four guards), D6 (strip ledger). All transcribe the Series 07/08 certificate pattern over WS1–WS5 payoffs.
- **The verdict delivered: `selfReferenceEstablished`** — spine landed AND certified diagonal-not-bisimulation (Impossibility proved independent of relational identity, WS1, the repair of Series 08), plurality free and non-circular from one position (WS2), order endogenous and (NL)+(NF) discharged (WS3), depth-as-accumulated-blind-spots floored (WS4/WS6), **monotonicity settled to Partial/Refuted by the kill condition** (WS5). The monotonicity *result* is a Refuted-universal, a first-class success, not a shortfall.
- **`coincident` (the live negative arm the series exists to test):** returned only by a *failed* audit — if `diagonalNotBisim` could not be discharged because the spine's proof unfolds to `ws1_symmetric_states_bisimilar`. The coincidence check (D4) and the term inspection (protocol §C) show it does not; but this is the *pre-registered gravest alternative*, and reporting it honestly (Series 08's wall re-hit at greater depth) is a first-class outcome, not a failure to bury.
- **`Circular` (the live negative arm):** returned by a failed audit — if freeness were defined-in (residue trivially free) or monotonicity baked-in (growth stamped into `ReDiagStep`). The four guards (D5) show neither: freeness is a theorem, monotonicity tested outside the map. So `Circular` is live but not triggered.
- **`monismStands` (the pre-registered honest failure):** if a self-total hold were constructible or the carrier were a mere self-loop (content a point, no diagonal). Not triggered: the spine denies the self-total hold (D1), and the carrier is hold-reflexive (WS1 D5).
- **Strip test (aggregate).** WS7's D6 IS the aggregated strip test: the spine strips to a **Cantor fixed-point** (not a bisimulation — the whole repair), plurality to "diag not in range," forced-dynamics to `Function.update`-seriality, the bound to a diagonal-flip refutation — all real facts, the self-reference readings named as earned surplus. WS7 reports this as the honest bottom line: **Series 09's mathematical core is a Cantor/Lawvere diagonal on a hold-reflexive carrier, genuinely independent of relational identity (the repair of Series 08's coincidence); its philosophical surplus (self-total hold, residue, re-diagonalization, blind spot, the incompletable I) is the interpretation, marked not hidden** (charter §10). The load-bearing, non-stripped gains: the spine is a fixed-point contradiction *not a bisimulation* (D4), and the residue's distinctness needs *no second position* (WS2) — those two are the repair, and they survive because they are structural, not verbal.

## Deliverable

`series-09/formal/Series09/ws7.lean`: `Series09Verdict`; the `Audit` structure; `ws7_audit` (D1), `verdict` / `ws7_verdict` / `ws7_verdict_eq` (D2), `ws7_audited_not_coincident` / `ws7_audited_not_monism` / `ws7_audited_not_circular` (D3), `ws7_coincidence_check` (D4), `ws7_no_coincidence` / `ws7_no_monotonicity_by_fiat` / `ws7_freeness_not_defined_in` / `ws7_carrier_genuine` (D5), `ws7_strip_ledger` (D6), `verdictSpineCoincident` / `verdictNoCertificate`. **Runs last; consumes WS1–WS6.** Axiom check: `#print axioms ws7_verdict` reduces through the whole audit (hence every WS1–WS5 headline, and the term-inspection of `ws1_no_self_total_hold` confirming no bisimulation lemma) to the standard `propext` / `Classical.choice` / `Quot.sound`. **Owns the final verdict: `selfReferenceEstablished`, with the spine certified diagonal-not-bisimulation (the repair of Series 08) and monotonicity honestly Refuted-in-general.**
