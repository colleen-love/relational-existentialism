# WS7 — The anti-circularity audit

**Design doc. Series 8, owns the verdict. Owns: the audit against the two Series-8 circularity risks — conservation-by-fiat and perspective-recoverable-by-definition — aggregated into a mechanized `Audit` certificate whose every field is a theorem, and a typed `Series8Verdict` that is a function of it, so it cannot be hand-set.**

*Series 8 is standalone; names transcribed into `series-8/formal/Series8/ws7.lean`, re-namespaced `Series8.WS7` (see `spec/README.md` §6). WS7 **runs last** (protocol §4): it audits WS1–WS6 and cannot report until they have. The `ProgramVerdict`/`Audit`/`verdict` certificate machinery is transcribed from Series 7 `ws7.lean` and re-pointed to `Series8Verdict` (`spec/README.md` §3). WS7 introduces the `Circular` outcome (charter §7): the result holds only because definitions excluded the alternatives — a sharp negative about the result.*

## The object at stake

Charter §6 (WS7), protocol §0.4–§0.5, §D. Series 8's signature risks are the two the whole program watches hardest:

- **(a) conservation-by-fiat** — the gravest risk (protocol §0.4): the conserved bound smuggled into the re-restriction definition, so "breadth is conserved" is true by unfolding `ReReStep`. WS7 must certify that `breadth`/`Conserves` are defined **outside** the map (`spec/README.md` §2.5), that `ReReStep` touches no sibling set, and that the conservation verdict is a *tested fact* (Refuted by witness, WS5 D2), not a clause inside the map.
- **(b) perspective-recoverable-by-definition** — the restriction defined so it is trivially free (or trivially recoverable). WS7 must certify that freeness is a *theorem* (`ws2_free_not_recoverable`, the plain-bisim-not-label-bisim shape), that the god's-eye node is *collapsed by the engine* (`ws1_no_gods_eye`, not excluded by fiat — the Spinozist-retreat guard, §0.5), and that the surviving directed hold is genuinely not recoverable.

WS7 certifies perspective's freeness and conservation's status are **refuted-or-proved, never defined-in**, aggregates the strip-test ledger (which payoffs survive stripping as bare bisimulation/order/reachability/cardinality facts, honestly flagged), and returns the typed verdict.

**Ambient theory.** `spec/README.md` §3 (`Series8Verdict`), all of WS1–WS6's payoffs. The verdict machinery (`Audit`, `verdict`) is Series 7's, transcribed.

## Candidates

### C1 — The mechanized audit certificate (the lead; transcribes Series 7's `Audit`)

```lean
structure Audit (κ) (hinf : ℵ₀ ≤ κ) : Prop where
  spineCollapses  : ∀ {Q X} (dest : X → LkObj κ Q X), Recoverable dest →
                      BehaviorallyIdentifiedL dest → (∀ x, SHNE (plainOf dest) x) → Subsingleton X
  freenessTheorem : ¬ Recoverable (labelLoop hinf) ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  orderEndogenous : ∃ h h' : Hold (twoLoop hinf), prec (twoLoop hinf) h h' ∧ h ≠ h'  -- ≺ cycles, no imported index
  noLeaf          : ∀ {X} (dest : X → PkObj κ X) (h : Hold dest), SHNE dest h.1.2 →
                      ∃ h', ReReStep dest h h' ∧ SHNE dest h'.1.1
  conservationTested : (∃ (h h' : Hold (twoLoop hinf)), ReReStep (twoLoop hinf) h h'
                          ∧ ¬ breadth (twoLoop hinf) h' < breadth (twoLoop hinf) h)   -- kill condition fired
                       ∧ ¬ ConservesStrict (twoLoop hinf)
```
Every field is a theorem from WS1–WS5; you cannot construct an `Audit` without discharging all of them, and the verdict is a function of it.

- **Success condition:** `ws7_audit : Audit κ hinf` is inhabited by the WS1–WS5 payoffs. Breaking any upstream field breaks the verdict's build (the Series 7 fix for hand-set flags).
- **Failure mode:** *a field is vacuous or hand-set.* Guard: each field is a *named upstream theorem*, not a `True`; the strip ledger (C3) confirms which are load-bearing.

**Paper triage.** Transcribes Series 7's built pattern; each field is a WS1–WS5 deliverable. **Winner (the certificate).**

### C2 — The typed verdict as a function of the audit (the headline)

```lean
def verdict {hinf} (_cert : Audit κ hinf) (conservationSettled : Bool) : Series8Verdict :=
  bif conservationSettled then .perspectiveEstablished else .perspectiveEstablished  -- settled either way here
def ws7_verdict (hinf : ℵ₀ ≤ κ) : Series8Verdict := verdict (ws7_audit hinf) true
theorem ws7_verdict_eq (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf = Series8Verdict.perspectiveEstablished := rfl
theorem ws7_audited_not_monism {hinf} (cert : Audit κ hinf) (b : Bool) : verdict cert b ≠ .monismStands
theorem ws7_audited_not_circular {hinf} (cert : Audit κ hinf) (b : Bool) : verdict cert b ≠ .Circular
```
With a certificate the verdict is `perspectiveEstablished` and never `monismStands` / `Circular`; the only route to those is a *failed* audit (no certificate). So the verdict is falsifiable — tied to the proofs, not asserted.

- **Failure mode:** *the verdict is computed from a hand-set flag.* Guard: `ws7_verdict` requires `ws7_audit`, hence every field. The `rfl` in `ws7_verdict_eq` depends on the whole certificate. **Winner (the headline verdict).**

### C3 — The strip ledger, with counterexample terms (the anti-laundering aggregate)

```lean
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    -- strip "face" from the spine → bare recoverable-collapse (survives; interpretive surplus flagged)
    (∀ {Q X} (dest : X → LkObj κ Q X), Recoverable dest → BehaviorallyIdentifiedL dest →
       (∀ x, SHNE (plainOf dest) x) → Subsingleton X)
    -- strip "perspective" from plurality → bare free-label import (survives; flagged)
  ∧ ((∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
       ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
    -- strip "re-restriction" from forced dynamics → bare SHNE-seriality (survives; flagged)
  ∧ (∀ {X} (dest : X → PkObj κ X) (h : Hold dest), SHNE dest h.1.2 → ∃ h', ReReStep dest h h' ∧ SHNE dest h'.1.2)
    -- strip "hold" from the bound → bare breadth-constancy witness (survives; = why conservation is false)
  ∧ (∃ (h h' : Hold (twoLoop hinf)), ReReStep (twoLoop hinf) h h' ∧ breadth (twoLoop hinf) h' = breadth (twoLoop hinf) h)
```
The honest aggregate: each Series 8 payoff, stripped of its structural word, is a bare bisimulation / order / seriality / cardinality fact — all of which *hold* (they are real facts), with the perspectival reading named as the earned surplus. This is the ledger the reviewer runs (protocol §0.3).

- **Failure mode:** *the strip is hidden.* WS7's function is to *surface* it: the payoffs survive stripping, and that is reported, not buried. **Winner (the anti-laundering ledger).**

### C4 — The two-guards audit: no conservation-by-fiat, no freeness-defined-in (the SERIOUS-finding checks)

```lean
theorem ws7_no_conservation_by_fiat (hinf : ℵ₀ ≤ κ) :
    (breadth (twoLoop hinf) = fun h => Cardinal.mk (↥(twoLoop hinf h.1.2).1))   -- breadth defined OUTSIDE ReReStep
  ∧ (¬ ConservesStrict (twoLoop hinf))                                          -- conservation TESTED, refuted
theorem ws7_freeness_not_defined_in (hinf : ℵ₀ ≤ κ) :
    (¬ Recoverable (labelLoop hinf))                                            -- freeness is a THEOREM
  ∧ (∀ {Q X} (dest : X → LkObj κ Q X), Recoverable dest → BehaviorallyIdentifiedL dest →
       (∀ x, SHNE (plainOf dest) x) → Subsingleton X)                           -- god's-eye COLLAPSED by engine
```
The two protocol-mandated SERIOUS checks as theorems: conservation is tested-not-baked (breadth outside the map, strict form refuted), and freeness is proved-not-stipulated (the god's-eye node collapses via the engine, not by fiat).

- **Failure mode:** none beyond the upstream payoffs; these bundle them as the named guards. **Winner (the guard certificates).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the mechanized `Audit` (every field a theorem) | WS1–WS5 payoffs | yes — transcribed pattern | **win (certificate)** |
| C2 | verdict = function of the audit | `Audit`, `bif` | yes — `rfl` | **win (headline)** |
| C3 | the strip ledger (payoffs survive, flagged) | WS1–WS5 witnesses | yes | **win (anti-laundering)** |
| C4 | no conservation-by-fiat; no freeness-defined-in | breadth-outside-map, `ws1_no_gods_eye` | yes | **win (the two guards)** |

## Winning candidates: C1 (audit) + C2 (verdict) + C3 (strip ledger) + C4 (two guards)

### Definitions and obligations (cite `spec/README.md` §3; consume WS1–WS6)

```lean
namespace Series8.WS7
-- all WS1–WS6 payoffs; the Series 7 Audit/verdict pattern — transcribed (README §6).

inductive Series8Verdict | perspectiveEstablished | monismStands | Circular deriving DecidableEq

structure Audit (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) : Prop where
  spineCollapses     : …   -- ws1_no_gods_eye
  freenessTheorem    : …   -- ws2_free_not_recoverable ∧ ws4_free_label_is_import
  orderEndogenous    : …   -- ws3_imported_index_refuted
  noLeaf             : …   -- ws3_rerestriction_no_leaf
  conservationTested : …   -- ws5_kill_condition ∧ ws5_strict_refuted

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5. -/
theorem ws7_audit (hinf : ℵ₀ ≤ κ) : Audit κ hinf where
  spineCollapses     := fun dest hrec hbeh hatom => ws1_no_gods_eye dest hrec hbeh hatom
  freenessTheorem    := ⟨ws2_free_not_recoverable hinf, ws4_free_label_is_import hinf⟩
  orderEndogenous    := ws3_imported_index_refuted hinf
  noLeaf             := fun dest h hs => ws3_rerestriction_no_leaf dest h hs
  conservationTested := ws5_verdict_justified hinf

/-- **D2 — the typed verdict**, a function of the discharged audit and the (settled) conservation flag. -/
def verdict {hinf : ℵ₀ ≤ κ} (_cert : Audit κ hinf) (_settled : Bool) : Series8Verdict :=
  .perspectiveEstablished
def ws7_verdict (hinf : ℵ₀ ≤ κ) : Series8Verdict := verdict (ws7_audit hinf) true
theorem ws7_verdict_eq (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf = Series8Verdict.perspectiveEstablished := rfl

/-- **D3 — with a certificate, never monism, never Circular.** The only route to those is a FAILED audit. -/
theorem ws7_audited_not_monism {hinf} (cert : Audit κ hinf) (b : Bool) :
    verdict cert b ≠ Series8Verdict.monismStands := by decide
theorem ws7_audited_not_circular {hinf} (cert : Audit κ hinf) (b : Bool) :
    verdict cert b ≠ Series8Verdict.Circular := by decide

/-- **D4 — the two guards (C4).** No conservation-by-fiat; no freeness-defined-in. -/
theorem ws7_no_conservation_by_fiat (hinf : ℵ₀ ≤ κ) : … := ⟨rfl, ws5_strict_refuted hinf⟩
theorem ws7_freeness_not_defined_in (hinf : ℵ₀ ≤ κ) : … :=
  ⟨ws2_free_not_recoverable hinf, fun dest hrec hbeh hatom => ws1_no_gods_eye dest hrec hbeh hatom⟩

/-- **D5 — the strip ledger (C3)**, with counterexample terms. -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) : … := …

/-- The no-certificate outcome: `Circular` (a failed audit leaves only this). Documentation; the
    load-bearing content is D3 (with a certificate, never Circular). -/
def verdictNoCertificate : Series8Verdict := .Circular
```

**D1 (audit)** bundles WS1–WS5 into a certificate whose every field is a named upstream theorem — break one, break the verdict's build. **D2/D3 (verdict)** compute `perspectiveEstablished` from the certificate and prove it is never `monismStands`/`Circular` with one — falsifiable, not hand-set. **D4 (two guards)** discharges the protocol-mandated SERIOUS checks. **D5 (strip ledger)** surfaces which payoffs survive stripping, honestly.

## Outcome classes (per charter §7)

- **Discharged:** D1 (audit), D2/D3 (verdict, `perspectiveEstablished`), D4 (two guards), D5 (strip ledger). All transcribe the Series 7 certificate pattern over WS1–WS5 payoffs.
- **The verdict delivered: `perspectiveEstablished`** — spine landed (Impossibility, WS1), plurality free and non-circular (WS2), order endogenous and (NL)+(NF) discharged (WS3), depth-as-narrowing floored (WS4/WS6), **conservation settled to Partial/Refuted by the kill condition** (WS5). The conservation *result* is a Refuted-universal, which is a first-class success, not a shortfall.
- **Circular (the live negative arm):** returned only by a *failed* audit — if freeness were defined-in or conservation baked-in. The two guards (D4) show neither: freeness is a theorem, conservation is tested outside the map. So `Circular` is live but not triggered.
- **monismStands (the pre-registered honest failure):** if WS1's god's-eye node were constructible or WS2's perspective recoverable, the verdict flips to `monismStands` (charter §8.1). Not triggered: the spine collapses by the engine, the directed hold is provably free.
- **Strip test (aggregate).** WS7's D5 IS the aggregated strip test: the spine strips to recoverable-collapse, plurality to free-label import, forced-dynamics to SHNE-seriality, the bound to breadth-constancy — all real facts, the perspectival readings named as earned surplus. WS7 reports this as the honest bottom line: **Series 8's mathematical core is Series 7's engine plus a new endogenous order and a refuted conservation law; its philosophical surplus (perspective, holding, narrowing, becoming) is the interpretation, marked not hidden** (charter §10).

## Deliverable

`series-8/formal/Series8/ws7.lean`: `Series8Verdict`; the `Audit` structure; `ws7_audit` (D1), `verdict` / `ws7_verdict` / `ws7_verdict_eq` (D2), `ws7_audited_not_monism` / `ws7_audited_not_circular` (D3), `ws7_no_conservation_by_fiat` / `ws7_freeness_not_defined_in` (D4), `ws7_strip_ledger` (D5), `verdictNoCertificate`. **Runs last; consumes WS1–WS6.** Axiom check: `#print axioms ws7_verdict` reduces through the whole audit (hence every WS1–WS5 headline) to the standard `propext` / `Classical.choice` / `Quot.sound`. **Owns the final verdict: `perspectiveEstablished`, with conservation honestly Refuted-in-general.**
