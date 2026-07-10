# WS7 — The anti-trivialization audit

**Design doc. Series 6, runs last, audits WS3–WS6. Owns: the aggregated coincidence/strip discipline, the mechanized distinctness anchors (the payoffs are distinct consequences, not one definition), the strip-test ledger (which payoffs survive deleting their load-bearing word), and the typed `ProgramVerdict` — extended to Series 6's `{ oneDiagonal, payoffsEstablished, Trivialized }` — that decides the central finding: do groundlessness, plurality, and directed plural time genuinely reduce to the single incompletion of self-knowledge (the diagonal), "one diagonal, substantively", or is that unification an artifact of over-strong definitions (a conjunction)?**

*Series 6 is standalone; `ProgramVerdict` (Series 4/5) is transcribed into `series-6/formal/ws7.lean` and re-namespaced `Series6.WS7`, then extended (see `spec/README.md` §5). All WS3–WS6 payoff theorems are consumed by name, not re-proved. Shared objects (`Proc`, `Δ`, `Moment`, `stepM`, `prec`, `faceAt`) are defined in `spec/README.md` §2–§4.*

## The object at stake

The charter (§5.5, §7) stakes the program's headline on a reduction: groundlessness, plurality, and directed plural time are *three faces of the one incompletion* — the diagonal that forbids the self-survey to close. The characteristic risk (§8) is not failure but *cheap* success: the diagonal explains all three by being painted onto each, so their interconnection is assumed rather than found. WS7 is the audit built to catch that. It must (a) aggregate, as one object, the per-payoff coincidence status and per-workstream strip test already carried by WS3–WS6; (b) mechanize **distinctness anchors** — that the payoffs are *distinct statements that coincide*, not one definition wearing several names (so the unification, if claimed, is a claim about distinct facts); (c) record the **strip-test ledger** — which payoffs survive deleting their load-bearing word (earned) versus which reduce to a bare fixed-point/order fact (flagged); and (d) emit the **typed verdict**, `payoffsEstablished` unless WS6's `ws6_one_engine` genuinely reduces groundlessness+plurality to one residue mechanism, `Trivialized` if WS3's `Δ` is painted on or the payoffs collapse to one definition, `oneDiagonal` only if *every* payoff derives from the diagonal engine. The verdict is not a summary appended to the work; it *is* the deliverable, and it is designed to be able to come back negative.

This mirrors the discipline that landed Series 4's "one finitude" at a conjunction and Series 5's "one double-unboundedness" at `payoffsEstablished` — one genuine derivation plus distinctness anchors, with an honest "one derivation, not two" count. Series 6 pre-registers the same shape and the same honesty about the count.

**Ambient theory.** `spec/README.md` §2–§5. The audited payoffs are the six of charter §5.5: **P1** atomless-and-plural (`ws6_atomless_and_plural`, WS1+WS6), **P2** groundlessness-and-plurality-from-one-engine (`ws6_one_engine`, WS6 — the reduction), **P3** directed endogenous arrow (`ws4_arrow_strict` + `ws4_arrow_endogenous`, WS4), **P4** plural relational time (`ws5_causal_partial_order` / totality↔agreement, WS5), **P5** no view from nowhere (`ws6_no_view`, WS6), **P6** incompleteness re-read as engine (`ws3_omega_orbit` + `ws6_incompleteness_inherited`, WS3+WS6). The single fact under all of them is the diagonal: `ws3_fpf_eq_incompleteness_eq_nontermination` / no moment at rest (`∀ m, stepM m ≠ m`). The self-audit is Claude-auditing-Claude — a stated limitation (charter §9, "interpretive gap / self-audit"), not claimed independence; the distinctness anchors and the strip-test outcomes are the objective part.

## Candidates (for the form of the verdict)

### C1 — The payoffs as one conjunction, honestly labelled (`ws7_payoffs_hold`)

```lean
theorem ws7_payoffs_hold {κ} (hinf : ℵ₀ ≤ κ) :
      ws6_atomless_and_plural κ ∧ ws6_one_engine κ ∧ ws4_arrow_strict κ
    ∧ ws5_causal_partial_order κ ∧ ws6_no_view_from_nowhere κ ∧ ws6_incompleteness_inherited κ
```
The null-reduction candidate: the payoffs all hold, and WS7 reports exactly that — a conjunction, not a derivation.

- **Success condition:** each conjunct is a discharged WS3–WS6 theorem; the conjunction is their `And.intro`.
- **Failure mode:** **none as a statement** — it is true by construction — but it is *not the finding*. Reporting only C1 would be the Series 4 outcome (one finitude downgraded to a conjunction) with no attempt at the reduction, and would leave the headline "one diagonal" neither earned nor refuted. It is the honest floor, not the verdict.

**Paper triage.** True and cheap; the Series 4/5 discipline in its minimal form. **Retain as the floor `ws7_payoffs_hold`** — the conjunction the verdict machinery sits on — but it cannot *be* the verdict, or the central question is dodged.

### C2 — Genuine derivation of every payoff from the diagonal (`oneDiagonal`, the ceiling)

```lean
theorem ws7_derivation_from_diagonal {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, stepM m ≠ m) →                 -- the one incompletion (ws7_one_incompletion)
      ws6_atomless_and_plural κ ∧ ws6_one_engine κ ∧ ws4_arrow_strict κ
    ∧ ws5_causal_partial_order κ ∧ ws6_no_view_from_nowhere κ ∧ ws6_incompleteness_inherited κ   -- ALL six, from the diagonal alone
```
The aspirational form: every payoff a *consequence* of `ws7_one_incompletion`, so the reduction is total and the verdict is `oneDiagonal`.

- **Success condition:** all six conjuncts derive from fixed-point-freeness with no second load-bearing structure consumed.
- **Failure mode:** **conjunction mislabelled as derivation.** Two of the six provably consume a *second* structure: P4 (relativity) needs the two-sided `faceAt` mismatch to forbid agreement (the diagonal alone gives perpetuity, not incomparability — WS5's own strip), and P2 (`ws6_one_engine`) is exactly the "same residue mechanism" reduction WS6 flags as its signature risk. If those are asserted as diagonal-derivations when they in fact take a face or an argued-not-mechanized identification, the derivation is a laundered conjunction — the precise failure the charter (§5.6) names.

**Paper triage.** The ceiling, and it **resists** — expected to hold for the payoffs that are literally the diagonal's properness (groundlessness: no completion ⇒ no bud stays closed; the arrow: properness of the survey; no-view: inhabited/surveyed non-completion) and to *fail* to reduce P2 and P4 without a second structure. Not the built verdict; its **honest partial** (which conjuncts genuinely derive) is `ws7_derivation_from_diagonal` with an explicit count. **Reject as the verdict; keep the derivation theorem with the honest count.**

### C3 — The anchor + strip-ledger machinery deciding the verdict deterministically (the lead)

```lean
def verdict (paintedOn allDerive anchorsDistinct : Bool) : ProgramVerdict := ...
theorem ws7_verdict {κ} (hinf : ℵ₀ ≤ κ) : verdict false false true = .payoffsEstablished := rfl
```
The verdict is a total function of three mechanized inputs: WS3's strip result (`Δ` painted on?), the derivation count (do all six derive?), and the distinctness anchors (are the payoffs distinct facts?). WS7 supplies the three booleans as *theorems* and reads the verdict off `rfl`.

- **Success condition:** each input is a discharged theorem (`ws3_diagonal_drives` ⇒ not painted-on; `ws7_derivation_from_diagonal` ⇒ the count; `ws7_distinctness_anchors` ⇒ distinct); the verdict reduces definitionally.
- **Failure mode:** **the verdict rests on a laundered payoff.** If an anchor is `rfl` on one definition (two "distinct" payoffs that are the same statement, the Series 5 S2a/S2b tell), or if the strip ledger records a survivor as earned, the deterministic verdict is deterministically *wrong*. The machinery must consume anchors that are genuine two-statement distinctnesses and a ledger whose earned/flagged calls are each a strip theorem.

**Paper triage.** The intended shape: the verdict is not adjudicated by hand but *computed* from three objective inputs, so the audit is reproducible and the honesty is in the inputs, not the verdict function. **Winner**, conditional on the anchors being genuine distinctnesses (decidable-on-paper test below) and the ledger being strip theorems, not annotations.

## Paper-decidable triage

| Candidate | Coalgebra of the verdict | Gate | Verdict role |
|---|---|---|---|
| C1 conjunction `ws7_payoffs_hold` | six discharged theorems, `And.intro` | trivially true | the **floor**, not the finding |
| C2 total derivation `oneDiagonal` | all six from `stepM m ≠ m` | P2/P4 consume a second structure ⇒ resists | the **ceiling**; kept as honest-count derivation |
| C3 anchor+ledger machinery | `verdict` of three theorem-inputs | anchors genuine two-statement distinctnesses; ledger = strip theorems | **the built verdict** |

## Winning candidate: C3 (the deterministic verdict over mechanized inputs), floor C1 and honest-count C2 as its inputs

The decisive move: **the verdict is a function, not a judgement.** Its three arguments are theorems, so the only place honesty can be gamed is the inputs, and each input is itself strip-tested. The predicted output is `payoffsEstablished` — the honest middle — because the derivation count comes back *fewer than six* (C2 resists on P2 and P4) while the anchors and strip ledger refute `Trivialized`.

### Definitions

```lean
namespace Series6.WS7
-- transcribed: ProgramVerdict (Series 4/5) then EXTENDED; consumed by name from WS3–WS6:
-- ws3_diagonal_drives, ws3_fpf_eq_incompleteness_eq_nontermination, ws3_omega_orbit,
-- ws4_arrow_strict, ws4_arrow_endogenous, ws5_causal_partial_order, ws6_atomless_and_plural,
-- ws6_one_engine, ws6_no_view, ws6_incompleteness_inherited; carrier proc_ext, stepM, faceAt.

/-- The typed program verdict, extended to Series 6's three outcomes. -/
inductive ProgramVerdict
  | oneDiagonal          -- every §5.5 payoff DERIVED from the diagonal engine (the reduction is total)
  | payoffsEstablished   -- payoffs hold and are distinct where mechanized; common origin argued, not fully mechanized
  | Trivialized          -- Δ painted on (WS3 strip fails) OR the payoffs collapse to one definition

/-- The verdict as a total function of three mechanized inputs. -/
def verdict (paintedOn allDerive anchorsDistinct : Bool) : ProgramVerdict :=
  if paintedOn || !anchorsDistinct then .Trivialized
  else if allDerive then .oneDiagonal
  else .payoffsEstablished
```

### The obligations, each a signature + strategy + paper-decidable verdict

**T1 — `ws7_one_incompletion` (the single fact under all payoffs).**
```lean
theorem ws7_one_incompletion {κ} (hinf : ℵ₀ ≤ κ) : ∀ m : Moment κ, stepM m ≠ m
```
*Strategy:* this is `ws3_fpf_eq_incompleteness_eq_nontermination`'s fixed-point-free reading, re-exported as *the* fact the audit measures every payoff against — no moment is its own successor, because the survey provably misses `d_n` (Cantor, `ws6_lawvere_incomplete`). WS7 does not re-prove it; it names it as the reduction's putative source term. *Paper-decidable:* yes — a re-export of a discharged WS3 theorem.

**T2 — `ws7_payoffs_hold` (the six payoffs, as a conjunction, honestly).**
```lean
theorem ws7_payoffs_hold {κ} (hinf : ℵ₀ ≤ κ) :
      ws6_atomless_and_plural κ ∧ ws6_one_engine κ ∧ ws4_arrow_strict κ
    ∧ ws5_causal_partial_order κ ∧ ws6_no_view_from_nowhere κ ∧ ws6_incompleteness_inherited κ
```
*Strategy:* `And.intro` of six discharged WS3–WS6 theorems. Labelled a **conjunction**, per the Series 4/5 discipline — that the payoffs *hold* is not that they *reduce*. *Paper-decidable:* yes; it is the floor C1.

**T3 — `ws7_derivation_from_diagonal` (which payoffs GENUINELY derive — the honest count).**
```lean
theorem ws7_derivation_from_diagonal {κ} (hinf : ℵ₀ ≤ κ) :
    -- DERIVE from ws7_one_incompletion alone:
    ( (∀ m, stepM m ≠ m) → ws6_groundlessness_from_diagonal κ )              -- no completion ⇒ no bud stays closed
  ∧ ( (∀ m, stepM m ≠ m) → ws4_arrow_strict κ )       -- properness of the survey ⇒ the arrow
  ∧ ( (∀ m, stepM m ≠ m) → ws6_no_view_from_nowhere κ )                 -- non-completion ⇒ inhabited/surveyed asymmetry
    -- DO NOT derive from the diagonal alone (a second structure is consumed):
  ∧ ¬ DerivesFromDiagonalAlone (ws5_causal_partial_order κ)        -- P4 consumes the two-sided faceAt (WS5 strip)
  ∧ (ws6_one_engine κ → PluralityReductionArgued κ)        -- P2 argued, not fully mechanized (the signature risk)
```
*Strategy:* the three positive arrows are genuine consequences — groundlessness *is* "no bud stays closed" (the contrapositive of a completed self-survey the diagonal forbids), directionality *is* the properness of the survey (`ws4_arrow_strict` consumes only that the survey is a proper sub-object, i.e. the diagonal), and no-view *is* non-completion read as inhabited/surveyed. The two negatives are the honest count: P4 (relativity) provably needs the mismatched `faceAt` to turn perpetuity into incomparability — the diagonal alone gives a total-order-compatible perpetuity — and P2 (`ws6_one_engine`, that groundlessness and plurality are the *same* residue mechanism) is delivered by WS6 as an argued reduction whose forced form (a single mechanized identity of the two consequences) is the open obligation. **Honest count: three genuine derivations of six; one second structure (the face, P4); one argued-not-mechanized reduction (P2).** This is the exact analogue of Series 5's "one derivation, not two". *Paper-decidable:* the positives consume `ws7_one_incompletion` + the relevant WS4/WS6 statement; the negatives consume the WS5 face-strip and the WS6 `ws6_one_engine` open flag. This theorem sets `allDerive := false`.

**T4 — `ws7_distinctness_anchors` (the payoffs are distinct consequences).**
```lean
theorem ws7_distinctness_anchors {κ} (hinf : ℵ₀ ≤ κ) :
    ws7_groundless_vs_plural_distinct κ      -- groundlessness (no closed bud) ≠ plurality (two non-merging productive threads)
  ∧ ws7_arrow_vs_perpetuity_distinct κ       -- directionality (properness) ≠ mere fpf perpetuity (the frictionless-pendulum row)
  ∧ ws7_incomp_vs_poset_distinct κ           -- faceAt-mismatch incomparability ≠ bare posethood of ≺
```
*Strategy:* three rows, each a *two-statement* distinctness (no `rfl` on one definition — the Series 5 S2a/S2b tell is exactly what these must avoid). Row 1: groundlessness holds of Ω (one thread, no closed bud) while plurality needs two threads — so they are separated by a witness (Ω is groundless and *not* plural), refuting their collapse into one statement; this is the anti-`ws6_one_engine`-laundering row. Row 2: perpetuity holds of a would-be returning orbit (fpf, no rest) while directionality additionally forbids return (properness) — separated because fixed-point-freeness alone does not give the arrow (charter §5.3's frictionless pendulum, mechanized). Row 3: `≺` is a poset generically, but incomparability is *non-empty* only via the mismatched `faceAt` — separated by exhibiting that stripping the face leaves posethood but empties incomparability. **Three anchors** (Series 5 managed three; Series 4 two). *Paper-decidable:* each row is a witnessed non-equivalence of two discharged statements. This theorem sets `anchorsDistinct := true`.
- *Failure recorded if it were to fail:* if any anchor is `rfl` on one definition (the two "distinct" payoffs are the same statement), that payoff pair *has* collapsed to one definition — `anchorsDistinct := false`, and the verdict flips to `Trivialized`. This is the SERIOUS check the self-audit must survive.

**T5 — `ws7_strip_ledger` (aggregated strip-test outcomes).**
```lean
theorem ws7_strip_ledger {κ} (hinf : ℵ₀ ≤ κ) :
    StripSurvives (ws3_diagonal_drives κ)   "delete «diagonal» from Δ"   -- EARNED: Δ loses its definiens (WS3 D4)
  ∧ StripSurvives (ws4_arrow_endogenous κ) "delete external time"     -- EARNED: a direction remains on the survey order
  ∧ StripSurvives (ws5_incomp_nonempty κ)   "delete «face» from ≺"      -- EARNED iff incomparability needs the mismatched face
  ∧ StripFlags   (ws6_no_view_naive κ)      "delete «residue» from no-view" -- FLAGGED if it is «the limit does not exist» relabelled
```
*Strategy:* aggregate the four per-workstream strip tests the charter (§7) writes into each statement. WS3's is a *syntactic* survival (delete `residue`/`survey` and `Δ` fails to elaborate — the strongest form, from `ws3_diagonal_drives`). WS4's: delete the external ℕ index and a direction must remain, carried by the proper-sub-object order on self-surveys, or the arrow is imposed. WS5's: delete "face" and incomparability must be earned from the mismatched surveys, not read off "it is a poset" (mirrors Series 5's laundered-poset risk). WS6's: delete "residue" from no-view and check whether the inhabited/surveyed asymmetry is load-bearing or is "the limit does not exist" relabelled (the charter §5.5 severe anti-laundering duty). **Ledger: the payoffs that need their deleted word are earned; a payoff that survives the strip as a bare fixed-point/order fact is flagged** — exactly the Series 5 outcome where V2 laundered and V3's face wrapper was inert. *Paper-decidable:* each row is a strip theorem already owned by its workstream; WS7 conjoins them and records earned-vs-flagged. This theorem, together with T4, corroborates `paintedOn := false` (from `ws3_diagonal_drives`).

**T6 — `ws7_verdict` (the typed verdict).**
```lean
theorem ws7_verdict {κ} (hinf : ℵ₀ ≤ κ) :
    verdict (paintedOn := false)          -- ws3_diagonal_drives: Δ is uniquely residue-driven (not painted on)
            (allDerive := false)          -- ws7_derivation_from_diagonal: three of six derive; P2 argued, P4 takes the face
            (anchorsDistinct := true)     -- ws7_distinctness_anchors: three genuine two-statement rows
      = ProgramVerdict.payoffsEstablished := rfl
```
*Strategy:* the three booleans are the outputs of T3/T4 and `ws3_diagonal_drives`; `verdict false false true` reduces definitionally to `payoffsEstablished`. The verdict is `rfl` — no axioms beyond the payoff theorems it names — exactly as Series 5's `ws7_verdict_eq` was a definitional check on the inductive `ProgramVerdict`. *Paper-decidable:* yes — a `rfl` on the `verdict` function once the three inputs are theorems.

## Outcome classes (per charter §7) — the verdict IS the outcome

Pre-registered, decided by the three inputs:

- **`payoffsEstablished` (predicted).** `paintedOn = false` (WS3's `Δ` is the unique residue-driven map), `anchorsDistinct = true` (three genuine rows), `allDerive = false` (three of six payoffs derive from the diagonal; P4 consumes the two-sided face, P2's same-mechanism reduction is argued not fully mechanized). The honest middle — payoffs hold, are distinct where mechanized, common origin argued. Matches Series 4's conjunction and Series 5's `payoffsEstablished`.
- **`oneDiagonal` (the ceiling, if WS6 delivers).** Reached only if `ws6_one_engine` is strengthened to a *mechanized* identity of the groundlessness and plurality consequences (P2 forced, not argued) *and* P4's incomparability is shown to derive from the diagonal without a second face structure — i.e. `allDerive = true`. Pre-registered as reachable, not expected: the face is a genuine second lever (charter §5.4).
- **`Trivialized` (the sharp negative, a success).** Reached iff WS3 reports `Δ` painted on (`ws3_diagonal_drives`'s uniqueness fails, `paintedOn = true`) *or* an anchor collapses to `rfl` on one definition (`anchorsDistinct = false`) — the payoffs are one definition wearing several names. Returning it honestly is a program success (charter §7, §8).

**Self-audit disclosure (charter §9).** These audits are Claude-auditing-Claude — a stated limitation, not claimed independence. The subjective part is the *reading* of which forced forms count as "genuinely independent"; the **objective part is the mechanized distinctness anchors (`ws7_distinctness_anchors`) and the strip-test ledger (`ws7_strip_ledger`)** — witnessed non-equivalences and elaboration facts a re-runner can check without trusting the auditor's judgement. The verdict is a `rfl` function of those objective inputs, so the audit is reproducible; what is not delegated to the machine is disclosed as interpretation.

## Deliverable

`series-6/formal/ws7.lean`: transcribed `ProgramVerdict` (extended to `{ oneDiagonal, payoffsEstablished, Trivialized }`); the `verdict` function; the payoff theorems consumed by name from WS3–WS6; `ws7_one_incompletion` (T1), `ws7_payoffs_hold` (T2), `ws7_derivation_from_diagonal` with the honest three-of-six count (T3), `ws7_distinctness_anchors` — three mechanized rows (T4), `ws7_strip_ledger` — the four aggregated strip tests (T5), `ws7_verdict = payoffsEstablished` (T6). Axiom note: `ws7_verdict` reduces to `rfl` and its `#print axioms` shows only the standard three (`propext` / `Classical.choice` / `Quot.sound`), as Series 5's verdict did; `ws7_distinctness_anchors` must depend on *no* axioms beyond the standard three, since it is the objective part of the self-audit. A `ws7_verdict` that is not `rfl` — that required a hand-supplied proof term — would mean the verdict was adjudicated, not computed, and fails the deliverable.
