# Program 2 Series 12 (2.12), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: DESIGNED (Phase B complete; Phase C blind design review pending). Spec batch committed (`born-derisking.md`, `README.md`, `ws1..ws5-design.md`); no `formal/` yet. Current verdict: **PENDING** (computed at WS5, never hand-set; the de-risking's expected close is BORN). This is the third Phase-3 recovery test (`charter-extension-2.md`), execution tier 3, THE WEIGHT: do the imports carry a measure — a probability — and is it the Born rule, `|amp|²`? Two live questions: is there genuine CHANCE (do the imports carry a measure, or is the freedom structureless — DETERMINISTIC), and if so is the measure the SQUARED amplitude (BORN) or another (STOCHASTIC-NOT-BORN)? The Born rule must be EARNED (forced by consistency with Series 2.11's interference, the classical additive measure REFUTED), never named. Honestly uncertain which way it lands; DETERMINISTIC (interference without chance) is a real and respectable outcome. Scope: Series 2.11's real ±1 amplitude — the rebit Born rule; the full complex form and Gleason's uniqueness are the disclosed forward-note. Phase B may begin: Series 2.11 has landed (INTERFERING).*

---

## 0. Snapshot

- **Phase:** DESIGNED (Phase B complete). `spec/born-derisking.md` + `spec/README.md` + `spec/ws1..ws5-design.md` written and committed as one batch (the Phase B gate) before any `formal/` file. Scaffold `spec/` and `formal/P2S12/` created. Phase C (blind design review, MANDATORY per P3-D1) pending. **Precondition:** Series 2.11 landed (INTERFERING) — met.
- **Verdict:** **PENDING.** Pre-registered outcomes: BORN (a measure whose consistent form is `|amp|²` — quantum probability, scoped rebit), STOCHASTIC-NOT-BORN (a measure, not the squared one — chance without the rule), DETERMINISTIC (no measure — no chance, the deepest NOT-RECOVERED), SHAPE-DRAWN, PARTIAL. No pre-baked expectation; the receipts for non-classicality are strong, for genuine chance weak.
- **Build state:** none yet. Registered at Phase E (namespace `P2S12`, `srcDir ../program-2/series-12/formal`, roots `["P2S12", "P2S12.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S11|P2S12)` — imports 2.11 only, reusing the amplitude/weight; NOT the tier-1 probes).
- **Axiom state / gate state / names grep:** to be verified at Phase E (standard three or fewer; imports `P2S11` only, S8–S0/P1 transitive; forbidden identifiers: weight, measure, probability, born, chance, random, stochastic, self, import, god, choice — docstring prose excepted).
- **Open SERIOUS findings:** none yet (no review has run).

## 1. The carrier — the weight as a probability on the imported amplitude

**S12 stands on the imported object** (`program-2/series-11`, namespace `P2S11`, reaching `P2S8` / … / `P1` transitively; the tier-1 probes 2.9/2.10 are NOT imported). Its working material, reached transitively:

| Carrier piece | Where |
|---|---|
| The signed amplitude `amp` and the weight `|amp|²` (`combinedWeight` / `partsWeight`) | `P2S11` (imported) |
| The destructive interference `ws3_destructive` (the combined weight falls below the parts — forbids a classical additive probability) | `P2S11` (imported) |
| The IMPORTS — the out-of-image differentiator, the one freedom (a permanent open) | `P2S0` / `P1` (transitive) |
| **The reading of the weight as a PROBABILITY** carried by the imports, and the CONSISTENCY test that forces (or refutes) the Born form | **built at S12 WS1–WS4 — the crux, earned from the interference, de-risked on paper first** |

**Design note (from `charter-extension-2.md` §4, 2.12):** the Born rule must be EARNED — the squared form FORCED by consistency with the interference (a classical additive probability CONTRADICTS the combined-weight-below-parts), never defined as `|amp|²` (the no-smuggling gate, sharpest here). Genuine chance requires the imports to carry a measure; DETERMINISTIC (no measure) is a pre-registered honorable outcome. Scope disclosed: the rebit Born rule (real ±1 amplitude); the complex form and Gleason's uniqueness a forward-note.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_outcomes_nontrivial` (distinct outcomes with distinct amplitudes; the imports' measure genuinely at issue) | OPEN | — |
| WS2 | `ws2_weight_nonneg` (`|amp|²` a non-negative weight), `ws2_not_classical` (the interference makes the combined weight fall strictly below the parts — no classical additive probability, resting on `P2S11.ws3_destructive`) | OPEN | — |
| WS3 (anti-costume core) | `ws3_classical_fails` (the classical additive measure — square-then-add — CONTRADICTS the interference), `ws3_born_consistent` (the Born measure — add-then-square — is consistent and non-negative); together the squared form FORCED, not named | OPEN | — |
| WS4 (the knot) | `ws4_born_reachable` (a measure whose consistent form is `|amp|²`, classical refuted), `ws4_deterministic_reachable` (imports carry no non-trivial measure), and if buildable `ws4_stochastic_not_born_reachable` — the fork, no fiat | OPEN | — |
| WS5 | verdict + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`; audits (a) Born earned not named, (b) fork not by fiat, (c) weight non-classical, (d) scope disclosed — rebit not complex/Gleason, (e) names-not-terms) | OPEN | — |

## 3. Audit clauses (protocol §0; UNVERIFIED until Phase F)

- (a) THE BORN RULE IS EARNED, NOT NAMED — no proof term defines the probability as `|amp|²`; the squared form is FORCED by consistency with the interference and the classical form REFUTED. UNVERIFIED. **The clause the series lives or dies on — the sharpest no-smuggling test in the program.**
- (b) THE FORK NOT BY FIAT — BORN / STOCHASTIC-NOT-BORN / DETERMINISTIC all pre-registered and reachable/refutable on genuine grounds, the verdict discriminating. UNVERIFIED.
- (c) THE WEIGHT IS NON-CLASSICAL — the interference (Series 2.11) makes the combined weight fall below the parts, ruling out any classical additive probability. UNVERIFIED.
- (d) THE SCOPE IS DISCLOSED — the amplitude is Series 2.11's real ±1 sign (the rebit Born rule); no theorem claims the full complex amplitude or Gleason's uniqueness (the disclosed forward-note). UNVERIFIED.
- (e) NAMES-NOT-TERMS — no proof term named "weight," "measure," "probability," "Born," "chance," "random," "stochastic," "self," "import," "God," "choice" as content; the grep is the teeth. UNVERIFIED.

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

Empty. Phase C and Phase F findings are recorded here with stable IDs, grades, and closure (Fixed / Relabeled per §0.2a). A Tier-1 landing-review finding is recorded with a `T1-` id. **Note (per program finding P3-D1):** Tier 1 will check phase-completeness on this landing — that a Phase C (blind design review) genuinely ran, `blind-seed-C.md` is present, and its findings are recorded — an undisclosed skip being a reviewability defect in its own right.

## 5. Deviations from the charter

None yet. Any narrowing between charter and build is disclosed here.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, and — probed here, never closed — the classification of the out-of-image imports. Series 2.12 adds none and closes none. If it lands DETERMINISTIC or SHAPE-DRAWN, its question joins the standing catalogue of what the ontology does not yet own.

## 7. Series log

- **2026-07-21 — Series 2.12 Phase B (Design) complete.** Executor wrote the paper gate `spec/born-derisking.md` (the two candidate measures — classical square-then-add `partsWeight`, Born add-then-square `combinedWeight`, both imported from S2.11; the form-agnostic consistency predicate `respectsCancel`; the classical form CONTRADICTS the interference on `attTri` — cancellation holds yet weight `2 ≠ 0`; the Born form is CONSISTENT — vanishes on cancellation — and non-negative; a non-trivial measure survives — `combinedWeight` takes `0`/`4`; no probability defined, no complex number) and the six design files (`README.md`, `ws1..ws5-design.md`) with typed signatures. The one added primitive: `respectsCancel`. Module naming fixed: namespace `P2S12`, imports `P2S11` only. Expected computed verdict BORN (`squared`); DETERMINISTIC and STOCHASTIC-NOT-BORN pre-registered and reachable/discriminated. Committed as one batch before any `formal/` file (the Phase B gate met). Next: Phase C blind design review (MANDATORY, P3-D1).
- **2026-07-21 — Series 2.12 (The Weight) chartered.** Tier 1 authored `series-12/charter.md` / `charter-status.md` / `protocol.md`: the third Phase-3 recovery test, execution tier 3, the second half of the quantum recovery. Knot: do the imports carry a measure — a probability — and is it the Born rule `|amp|²`? Two live questions (genuine chance? Born or not?). Reuses Series 2.11's amplitude/weight and interference; imports `P2S11` only. The Born rule must be EARNED (forced by consistency with the interference, the classical additive measure refuted), never named (the sharpest no-smuggling test). Scope disclosed: the rebit Born rule (real ±1), the complex form and Gleason's uniqueness a forward-note. Pre-registered: BORN, STOCHASTIC-NOT-BORN, DETERMINISTIC (the deepest NOT-RECOVERED — interference without chance), SHAPE-DRAWN. Namespace `P2S12`. Phase B begins now that 2.11 has landed. Handoff to a fresh Tier-2 executor pending — and the executor is on notice (P3-D1) that the chartered A→G phases, including the blind Phase C, are not optional.
