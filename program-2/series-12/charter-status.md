# Program 2 Series 12 (2.12), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: CODED (Phase E complete; Phase C on record, zero SERIOUS; Phase F blind code review pending). `formal/P2S12/ws1..ws5` + aggregator + `AxiomCheck` built. Current verdict: **BORN** (computed at WS5 `ws5_verdict_eq = Outcome.squared`, from the earned flags — never hand-set): the imports carry a non-trivial measure whose only cancellation-consistent form is the squared amplitude, the classical additive form refuted; quantum probability recovered in its rebit form (real `±1`), the complex amplitude and Gleason's / Busch's uniqueness the disclosed forward-note. This is the third Phase-3 recovery test (`charter-extension-2.md`), execution tier 3, THE WEIGHT: do the imports carry a measure — a probability — and is it the Born rule, `|amp|²`? Two live questions: is there genuine CHANCE (do the imports carry a measure, or is the freedom structureless — DETERMINISTIC), and if so is the measure the SQUARED amplitude (BORN) or another (STOCHASTIC-NOT-BORN)? The Born rule must be EARNED (forced by consistency with Series 2.11's interference, the classical additive measure REFUTED), never named. Honestly uncertain which way it lands; DETERMINISTIC (interference without chance) is a real and respectable outcome. Scope: Series 2.11's real ±1 amplitude — the rebit Born rule; the full complex form and Gleason's uniqueness are the disclosed forward-note. Phase B may begin: Series 2.11 has landed (INTERFERING).*

---

## 0. Snapshot

- **Phase:** CODED (Phase E complete). Phases A (charter), B (design, spec batch), C (blind design review, zero SERIOUS, on record), E (code) done. Phase F (blind code review, MANDATORY per P3-D1) pending. **Precondition:** Series 2.11 landed (INTERFERING) — met; Phase C pass on record (P3-D1 Phase-E precondition) — met.
- **Verdict:** **BORN** (`ws5_verdict_eq : verdict true true true true true = Outcome.squared`, computed from the earned flags). Pre-registered alternatives not obtaining: STOCHASTIC-NOT-BORN (discriminated by the verdict function, not witnessed — no non-square measure survives consistency on the rebit ±1 amplitudes), DETERMINISTIC (reachable via a constant/trivial weight, but the imports' actual weight is non-trivial), SHAPE-DRAWN, PARTIAL. The receipts: non-classicality strong (`ws2_not_classical`, from S2.11's interference); genuine chance carried by the non-trivial imported weight (`ws1_measure_nontrivial`, values 0/4); the squared form forced by the form-agnostic consistency test (`ws3_sq_forced`), the classical refuted (`ws3_classical_fails`).
- **Build state:** BUILT. Registered (namespace `P2S12`, `srcDir ../program-2/series-12/formal`, roots `["P2S12", "P2S12.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S11|P2S12)`). `lake build P2S12 P2S12.AxiomCheck` succeeds; `formal/P2S12.lean` (aggregator) + `P2S12/ws1..ws5.lean` + `P2S12/AxiomCheck.lean`.
- **Axiom state:** standard three or fewer — every payoff reduces to `[propext, Classical.choice, Quot.sound]` or a subset (`ws3_classical_fails`, `ws3_sq_earned`, `ws4_deterministic_reachable`, `ws5_audit_scope`: `[propext, Quot.sound]`; `ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_audit_names_not_terms`: no axioms). No non-standard axiom.
- **Gate state:** GREEN — `program-2/series-12` imports resolve only to `P2S11`/`P2S12` (+ Mathlib); `P2S8`/…/`P2S0`/`P1` transitive through S11; the tier-1 probes `P2S9`/`P2S10` NOT imported.
- **Names grep:** CLEAN — no proof term, definition, or constructor is named a forbidden content-word (weight, measure, probability, born, chance, random, stochastic, self, import, god, choice); all 126 grep hits are docstring prose or the Lean `import` keyword. Verified no forbidden word on any code/declaration line.
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

*Lean names are neutral (audit e): the charter's prose names (`ws2_weight_nonneg`, `ws3_born_consistent`, `ws4_born_reachable`, `ws4_stochastic_not_born_reachable`) map to neutral built names (`ws2_sq_nonneg`, `ws3_sq_consistent`, `ws4_squared_reachable`, `unsquared` discriminated in the verdict). The consistency primitive is `respectsCancel` (form-agnostic, mentions no square).*

| WS | Target theorem(s) — built name | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_outcomes_nontrivial` (`loopAmp attTri ≠ loopAmp attStar`), `ws1_measure_nontrivial` (`combinedWeight attTri ≠ combinedWeight attStar`, values 0/4 — the imports' measure genuinely at issue) | BUILT | Built (Phase E), axiom-clean |
| WS2 | `ws2_sq_nonneg` (`0 ≤ combinedWeight att`), `ws2_not_classical` (`combinedWeight attTri < partsWeight attTri`, resting on `P2S11.ws3_destructive`) | BUILT | Built (Phase E), axiom-clean |
| WS3 (anti-costume core) | `ws3_classical_fails` (`¬ respectsCancel partsWeight` — square-then-add CONTRADICTS the cancellation), `ws3_sq_consistent` (`respectsCancel combinedWeight ∧ nonneg` — add-then-square CONSISTENT), `ws3_sq_forced` (consistent ∧ classical fails ∧ they differ), `ws3_sq_earned` (the squared form a function of the built `amp`/`hol`, definitionally) | BUILT | Built (Phase E), axiom-clean |
| WS4 (the knot) | `ws4_squared_reachable` (non-trivial measure ∧ consistent ∧ classical refuted — BORN), `ws4_deterministic_reachable` (a constant weight is trivial — DETERMINISTIC pole); STOCHASTIC-NOT-BORN discriminated by `verdict`, honestly not witnessed | BUILT | Built (Phase E), axiom-clean |
| WS5 | `ws5_verdict_eq` (`= Outcome.squared`), `ws5_verdict_discriminates` (all five outcomes), `ws5_flags_justified`; audits `ws5_audit_earned` (a), `ws5_audit_fork_genuine` (b), `ws5_audit_nonclassical` (c), `ws5_audit_scope` (d), `ws5_audit_names_not_terms` (e) | BUILT | Built (Phase E); verdict computed BORN, audits UNVERIFIED until Phase F |

## 3. Audit clauses (protocol §0; UNVERIFIED until Phase F)

- (a) THE BORN RULE IS EARNED, NOT NAMED — no proof term defines the probability as `|amp|²`; the squared form is FORCED by consistency with the interference and the classical form REFUTED. UNVERIFIED. **The clause the series lives or dies on — the sharpest no-smuggling test in the program.**
- (b) THE FORK NOT BY FIAT — BORN / STOCHASTIC-NOT-BORN / DETERMINISTIC all pre-registered and reachable/refutable on genuine grounds, the verdict discriminating. UNVERIFIED.
- (c) THE WEIGHT IS NON-CLASSICAL — the interference (Series 2.11) makes the combined weight fall below the parts, ruling out any classical additive probability. UNVERIFIED.
- (d) THE SCOPE IS DISCLOSED — the amplitude is Series 2.11's real ±1 sign (the rebit Born rule); no theorem claims the full complex amplitude or Gleason's uniqueness (the disclosed forward-note). UNVERIFIED.
- (e) NAMES-NOT-TERMS — no proof term named "weight," "measure," "probability," "Born," "chance," "random," "stochastic," "self," "import," "God," "choice" as content; the grep is the teeth. UNVERIFIED.

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

**Phase C (blind design review) — RAN 2026-07-21, `spec/blind-seed-C.md` on record, blind reviewer read only the seed. Result: ZERO SERIOUS. Audit (a) — the no-smuggling gate, the clause the series lives or dies on — CLEAN: the reviewer confirmed `respectsCancel` is form-agnostic (its body references only `directAmp`/`loopAmp`/the zero-test, never squaring or `combinedWeight`), so the squared form is genuinely SELECTED by the predicate, not defined-and-relabelled. Audits (b)-(e) PASS. Four COSMETIC findings, all accepted with rationale (no design edit ⇒ no Phase C re-loop needed):**

| ID | Grade | Location | Defect | Disposition |
|----|-------|----------|--------|-------------|
| C1-S1 | COSMETIC | `ws3_sq_forced` | "forced" is a selection between the two candidate measures, not uniqueness among all vanishing forms | ACCEPTED — the scope is already disclosed (audit d claims no uniqueness; the design docs scope it as "the consistent one of the TWO candidates, not the unique one among all `|·|^p`"). The label matches the in-scope claim. |
| C1-S2 | COSMETIC | `ws5_audit_names_not_terms : True` | vacuous marker; `True` does not formalize the names property | ACCEPTED — the sanctioned house placeholder (matches `P2S11.ws5_audit_names_not_terms`); the property is enforced by the protocol §6 grep + the §5 semantic check, not by a proposition. |
| C1-S3 | COSMETIC | `ws3_sq_earned`, `ws5_audit_earned` (2nd/3rd conjuncts) | near-`rfl` transparency lemmas restating the definitions | ACCEPTED — intentional disclosure lemmas (mirror `P2S11.ws3_amp_earned`); they discharge audit (a) by exhibiting the definitional chain to the built `amp`/`hol`, honestly. |
| C1-S4 | COSMETIC | `ws1_measure_nontrivial`, `combinedWeight`, `partsWeight` | names contain interpretive fragments ("measure"/"weight") as composites | ACCEPTED — mechanically clean (no identifier is a bare content-word); `combinedWeight`/`partsWeight` are the imported neutral names. Names-in-prose rule satisfied. |

**Note (per program finding P3-D1):** Phase C (blind design review) genuinely ran, `blind-seed-C.md` is present, and its findings are recorded here — the P3-D1 reviewability requirement is met. Phase F findings will be appended below with `Fn-Sm` ids.

## 5. Deviations from the charter

None yet. Any narrowing between charter and build is disclosed here.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, and — probed here, never closed — the classification of the out-of-image imports. Series 2.12 adds none and closes none. If it lands DETERMINISTIC or SHAPE-DRAWN, its question joins the standing catalogue of what the ontology does not yet own.

## 7. Series log

- **2026-07-21 — Series 2.12 Phase E (Code) complete; verdict computes BORN.** Registered `P2S12` (lakefile lib + `defaultTargets`; gate line `(P2S11|P2S12)`). Built `formal/P2S12/ws1..ws5` + aggregator + `AxiomCheck`, the `P2S12` namespace, importing `P2S11` only. The one added primitive `respectsCancel` (form-agnostic). `lake build P2S12 P2S12.AxiomCheck` succeeds; sorry-free; axiom-clean (standard three or fewer); gate green; names grep clean (prose only). The WS5 verdict COMPUTES `Outcome.squared` from the earned flags (`ws5_verdict_eq`, `rfl`): **BORN** — the imports carry a non-trivial measure (`ws1_measure_nontrivial`, 0/4) whose only cancellation-consistent form is the squared amplitude (`ws3_sq_consistent`), the classical additive form refuted (`ws3_classical_fails`, `¬ respectsCancel partsWeight`) and the squared form forced (`ws3_sq_forced`), earned off the built holonomy (`ws3_sq_earned`), non-classical (`ws2_not_classical`). Quantum probability recovered in its rebit form; the complex amplitude and Gleason/Busch uniqueness the disclosed forward-note. Next: Phase F blind code review (MANDATORY, P3-D1).
- **2026-07-21 — Series 2.12 Phase C (blind design review) complete; zero SERIOUS.** `spec/blind-seed-C.md` generated (signatures + mechanical audit checks only, no motivating prose); blind reviewer read only the seed. Audit (a) CLEAN (the squared form selected by the form-agnostic `respectsCancel`, not defined); (b)-(e) PASS. Four COSMETIC findings recorded in §4, all accepted with rationale; no design edit, so no Phase C re-loop. Phase E precondition (a Phase C pass on record) met.
- **2026-07-21 — Series 2.12 Phase B (Design) complete.** Executor wrote the paper gate `spec/born-derisking.md` (the two candidate measures — classical square-then-add `partsWeight`, Born add-then-square `combinedWeight`, both imported from S2.11; the form-agnostic consistency predicate `respectsCancel`; the classical form CONTRADICTS the interference on `attTri` — cancellation holds yet weight `2 ≠ 0`; the Born form is CONSISTENT — vanishes on cancellation — and non-negative; a non-trivial measure survives — `combinedWeight` takes `0`/`4`; no probability defined, no complex number) and the six design files (`README.md`, `ws1..ws5-design.md`) with typed signatures. The one added primitive: `respectsCancel`. Module naming fixed: namespace `P2S12`, imports `P2S11` only. Expected computed verdict BORN (`squared`); DETERMINISTIC and STOCHASTIC-NOT-BORN pre-registered and reachable/discriminated. Committed as one batch before any `formal/` file (the Phase B gate met). Next: Phase C blind design review (MANDATORY, P3-D1).
- **2026-07-21 — Series 2.12 (The Weight) chartered.** Tier 1 authored `series-12/charter.md` / `charter-status.md` / `protocol.md`: the third Phase-3 recovery test, execution tier 3, the second half of the quantum recovery. Knot: do the imports carry a measure — a probability — and is it the Born rule `|amp|²`? Two live questions (genuine chance? Born or not?). Reuses Series 2.11's amplitude/weight and interference; imports `P2S11` only. The Born rule must be EARNED (forced by consistency with the interference, the classical additive measure refuted), never named (the sharpest no-smuggling test). Scope disclosed: the rebit Born rule (real ±1), the complex form and Gleason's uniqueness a forward-note. Pre-registered: BORN, STOCHASTIC-NOT-BORN, DETERMINISTIC (the deepest NOT-RECOVERED — interference without chance), SHAPE-DRAWN. Namespace `P2S12`. Phase B begins now that 2.11 has landed. Handoff to a fresh Tier-2 executor pending — and the executor is on notice (P3-D1) that the chartered A→G phases, including the blind Phase C, are not optional.
