# Series 2.12 design index (`spec/README.md`) — THE WEIGHT

**The design layer for the second half of the quantum recovery. Read `born-derisking.md` first (the paper gate: the two candidate measures — the classical additive square-then-add and the Born add-then-square — read off Series 2.11's built weight; the classical form CONTRADICTS the interference, the Born form is CONSISTENT and non-negative, a non-trivial measure survives, no complex number, no probability defined — all survived, expected verdict BORN). This README fixes the imported object, the one added primitive, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All files (`born-derisking.md`, `README.md`, `ws1..ws5-design.md`) are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported object (quantified, never named as content)

Series 2.12 imports `P2S11` only; `P2S8 / P2S7 / … / P2S0 / P1` are reached transitively. It does NOT import the tier-1 probes `P2S9`/`P2S10` (their content is not reused). Working material, all built and axiom-checked in Series 2.11 (and, through it, Series 2.8):

- **The sign** `P2S11.amp n := if n % 2 = 0 then 1 else -1 : ℤ` (`±1`-valued; `amp_values`, `amp_sq`), a function of the built holonomy alone.
- **The two path amplitudes** `P2S11.directAmp := amp 0` (`= +1`, `directAmp_eq`) and `P2S11.loopAmp att := amp (hol att p0 p1 p2)` (`loopAmp attTri = -1`, `loopAmp attStar = +1`, `ws1_amp_signed`).
- **The two candidate combined weights** `P2S11.combinedWeight att := (directAmp + loopAmp att)^2` (ADD-then-SQUARE) and `P2S11.partsWeight att := directAmp^2 + (loopAmp att)^2` (SQUARE-then-ADD). These ARE the two candidate measures — Series 2.12 adds no arithmetic, only the reading and the consistency test.
- **The interference** `P2S11.ws3_destructive : combinedWeight attTri < partsWeight attTri` and `P2S11.ws2_amp_cancels : directAmp + loopAmp attTri = 0`, on the carriers `P2S8.attTri` (frustrated, `hol = 3`) / `P2S8.attStar` (gluable, `hol = 0`).
- **The imports** — the out-of-image differentiator, the program's one genuine freedom (`P2S0` / `P1`, a permanent open, transitive) — read as the free selection among the outcomes, the candidate carrier of a measure.

## 2. The one added primitive (built FRESH at S12; `formal/P2S12/ws1..ws5`)

Series 2.12 adds exactly one thing — the reading of the weight as a PROBABILITY carried by the imports, together with the FORM-AGNOSTIC consistency test that forces (or refutes) the Born form:

```lean
-- A candidate measure RESPECTS the cancellation if it vanishes wherever the amplitudes cancel.
-- Mentions no square: the bare demand that a probability vanish on the interference ("cancellation is
-- absence"). The Born (add-then-square) form is PROVED to satisfy it; the classical (square-then-add)
-- form is PROVED to fail it. The squared form is the RESIDUE of the test, never a definition.
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop :=
  ∀ att, directAmp + loopAmp att = 0 → μ att = 0
```

Everything downstream is a ℤ-arithmetic fact on a finite carrier: `decide` / `omega` / `norm_num` / `sq_nonneg`-checkable. The two candidate measures are the imported `combinedWeight` (add-then-square) and `partsWeight` (square-then-add); no probability is defined as `|amp|²`.

## 3. The discipline (the no-smuggling gate, PROMOTED first-class, sharpest in the program)

- **The Born rule is EARNED, not named (audit a, the phase sin here, sharpest).** No object writes `probability := combinedWeight`. `respectsCancel` is form-agnostic (it demands "vanish on cancellation," not "equal a square"); the add-then-square form is PROVED consistent (`ws3_sq_consistent`) while the square-then-add form is PROVED to FAIL (`ws3_classical_fails`), so the squared form is FORCED (`ws3_sq_forced`). `ws3_sq_earned` ties the add-then-square form to the built `amp`/`hol`/`incr` definitionally — no complex number, no bolted-on probability.
- **Genuine chance requires a measure (audit b).** Chance is claimed ONLY because the imported weight `combinedWeight` is NON-TRIVIAL (`ws1_measure_nontrivial`: values `0`/`4`). Were the only surviving measure constant (`partsWeight ≡ 2`), the honest verdict would be DETERMINISTIC — interference without chance — reported in full. The DETERMINISTIC pole is genuinely reachable (`ws4_deterministic_reachable`: a constant weight is trivial), not excluded by fiat.
- **The weight is NON-CLASSICAL (audit c).** `combinedWeight attTri = 0 < 2 = partsWeight attTri` (imported `ws3_destructive`): the combined weight falls STRICTLY below the parts, impossible for any classical additive probability (classically weights add, `combined ≥ parts`).
- **The scope is disclosed (audit d).** `amp` is a REAL `±1` (`amp_values`, `ws5_audit_scope`); this series earns at most the REBIT Born rule (the square is the consistent one of the TWO candidate measures, not the unique one among all `|·|^p`). No theorem claims the full complex amplitude or Gleason's / Busch's uniqueness — the disclosed forward-note.
- **BORN, STOCHASTIC-NOT-BORN, DETERMINISTIC honorable.** DETERMINISTIC (no non-trivial measure) is the deepest NOT-RECOVERED and a specification (add a source of weighted freedom); STOCHASTIC-NOT-BORN (a non-square measure) is chance of the wrong shape. Neither materialises here (§ de-risking: the measure is non-trivial and its consistent form is the square), but both are pre-registered and reachable/discriminated in the verdict function.

## 4. Cross-workstream triage

| WS | Object | Headline(s) | Costume foreclosed |
|----|--------|-------------|--------------------|
| WS1 (ground) | `loopAmp`, `combinedWeight` | `ws1_outcomes_nontrivial`, `ws1_measure_nontrivial` | distinct outcomes, a non-trivial measure to weigh; DETERMINISTIC obstruction pre-registered |
| WS2 | `combinedWeight`, `partsWeight` | `ws2_sq_nonneg`, `ws2_not_classical` | a non-negative weight that undercuts its parts — not a classical additive probability |
| WS3 (anti-costume core) | `respectsCancel`, `combinedWeight`, `partsWeight` | `ws3_classical_fails`, `ws3_sq_consistent`, `ws3_sq_forced`, `ws3_sq_earned` | the square FORCED by a form-agnostic test, the classical REFUTED; earned off `hol`, no complex number, no probability defined |
| WS4 (the knot) | `combinedWeight`/`partsWeight`, constant weight | `ws4_squared_reachable`, `ws4_deterministic_reachable` | BORN and DETERMINISTIC both genuine, no fiat; STOCHASTIC-NOT-BORN discriminated, honestly not witnessed |
| WS5 | `verdict` | `ws5_verdict_eq (= squared)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)-(e) | computed, not hand-set |

## 5. The outcomes (WS5)

`squared` (the imports carry a non-trivial measure whose consistent form is the squared amplitude, the classical refuted → BORN, quantum probability recovered, rebit-scoped, the expected close), `unsquared` (a non-trivial measure but not the squared/consistent form → STOCHASTIC-NOT-BORN, chance of the wrong shape, a specification — discriminated, not witnessed here), `deterministic` (no non-trivial measure → DETERMINISTIC, no chance, the deepest NOT-RECOVERED, a specification: add weighted freedom), `shapeDrawn` (the fork drawn, neither pole forced), `partial'` (degenerate; `partial` is a Lean keyword — not even a non-negative weight, or a rigged fork).

## 6. Names-in-prose rule (audit e)

The concept-words — weight, measure, probability, Born, chance, random, stochastic, self, import, God, choice — appear only in docstring prose. Every proof term, definition, and discharged obligation carries a NEUTRAL name (`respectsCancel`, `combinedWeight`/`partsWeight` imported, `verdict`, `Outcome`, `squared`/`unsquared`/`deterministic`/`shapeDrawn`/`partial'`, `ws*`). `sq` is the sanctioned neutral stem for the squared form (`ws2_sq_nonneg`, `ws3_sq_consistent`, `ws3_sq_forced`, `ws3_sq_earned`, `ws4_squared_reachable`); no headline embeds a forbidden content-word as a whole word. The §6 grep runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt (they are not proof-term names). Note the grep treats `_` and camelCase as word-internal, so the semantic check (protocol §5) is the real teeth: NO proof term is NAMED for the interpretive content, checked by the blind reviewer.
