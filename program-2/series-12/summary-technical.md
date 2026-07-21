# Series 2.12 (The Weight): technical summary

**Verdict: BORN. `ws5_verdict_eq : verdict true true true true true = Outcome.squared`, computed from the earned flags, never hand-set. Build: sorry-free, axiom-clean (standard three or fewer), gate-green, names-grep clean.**

## Imports and reuse

Namespace `P2S12`. Imports `P2S11` only; reaches `P2S8 / P2S7 / ... / P2S0 / P1` transitively; does not import the tier-1 probes `P2S9`/`P2S10`. Gate line: `check program-2/series-12 "^import (P2S11|P2S12)(\.[A-Za-z0-9_]+)*$"`. The series rebuilds no imported machinery. The two candidate measures are the imported neutral objects:

```
combinedWeight att = (directAmp + loopAmp att)^2       -- add-then-square (Born candidate)
partsWeight    att = directAmp^2 + (loopAmp att)^2      -- square-then-add (classical additive candidate)
```

with `directAmp = amp 0 = 1`, `loopAmp att = amp (hol att p0 p1 p2)`, `loopAmp attTri = -1`, `loopAmp attStar = 1`, and the interference `P2S11.ws3_destructive : combinedWeight attTri < partsWeight attTri` (0 < 2).

## The one added primitive

```
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop :=
  ∀ att, directAmp + loopAmp att = 0 → μ att = 0
```

Form-agnostic: the body references only `directAmp`, `loopAmp`, and the zero-test. It mentions no square and not `combinedWeight`. It reads the physical anchor "cancellation is absence" as a predicate any candidate measure either satisfies or fails.

## The workstreams

- **WS1 (ground).** `ws1_outcomes_nontrivial : loopAmp attTri ≠ loopAmp attStar` (distinct outcomes, distinct amplitudes). `ws1_measure_nontrivial : combinedWeight attTri ≠ combinedWeight attStar` (0 vs 4, a non-trivial candidate weight, the ground of genuine chance).
- **WS2.** `ws2_sq_nonneg : 0 ≤ combinedWeight att` (a square is non-negative). `ws2_not_classical : combinedWeight attTri < partsWeight attTri` (`:= P2S11.ws3_destructive`, the strict fall below the parts, ruling out a classical additive probability).
- **WS3 (anti-costume core).** `ws3_classical_fails : ¬ respectsCancel partsWeight` (the square-then-add form fails the consistency predicate, refuted by the non-vacuous witness `attTri`, where `directAmp + loopAmp attTri = 0` holds by `P2S11.ws2_amp_cancels` and `partsWeight attTri = 2 ≠ 0`). `ws3_sq_consistent : respectsCancel combinedWeight ∧ ∀ att, 0 ≤ combinedWeight att` (the add-then-square form respects the cancellation for every `att`, and is non-negative). `ws3_sq_forced` (consistent, classical fails, and the two differ, 0 ≠ 2). `ws3_sq_earned` (the add-then-square form is a function of the built `amp`/`hol`, definitionally, two `rfl`s).
- **WS4 (the knot).** `ws4_squared_reachable` (a non-trivial measure whose consistent form is the square, classical refuted, the BORN pole). `ws4_deterministic_reachable` (a constant weight is a trivial measure, the DETERMINISTIC pole, reachable, not construction-blocked). STOCHASTIC-NOT-BORN is discriminated by the verdict function but not witnessed on the rebit amplitudes.
- **WS5 (verdict and audit).** `Outcome` with constructors `squared`/`unsquared`/`deterministic`/`shapeDrawn`/`partial'`. `verdict` is a total function of five Bool flags; `ws5_verdict_eq` computes `squared` on all-true (`rfl`); `ws5_verdict_discriminates` reaches all five constructors (`decide`); `ws5_flags_justified` supplies each flag from a WS1-WS4 headline. Audit clauses `ws5_audit_earned` (a), `ws5_audit_fork_genuine` (b), `ws5_audit_nonclassical` (c), `ws5_audit_scope` (d, `∀ n, amp n = 1 ∨ amp n = -1`), `ws5_audit_names_not_terms` (e, the accepted house placeholder).

## The no-smuggling gate (audit a), the clause the series lives or dies on

No object writes `probability := combinedWeight`. The squared form is selected by the form-agnostic `respectsCancel`: `combinedWeight` is proved to satisfy it, `partsWeight` proved to fail it via a non-vacuous witness. The blind Phase F reviewer pressed hardest here and confirmed the selection is a real mathematical distinction (`(sum)^2` vanishes when the sum vanishes while the sum of squares does not), not a baked-in square. The scope is honest: this forces the square among the two candidate measures, not the unique measure among all powers.

## Reviews

Both blind phases ran and are on record (P3-D1 satisfied). Phase C (design, `blind-seed-C.md`): zero SERIOUS, four COSMETIC, audit (a) clean. Phase F (code, `blind-seed-F.md`): zero SERIOUS, zero REAL, two COSMETIC, all 21 signatures proved verbatim, audit (a)-(e) and the axiom pass all PASS.

## Mechanical checks (protocol §6)

```
lake build P2S12 P2S12.AxiomCheck   # succeeds
grep -rn "sorry" formal             # none
P2S12.AxiomCheck                    # every payoff: subset of {propext, Classical.choice, Quot.sound}; three depend on none
scripts/gate.sh                     # OK program-2/series-12 (imports resolve to P2S11/P2S12 + Mathlib)
names grep                          # all hits docstring prose / the import keyword; no forbidden word on a code line
```

## Result

BORN, the rebit Born rule. The imports carry a non-trivial, non-negative, non-classical measure whose only cancellation-consistent form is the squared amplitude, the classical additive form refuted by the interference and the squared form forced by the consistency test, never named. The complex amplitude and Gleason's / Busch's uniqueness are the disclosed forward-note. Program 1's four permanent opens stand; the classification of the out-of-image imports, the deepest of them, is probed here and left open.
