# WS4 design — the fork (BORN vs STOCHASTIC-NOT-BORN vs DETERMINISTIC) (2.12)

**The knot. Prove the fork, each pole pre-registered, none by fiat. BORN: the imports carry a genuine (non-trivial) measure AND the consistent measure is the squared amplitude (the classical alternative refuted, WS3) — the Born rule, scoped to the real ±1 amplitude. DETERMINISTIC: a configuration where the imports carry NO non-trivial measure (a structureless freedom, a constant weight) — no chance. STOCHASTIC-NOT-BORN (discriminated, not witnessed): a measure that is not the squared one — chance without the quantum rule; on the rebit ±1 amplitudes no non-square measure survives consistency, so it is a verdict the function can return but not a claimed carrier. Which obtains is computed, not chosen. The costume watch: BORN rests on the squared form being FORCED by consistency (WS3), not on defining it; the classical measure must genuinely FAIL, not be excluded by fiat.**

## Imported objects (from `P2S11`)

- `P2S11.combinedWeight`, `P2S11.partsWeight` — the two candidate measures.
- `P2S11.combinedWeight attTri = 0`, `combinedWeight attStar = 4` (non-trivial); `P2S11.ws4_additive_reachable` (the star's constructive pole).

## WS3 objects reused

- `respectsCancel`, `ws3_sq_consistent`, `ws3_classical_fails` (from `ws3`).
- `ws1_measure_nontrivial : combinedWeight attTri ≠ combinedWeight attStar` (from `ws1`).

## Signatures

```lean
namespace P2S12
open P2S8 P2S11

-- BORN-REACHABLE. The imports carry a NON-TRIVIAL measure (combinedWeight: 0 on attTri, 4 on attStar)
-- whose CONSISTENT form is the squared amplitude (respectsCancel combinedWeight) while the classical
-- additive form is REFUTED (¬ respectsCancel partsWeight). Quantum probability, rebit-scoped, no fiat.
theorem ws4_squared_reachable :
    combinedWeight attTri ≠ combinedWeight attStar
  ∧ respectsCancel combinedWeight
  ∧ ¬ respectsCancel partsWeight

-- DETERMINISTIC-REACHABLE. A structureless freedom — a CONSTANT weight — carries no non-trivial
-- measure: it assigns the same value to every configuration, so there is nothing to weigh, no chance.
-- A genuine, distinct pole (the deepest NOT-RECOVERED), not construction-blocked.
theorem ws4_deterministic_reachable :
    ∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att'

-- STOCHASTIC-NOT-BORN is discriminated by the verdict function (WS5) but NOT witnessed on these
-- carriers: the only consistent measure of the two candidates is the squared one (WS3). Recorded in
-- WS5's discrimination theorem, not as a reachable-carrier claim here (the honest scope).
```

## Proofs (by hand, checked)

- `ws4_squared_reachable`: `⟨ws1_measure_nontrivial, ws3_sq_consistent.1, ws3_classical_fails⟩`.
- `ws4_deterministic_reachable`: `intro c att att'; rfl` (a constant function is constant — the trivial measure witnessing the DETERMINISTIC pole is genuinely available).

## Outcome classes / costume watch

- **BORN vs DETERMINISTIC genuinely distinct:** BORN needs a NON-TRIVIAL measure (`ws1_measure_nontrivial`); DETERMINISTIC is the trivial (constant) measure. Both exist; which the imports carry is the computed question. This world's imported weight `combinedWeight` is non-trivial → BORN, not DETERMINISTIC.
- **The fork not by fiat (audit b/d):** BORN is not built into the objects — a constant weight gives DETERMINISTIC, and the classical additive `partsWeight` is a genuine, distinct measure that genuinely FAILS consistency (`ws3_classical_fails`), not one excluded by omission. DETERMINISTIC is not built in — the actual imported weight is non-trivial.
- **STOCHASTIC-NOT-BORN honestly scoped:** pre-registered and discriminated by the verdict function, but NOT claimed reachable here (no non-square measure survives consistency on the rebit ±1 amplitudes). The general non-square measure is the disclosed forward-note.

## Strip test

Delete "Born," "measure," "chance," "deterministic," "stochastic": the bare facts are `combinedWeight attTri ≠ combinedWeight attStar` (`0 ≠ 4`), `respectsCancel combinedWeight`, `¬ respectsCancel partsWeight`, and "a constant function is constant" — inequalities, the two consistency facts (WS3), and `rfl`. Survives.
