# Blind seed — Phase F (code review). Series 2.12.

You are reviewing built Lean 4 (Mathlib) CODE for whether it PROVES the claimed signatures. You are BLIND: you see the code and the claims below and NOTHING of their motivation. Judge only the code against the contracts here.

## Files you MAY read

- This file (`spec/blind-seed-F.md`).
- The Lean sources ONLY:
  - `program-2/series-12/formal/P2S12/ws1.lean`
  - `program-2/series-12/formal/P2S12/ws2.lean`
  - `program-2/series-12/formal/P2S12/ws3.lean`
  - `program-2/series-12/formal/P2S12/ws4.lean`
  - `program-2/series-12/formal/P2S12/ws5.lean`
  - `program-2/series-12/formal/P2S12.lean`, `program-2/series-12/formal/P2S12/AxiomCheck.lean`
- You MAY also read the imported prior module `program-2/series-11/formal/P2S11/*.lean` and `program-2/series-8/formal/P2S8/*.lean` to confirm the imported facts the code relies on are real (their statements only).

You must NOT read: `charter.md`, `charter-status.md`, `protocol.md`, any `charter-extension` file, any `summary*` file, `born-derisking.md`, `spec/README.md`, or any `ws*-design.md`. If you read a forbidden file, stop and report it (the review is discarded and re-run).

## The imported facts (from `P2S11`/`P2S8`, treat as true; confirm the statements exist)

```lean
amp n = if n % 2 = 0 then 1 else -1 ;  directAmp = amp 0 ;  loopAmp att = amp (hol att p0 p1 p2)
combinedWeight att = (directAmp + loopAmp att)^2 ;  partsWeight att = directAmp^2 + (loopAmp att)^2
directAmp_eq : directAmp = 1 ;  loopAmp_attTri : loopAmp attTri = -1 ;  loopAmp_attStar : loopAmp attStar = 1
amp_values : ∀ n, amp n = 1 ∨ amp n = -1 ;  ws2_amp_cancels : directAmp + loopAmp attTri = 0
ws3_destructive : combinedWeight attTri < partsWeight attTri
```

## The claimed signatures (the code must PROVE exactly these, sorry-free)

```lean
namespace P2S12 -- open P2S8 P2S11
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop := ∀ att, directAmp + loopAmp att = 0 → μ att = 0
theorem ws1_outcomes_nontrivial : loopAmp attTri ≠ loopAmp attStar
theorem ws1_measure_nontrivial  : combinedWeight attTri ≠ combinedWeight attStar
theorem ws2_sq_nonneg (att : S → Finset S) : 0 ≤ combinedWeight att
theorem ws2_not_classical : combinedWeight attTri < partsWeight attTri
theorem ws3_classical_fails : ¬ respectsCancel partsWeight
theorem ws3_sq_consistent   : respectsCancel combinedWeight ∧ ∀ att, 0 ≤ combinedWeight att
theorem ws3_sq_forced : respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight ∧ combinedWeight attTri ≠ partsWeight attTri
theorem ws3_sq_earned : (∀ att, combinedWeight att = (directAmp + loopAmp att)^2) ∧ (∀ att, loopAmp att = amp (hol att p0 p1 p2))
theorem ws4_squared_reachable : combinedWeight attTri ≠ combinedWeight attStar ∧ respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight
theorem ws4_deterministic_reachable : ∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att'
inductive Outcome | squared | unsquared | deterministic | shapeDrawn | partial'
def verdict (nontrivial nonneg nonclassical sqConsistent classicalFails : Bool) : Outcome
theorem ws5_verdict_eq : verdict true true true true true = Outcome.squared
theorem ws5_verdict_discriminates : (five rows, all five constructors reached)
theorem ws5_flags_justified : (nontrivial ∧ nonneg ∧ nonclassical ∧ sqConsistent ∧ classicalFails, each a proved fact)
theorem ws5_audit_earned : (respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight) ∧ (combinedWeight = square) ∧ (loopAmp = amp∘hol)
theorem ws5_audit_fork_genuine : (nontrivial ∧ constant-is-constant ∧ combinedWeight attTri ≠ partsWeight attTri)
theorem ws5_audit_nonclassical : combinedWeight attTri < partsWeight attTri
theorem ws5_audit_scope : ∀ n : ℤ, amp n = 1 ∨ amp n = -1
theorem ws5_audit_names_not_terms : True
```

## Your task

1. **Proves-the-claim.** For each theorem, confirm the code proves EXACTLY the stated signature (no weaker restatement, no added hypothesis silently discharged, no `sorry`, no `admit`, no `native_decide` masking a false claim). Confirm `verdict` is a total function and `ws5_verdict_discriminates` genuinely reaches all five constructors (trace the `if`-chain by hand). Confirm the imported facts the proofs cite are the real statements in `P2S11`/`P2S8`.
2. **Audit (a) — forced, not defined (PRESS HARDEST).** Confirm `respectsCancel`'s body is `∀ att, directAmp + loopAmp att = 0 → μ att = 0` and mentions NO squaring and NOT `combinedWeight`. Confirm `combinedWeight` is shown to satisfy it and `partsWeight` shown to FAIL it (via a real witness `attTri` where the hypothesis `directAmp + loopAmp attTri = 0` genuinely holds and `partsWeight attTri ≠ 0`). If the square were baked into `respectsCancel`, or `ws3_classical_fails`'s witness were vacuous (hypothesis never satisfiable), grade SERIOUS.
3. **Audit (b) — genuine measure vs asserted chance.** Confirm `ws1_measure_nontrivial` is a real inequality (`combinedWeight attTri` and `combinedWeight attStar` genuinely differ, 0 vs 4) and `ws4_deterministic_reachable` genuinely holds (a constant function is constant). No chance claimed where the weight is constant.
4. **Audit (c) — non-classical.** Confirm `ws2_not_classical` is a STRICT `<` inherited from `ws3_destructive`.
5. **Audit (d) — scope.** Confirm NO theorem claims `amp` is complex, or the squared form unique among all `|·|^p`, or Gleason/Busch uniqueness. `ws5_audit_scope` claims only `amp n = 1 ∨ amp n = -1`.
6. **Names grep (audit e).** Run: `grep -rniE "\b(weight|measure|probability|born|chance|random|stochastic|self|import|god|choice)\b" program-2/series-12/formal`. Confirm every hit is docstring/comment prose or the Lean `import` keyword — NO proof term, def, or constructor is NAMED a bare content-word. (Composites like `combinedWeight`, `ws1_measure_nontrivial` are acceptable; judge whether any identifier IS the interpretive content-word.)
7. **Strip test.** For each headline, delete "probability, weight, measure, Born, classical, consistent, chance, deterministic, stochastic" and confirm it still reads as a bare arithmetic/consistency fact.
8. **Axioms.** Confirm `AxiomCheck.lean` reports only `propext`, `Classical.choice`, `Quot.sound` (or a subset) for every payoff — no other axiom, no `sorryAx`.

## Grading rubric

- **SERIOUS:** the code does not prove the claimed signature; a `sorry`/`admit`/`sorryAx`/non-standard axiom; the squared form DEFINED not forced (audit a); `ws3_classical_fails`'s refutation vacuous; chance asserted where the weight is constant (audit b); a scope overclaim (audit d); a proof term NAMED a content-word (audit e); `verdict` not reaching a claimed constructor; an undisclosed narrowing between the claimed signature and the proved one.
- **REAL:** a genuine gap correctly labelled once fixed (an over-strong docstring, a near-`rfl` lemma dressed as content, a hypothesis assumed-and-returned).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

Grade each finding SERIOUS / REAL / COSMETIC with a stable ID (`F1-S1`, …), the exact location (file:theorem), and the precise defect. Press HARDEST on audit (a). If nothing is SERIOUS, state so explicitly. Return a structured list of findings.
