# Blind seed — Phase C (design review). Series 2.12.

You are reviewing a set of Lean 4 (Mathlib) DESIGN signatures for coherence and non-vacuity. You are BLIND: you see the mathematical objects and claims below and NOTHING of their motivation. Judge only what is written here. Do not speculate about interpretation.

---

## 1. The imported objects (already built and axiom-checked in a prior module `P2S11`, reached by `import P2S11`; `P2S8 / … / P1` transitive). Treat these as given/true.

```lean
-- carrier: S := Fin 3, with distinguished p0 p1 p2 : S; att : S → Finset S ranges over configurations.
-- (from P2S8, transitive)
incr : (S → Finset S) → S → S → ℤ            -- incr att x y = (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)
hol  : (S → Finset S) → S → S → S → ℤ         -- hol att x y z = incr att x y + incr att y z + incr att z x
attTri  : S → Finset S                        -- hol attTri  p0 p1 p2 = 3
attStar : S → Finset S                        -- hol attStar p0 p1 p2 = 0

-- (from P2S11)
amp : ℤ → ℤ                                   -- amp n = if n % 2 = 0 then 1 else -1
directAmp : ℤ := amp 0                         -- = 1
loopAmp   : (S → Finset S) → ℤ := fun att => amp (hol att p0 p1 p2)   -- loopAmp attTri = -1, loopAmp attStar = 1
combinedWeight : (S → Finset S) → ℤ := fun att => (directAmp + loopAmp att) ^ 2   -- "add then square"
partsWeight    : (S → Finset S) → ℤ := fun att => directAmp ^ 2 + (loopAmp att) ^ 2 -- "square then add"
-- given facts: amp_values : ∀ n, amp n = 1 ∨ amp n = -1 ;  amp_sq : ∀ n, amp n ^ 2 = 1
-- ws2_amp_cancels : directAmp + loopAmp attTri = 0 ;  ws3_destructive : combinedWeight attTri < partsWeight attTri
```

## 2. The one new definition under review

```lean
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop :=
  ∀ att, directAmp + loopAmp att = 0 → μ att = 0
```

## 3. The theorem signatures under review (namespace `P2S12`, `open P2S8 P2S11`)

```lean
-- WS1
theorem ws1_outcomes_nontrivial : loopAmp attTri ≠ loopAmp attStar
theorem ws1_measure_nontrivial  : combinedWeight attTri ≠ combinedWeight attStar

-- WS2
theorem ws2_sq_nonneg (att : S → Finset S) : 0 ≤ combinedWeight att
theorem ws2_not_classical : combinedWeight attTri < partsWeight attTri

-- WS3
theorem ws3_classical_fails : ¬ respectsCancel partsWeight
theorem ws3_sq_consistent   : respectsCancel combinedWeight ∧ ∀ att, 0 ≤ combinedWeight att
theorem ws3_sq_forced :
    respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight ∧ combinedWeight attTri ≠ partsWeight attTri
theorem ws3_sq_earned :
    (∀ att, combinedWeight att = (directAmp + loopAmp att) ^ 2)
  ∧ (∀ att, loopAmp att = amp (hol att p0 p1 p2))

-- WS4
theorem ws4_squared_reachable :
    combinedWeight attTri ≠ combinedWeight attStar
  ∧ respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight
theorem ws4_deterministic_reachable :
    ∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att'

-- WS5
inductive Outcome | squared | unsquared | deterministic | shapeDrawn | partial'  deriving DecidableEq
def verdict (nontrivial nonneg nonclassical sqConsistent classicalFails : Bool) : Outcome :=
  if !nonneg then Outcome.partial'
  else if !nontrivial then Outcome.deterministic
  else if sqConsistent && classicalFails && nonclassical then Outcome.squared
  else if classicalFails && !sqConsistent then Outcome.unsquared
  else Outcome.shapeDrawn
theorem ws5_verdict_eq : verdict true true true true true = Outcome.squared
theorem ws5_verdict_discriminates :
    verdict true true true true true   = Outcome.squared
  ∧ verdict true true true true false  = Outcome.shapeDrawn
  ∧ verdict true true false false true = Outcome.unsquared
  ∧ verdict false true true true true  = Outcome.deterministic
  ∧ verdict true false true true true  = Outcome.partial'
theorem ws5_flags_justified :
    (combinedWeight attTri ≠ combinedWeight attStar)
  ∧ (∀ att, 0 ≤ combinedWeight att)
  ∧ (combinedWeight attTri < partsWeight attTri)
  ∧ (respectsCancel combinedWeight)
  ∧ (¬ respectsCancel partsWeight)
theorem ws5_audit_earned :
    (respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight)
  ∧ (∀ att, combinedWeight att = (directAmp + loopAmp att) ^ 2)
  ∧ (∀ att, loopAmp att = amp (hol att p0 p1 p2))
theorem ws5_audit_fork_genuine :
    (combinedWeight attTri ≠ combinedWeight attStar)
  ∧ (∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att')
  ∧ (combinedWeight attTri ≠ partsWeight attTri)
theorem ws5_audit_nonclassical : combinedWeight attTri < partsWeight attTri
theorem ws5_audit_scope : ∀ n : ℤ, amp n = 1 ∨ amp n = -1
theorem ws5_audit_names_not_terms : True
```

## 4. Success criteria (restated mechanically; judge the DESIGN against these)

1. There exist genuinely distinct outcomes with distinct amplitudes, and the candidate weight is genuinely at issue (not constant by construction). [WS1]
2. `combinedWeight` is `≥ 0` everywhere, and `combinedWeight attTri < partsWeight attTri` (a combined quantity strictly below the sum of its parts). [WS2]
3. `partsWeight` fails `respectsCancel` and `combinedWeight` satisfies it, and they differ on `attTri`. [WS3]
4. The three poles (`squared`, `deterministic`, and the discriminated `unsquared`) are distinguishable, and `partsWeight` genuinely fails (an explicit witness), not merely omitted. [WS4]
5. `verdict` is a total function of the five flags computing `squared` on all-true and reaching all five constructors; each flag equals a proved headline. [WS5]

## 5. The audit checks (a)-(e), as MECHANICAL instructions

- **(a) Forced, not defined.** Confirm NO definition sets a probability/weight equal to `(… )^2` by fiat and then re-derives it. Confirm `respectsCancel` is FORM-AGNOSTIC: its body `∀ att, directAmp + loopAmp att = 0 → μ att = 0` must NOT mention squaring or `combinedWeight`. Confirm the squared form is SELECTED by the predicate (`combinedWeight` satisfies it, `partsWeight` does not), not built into it. If `respectsCancel` were tailored to `combinedWeight` (e.g. its body referenced the square), grade SERIOUS. Judge: is `ws3_sq_forced` a genuine selection or a relabelled definition?
- **(b) A genuine non-trivial measure vs asserted structure.** Confirm the non-triviality claim `combinedWeight attTri ≠ combinedWeight attStar` is a real inequality (`0 ≠ 4`), and that the `deterministic` pole is genuinely reachable (a constant function is constant) rather than excluded. If genuine chance were claimed where the weight is constant, grade SERIOUS.
- **(c) Strict inequality, not a relabelled sum.** Confirm `ws2_not_classical` is a STRICT `<` (not `≤` with equality achievable), resting on `combinedWeight attTri = 0 < 2 = partsWeight attTri`.
- **(d) Scope.** Confirm NO signature claims `amp` is complex, or uniqueness of the squared form among all powers `|·|^p`, or a Gleason/Busch-style uniqueness. `ws5_audit_scope` must claim only `amp n = 1 ∨ amp n = -1`. If any signature overclaims uniqueness or a complex form, grade SERIOUS.
- **(e) Names.** Grep the signatures: no theorem/def/constructor identifier may BE a forbidden content-word as its name — the forbidden set: weight, measure, probability, born, chance, random, stochastic, self, import, god, choice. (Underscored/camelCase composites that merely CONTAIN a fragment are acceptable to the mechanical grep; judge whether any identifier is NAMED for the interpretive content, e.g. a theorem literally named `born…` or a constructor `probability`.)

## 6. Strip test

For each headline, delete the words "probability, weight, measure, Born, classical, consistent, chance, deterministic, stochastic" and confirm the statement still reads as a bare arithmetic/consistency fact (a non-negativity, an inequality, a vanishing-on-zero, a function-equality). If a headline becomes vacuous or circular once stripped, grade it.

## 7. Grading rubric

- **SERIOUS:** the design cannot support its claim; the squared form is DEFINED not forced (audit a); chance asserted where the weight is constant (audit b); a scope overclaim (audit d, complex/uniqueness); a name is a term (audit e); a pole is hard-wired; or a signature is vacuous/circular.
- **REAL:** a genuine gap correctly labelled once fixed (an over-strong name, an assumed-and-returned hypothesis, a consistency check that is really a definition, a docstring overclaim).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

## 8. Your task

For EACH signature: (1) is the design COHERENT and NON-VACUOUS — could it be proved as stated on the given imported facts, and does it say something with content? (2) Run the audit checks (a)-(e) and the strip test. (3) Grade each finding SERIOUS / REAL / COSMETIC with a stable ID (`C1-S1`, `C1-S2`, …), the exact location (theorem/def name), and the precise defect. Press HARDEST on (a): is the squared form forced by a form-agnostic consistency test, or defined and relabelled? Return a structured list of findings. If you find nothing SERIOUS, say so explicitly.
