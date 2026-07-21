# WS5 design — the verdict and the audit folded in (2.12)

**The verdict is COMPUTED, never hand-set: BORN (WS1 non-trivial outcomes and a non-trivial measure, WS2 a non-negative non-classical weight, WS3 the squared form forced and the classical form refuted, WS4 a genuine measure whose consistent form is `|amp|²` — quantum probability recovered, scoped rebit); STOCHASTIC-NOT-BORN (a measure, not the squared form); DETERMINISTIC (no measure — no chance); SHAPE-DRAWN (the fork drawn, neither forced); PARTIAL (degenerate). The five audit clauses (a)-(e) bundle the payoffs.**

## Imported / prior objects

- WS1: `ws1_outcomes_nontrivial`, `ws1_measure_nontrivial`. WS2: `ws2_sq_nonneg`, `ws2_not_classical`. WS3: `ws3_classical_fails`, `ws3_sq_consistent`, `ws3_sq_forced`, `ws3_sq_earned`. WS4: `ws4_squared_reachable`, `ws4_deterministic_reachable`.
- `P2S11.amp_values : ∀ n, amp n = 1 ∨ amp n = -1` (the real ±1 scope).

## The outcome type and verdict function (universe-free, neutral names)

```lean
namespace P2S12
open P2S8 P2S11

-- The outcome type. `squared` the imports carry a non-trivial measure whose consistent form is the
-- squared amplitude (the classical refuted) — quantum probability, rebit; `unsquared` a non-trivial
-- measure but not the squared/consistent form — chance of the wrong shape; `deterministic` no
-- non-trivial measure — no chance, the deepest NOT-RECOVERED; `shapeDrawn` the fork drawn, neither
-- pole forced; `partial'` degenerate (`partial` is a Lean keyword). No identifier embeds a forbidden
-- content-word.
inductive Outcome
  | squared
  | unsquared
  | deterministic
  | shapeDrawn
  | partial'
  deriving DecidableEq

-- The verdict FUNCTION of five earned flags:
--   nontrivial     — the imports carry a non-trivial measure (WS1/WS4)
--   nonneg         — the candidate measure is non-negative (WS2)
--   nonclassical   — the combined weight falls below the parts (WS2)
--   sqConsistent   — the add-then-square form respects the cancellation (WS3)
--   classicalFails — the square-then-add form does not (WS3)
def verdict (nontrivial nonneg nonclassical sqConsistent classicalFails : Bool) : Outcome :=
  if !nonneg then Outcome.partial'
  else if !nontrivial then Outcome.deterministic
  else if sqConsistent && classicalFails && nonclassical then Outcome.squared
  else if classicalFails && !sqConsistent then Outcome.unsquared
  else Outcome.shapeDrawn
```

## Signatures

```lean
-- THE COMPUTED VERDICT. On the earned flags (a non-trivial measure, non-negative, non-classical, the
-- squared form consistent, the classical form failing), `squared` — BORN, by computation.
theorem ws5_verdict_eq : verdict true true true true true = Outcome.squared

-- Falsifiability: the verdict DISCRIMINATES, reaching all five outcomes.
theorem ws5_verdict_discriminates :
    verdict true true true true true   = Outcome.squared
  ∧ verdict true true true true false  = Outcome.shapeDrawn      -- classical not refuted: cannot earn
  ∧ verdict true true false false true = Outcome.unsquared       -- a measure, not the squared form
  ∧ verdict false true true true true  = Outcome.deterministic   -- no non-trivial measure: no chance
  ∧ verdict true false true true true  = Outcome.partial'        -- not even a non-negative weight

-- THE FLAGS ARE JUSTIFIED: the five deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set.
theorem ws5_flags_justified :
    (combinedWeight attTri ≠ combinedWeight attStar)                    -- nontrivial (WS1)
  ∧ (∀ att : S → Finset S, 0 ≤ combinedWeight att)                       -- nonneg (WS2)
  ∧ (combinedWeight attTri < partsWeight attTri)                         -- nonclassical (WS2)
  ∧ (respectsCancel combinedWeight)                                      -- sqConsistent (WS3)
  ∧ (¬ respectsCancel partsWeight)                                       -- classicalFails (WS3)
```

## The five audit clauses (a)-(e)

```lean
-- (a) THE BORN RULE IS EARNED, NOT NAMED (the no-smuggling gate, sharpest here). No object defines the
-- probability as |amp|². The consistency predicate `respectsCancel` is form-agnostic; the squared form
-- is PROVED consistent (and the classical refuted), and is a function of the built amp/hol/incr.
theorem ws5_audit_earned :
    (respectsCancel combinedWeight ∧ ¬ respectsCancel partsWeight)
  ∧ (∀ att : S → Finset S, combinedWeight att = (directAmp + loopAmp att) ^ 2)
  ∧ (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2))

-- (b) THE FORK NOT BY FIAT. `squared` (non-trivial measure, consistent) and `deterministic` (a constant
-- weight is trivial) both reachable from the SAME objects; the two candidate measures genuinely differ.
theorem ws5_audit_fork_genuine :
    (combinedWeight attTri ≠ combinedWeight attStar)
  ∧ (∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att')
  ∧ (combinedWeight attTri ≠ partsWeight attTri)

-- (c) THE WEIGHT IS NON-CLASSICAL. The combined weight falls strictly below the parts (Series 2.11),
-- ruling out any classical additive probability (classically weights add, combined ≥ parts).
theorem ws5_audit_nonclassical : combinedWeight attTri < partsWeight attTri

-- (d) THE SCOPE IS DISCLOSED. The amplitude is a real ±1 (amp_values); no theorem claims the full
-- complex amplitude or Gleason's uniqueness (the disclosed forward-note). The rebit Born rule only.
theorem ws5_audit_scope : ∀ n : ℤ, amp n = 1 ∨ amp n = -1

-- (e) NAMES-NOT-TERMS. A META-property about identifiers, not a proposition: no proof term is named
-- for the interpretive content ("weight," "measure," "probability," "Born," "chance," ...). Enforced by
-- the protocol §6 grep (hits are docstring prose / the Lean `import` keyword only), the accepted house
-- placeholder.
theorem ws5_audit_names_not_terms : True
```

## Proofs (by hand, checked)

- `ws5_verdict_eq`, `ws5_verdict_discriminates`: `rfl` / `by decide` (finite Bool computation).
- `ws5_flags_justified`: `⟨ws1_measure_nontrivial, ws2_sq_nonneg, ws2_not_classical, ws3_sq_consistent.1, ws3_classical_fails⟩` (WS2 nonneg is `∀ att, 0 ≤ combinedWeight att`).
- `ws5_audit_earned`: `⟨ws3_sq_forced.left-and-mid, ws3_sq_earned.1, ws3_sq_earned.2⟩` (assemble from `ws3_sq_consistent.1`, `ws3_classical_fails`, `ws3_sq_earned`).
- `ws5_audit_fork_genuine`: `⟨ws1_measure_nontrivial, ws4_deterministic_reachable, ws3_sq_forced.2.2⟩`.
- `ws5_audit_nonclassical`: `ws2_not_classical`.
- `ws5_audit_scope`: `P2S11.amp_values`.
- `ws5_audit_names_not_terms`: `trivial`.

## The computed verdict

On this world's earned flags — `nontrivial = true` (`ws1_measure_nontrivial`), `nonneg = true` (`ws2_sq_nonneg`), `nonclassical = true` (`ws2_not_classical`), `sqConsistent = true` (`ws3_sq_consistent`), `classicalFails = true` (`ws3_classical_fails`) — `verdict = Outcome.squared`: **BORN**, quantum probability recovered in its rebit form. The imports carry a non-trivial measure whose only cancellation-consistent form is the squared amplitude, the classical additive form refuted. The full complex amplitude and Gleason's / Busch's uniqueness are the disclosed forward-note.

## Costume watch

- The verdict is COMPUTED from the flags (`rfl`), never hand-set; it DISCRIMINATES (all five outcomes reachable); the flags are EARNED (each a WS1-WS4 headline). BORN rests on the squared form being FORCED by the form-agnostic consistency test (WS3), not on a definition; the classical measure genuinely FAILS (an explicit witness), not excluded by fiat; the scope is disclosed (real ±1, no complex/Gleason). No name is a term.
