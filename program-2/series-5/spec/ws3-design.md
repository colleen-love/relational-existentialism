# WS3 design — Causation is acyclic (the tower does not return) (2.5)

**Prove that CAUSATION — the reification-dependency, the relation by which a relatum is minted from a pattern of
others — strictly raises reification rank and is therefore well-founded: no causal path among distinct relata
returns to its origin. The reified cycle sits ABOVE its constituents; following causation goes up, never back.
The acyclicity is PROVED from the rank-lift, NOT built into the definition of the causal relation (audit b, no
fiat).**

## 1. Candidate constructions

1. **Define "causal" as rank-increasing.** REJECTED: the sin of the fiat (charter 4.b). If causation is DEFINED
   as `rank t < rank u`, acyclicity is a triviality and LOOPED is excluded by construction. The strip test and
   the LOOPED-reachable check (WS4) are the guards.
2. **A structural reification-dependency, acyclicity a THEOREM (CHOSEN).** Define `causalDep attends comp t u :=
   comp u ∧ t ∈ attends u` — `u`, a reified composite (`comp u`), consumes its constituent `t` (`t ∈ attends
   u`). NO rank in the definition. Then PROVE the rank-lift `causalDep t u → rank t < rank u` on the concrete
   carrier (a reified composite outranks its constituents), and derive acyclicity from it via a general
   order lemma.

## 2. Triage

- **Fork not by fiat (audit b).** `causalDep` mentions only `attends` and `comp`, never `rank`; the rank-lift is
  a separate PROVED fact (`ws3_causal_rank_lift`, by `decide` on `TCar`). So a self-constituting relatum
  (`causalDep x x`) is NOT excluded by the definition — it is excluded on the tick carrier only by the rank
  fact, and it is genuinely REACHABLE elsewhere (WS4's fold carrier). Acyclicity is earned, not stipulated.
- **The knot is the coexistence (audit c).** The relating cycles (WS2, `p0 ⇄ p1`) while causation does not: on
  the SAME carrier `causalDep` strictly raises `rankT`, so `¬ ∃ x, TransGen causalDep x x`. Cyclic relating,
  acyclic time.
- **Strip test.** The payoff strips to "a relation contained in strict `ℕ`-rank-increase is acyclic (has no
  `TransGen` loop)." A bare well-foundedness fact — which is exactly why WS3 ALONE is the costume; the finding
  needs WS2 (the relating genuinely cycles) and WS4 (the fold is the sole candidate) beside it.

## 3. Winning construction — typed signatures

```
-- The fresh structural causal relation (reification-dependency): no rank in the definition.
@[reducible] def causalDep {X : Type u} (attends : X → Finset X) (comp : X → Prop) (t u : X) : Prop :=
  comp u ∧ t ∈ attends u

-- General: a rank-raising relation has no closed loop (the order spine).
theorem causation_acyclic {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (h : ∀ a b, r a b → rank a < rank b) : ¬ ∃ x, Relation.TransGen r x x

-- The rank-lift PROVED on the tick carrier (a composite outranks its constituents), not definitional.
theorem ws3_causal_rank_lift :
    ∀ t u : TCar, causalDep attendsT isTick t u → rankT t < rankT u

-- Causation is acyclic on the tick carrier: no closed causal loop.
theorem ws3_causation_acyclic :
    ¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x
```

## 4. Why acyclicity is proved, not defined (audit b)

`causalDep` is `comp u ∧ t ∈ attends u`: purely the structural fact that the composite `u` consumes `t`. The
rank-lift is a SEPARATE theorem discharged by `decide` on `TCar` (ticks `kA`, `kB` at rank 1 consume base relata
at rank 0; `kC` at rank 2 consumes `kA`, `kB` at rank 1). Acyclicity then follows from a general lemma
(`causation_acyclic`) that a rank-raising relation has no `TransGen` loop. Remove the rank-lift theorem and the
definition alone proves NOTHING about acyclicity — the fork stays open (a self-constituting relatum would be a
loop), as WS4's fold carrier shows.

## 5. Outcome classes

- **Causation acyclic (expected):** `ws3_causation_acyclic` holds; the reified cycle spirals up, never back.
- **PARTIAL (pre-registered):** if the rank-lift failed on the witness (some composite not outranking a
  constituent), acyclicity would not follow and the obligation lands degenerate, reported.

## 6. Strip annotation

- `causation_acyclic` → "a relation sitting inside strict `ℕ`-rank-increase has no transitive-closure loop."
- `ws3_causal_rank_lift` → "on the finite carrier, the composite-consumes-constituent relation raises `rank`."
- `ws3_causation_acyclic` → "the reification-dependency on `TCar` has no closed loop." A bare acyclicity fact;
  the finding is its COEXISTENCE with the WS2 cycle, not this alone.
