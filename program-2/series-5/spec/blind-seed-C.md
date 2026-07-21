# Blind seed — Phase C (design review)

You are reviewing a set of Lean 4 (Mathlib, `Cardinal.{0}`) design signatures for coherence and non-vacuity.
Judge ONLY the mathematics below against the contracts stated here. This seed is self-contained; do NOT read any
other file in this repository.

## 0. Imported machinery you may assume (proved elsewhere, treat as given)

```
-- from the powerset-coalgebra / diagonal layer:
PkObj (κ) (X) : Type                       -- κ-bounded subsets of X
SHNE (dest : X → PkObj κ X) (x : X) : Prop  -- every reachable node has a nonempty successor set (no leaf)
outDest (hinf : ℵ₀ ≤ κ) (attends : X → Finset X) : X → PkObj κ X
Hold (dest) : Type;  HoldPred (dest) := Hold dest → Prop
SelfTotal (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop   -- ∀ h, insp t h ↔ ¬ insp h h
residue (insp) : HoldPred dest := fun h => ¬ insp h h
ws1_no_self_total_hold (dest) (insp) : ¬ ∃ t, SelfTotal insp t         -- the diagonal (no hypotheses)
ws2_residue_distinct   (dest) (insp) : ∀ h, insp h ≠ residue insp       -- the diagonal
ws1_insp_not_surjective(dest) (insp) : ¬ Function.Surjective insp       -- Cantor, from the diagonal
FinReify (attends : X → Finset X) (reify : Finset X → X) : Prop := ∀ s, attends (reify s) = s
ws1_reification_exists : ∃ X attends reify, FinReify attends reify ∧ Function.Injective reify

-- a fixed finite witness carrier (proved facts about it may be assumed):
TCar := Fin 7 ; nodes p0 p1 q0 q1 kA kB kC
attendsT : TCar → Finset TCar   -- p0⇄p1, q0⇄q1 (two 2-cycles); kA↦{p0,p1}, kB↦{q0,q1}, kC↦{kA,kB}
rankT    : TCar → ℕ             -- kA,kB ↦ 1 ; kC ↦ 2 ; else 0
reifyT   : Finset TCar → TCar   -- cycleA={p0,p1}↦kA, cycleB={q0,q1}↦kB, {kA,kB}↦kC
isTick (x) : Prop := x = kA ∨ x = kB ∨ x = kC
ws1_cycle_reifies : (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ reifyT cycleA = kA ∧ attendsT (reifyT cycleA) = cycleA ∧ …
ws1_tcar_SHNE (hinf) (x) : SHNE (outDest hinf attendsT) x
```

## 1. The definitions and signatures under review

```
-- (D1) the relation under study; NOTE: its definition does NOT mention rank.
@[reducible] def causalDep (attends : X → Finset X) (comp : X → Prop) (t u : X) : Prop := comp u ∧ t ∈ attends u

-- (D2) the second witness carrier:
abbrev FCar := Fin 1 ; def om : FCar := 0 ; def attendsF : FCar → Finset FCar := fun _ => {om} ; def compF := fun _ => True

-- WS1
theorem ws1_no_pole_below (hinf : ℵ₀ ≤ κ) (x : TCar) : SHNE (outDest hinf attendsT) x
theorem ws1_no_pole_above (attends : X → Finset X) (reify : Finset X → X) (h : FinReify attends reify) (x : X) :
    attends (reify {x}) = {x} ∧ (reify {x} = x → attends x = {x})
theorem ws1_reify_nonvacuous : ∃ X attends reify, FinReify attends reify ∧ Function.Injective reify
theorem ws1_fold (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ h, insp h ≠ residue insp) ∧ (¬ ∃ t, SelfTotal insp t)
theorem ws1_no_total_count (dest) (insp) : ¬ Function.Surjective insp

-- WS2
theorem ws2_relating_cycles :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ reifyT cycleA = kA ∧ attendsT (reifyT cycleA) = cycleA

-- WS3
theorem causation_acyclic (r : X → X → Prop) (rank : X → ℕ) (h : ∀ a b, r a b → rank a < rank b) :
    ¬ ∃ x, Relation.TransGen r x x
theorem ws3_causal_rank_lift : ∀ t u : TCar, causalDep attendsT isTick t u → rankT t < rankT u
theorem ws3_causation_acyclic : ¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x

-- WS4
theorem transgen_rank_lt (r) (rank) (h : ∀ a b, r a b → rank a < rank b) :
    ∀ a b, Relation.TransGen r a b → rank a < rank b
theorem loop_forces_selfloop (r) (rank) (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u)
    (x) (hloop : Relation.TransGen r x x) : ∃ z, r z z
theorem ws4_loop_only_at_fold (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (r : X → X → Prop) (rank : X → ℕ) (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u) :
    (∀ x, Relation.TransGen r x x → ∃ z, r z z) ∧ (¬ ∃ t, SelfTotal insp t)
theorem ws4_no_fold_on_tower : ¬ ∃ x : TCar, causalDep attendsT isTick x x
theorem ws4_looped_reachable : Relation.TransGen (causalDep attendsF compF) om om
theorem ws4_fold_no_rank : ¬ ∃ rank : FCar → ℕ, ∀ t u, causalDep attendsF compF t u → rank t < rank u

-- WS5
inductive Outcome | acyclic | looped | shapeDrawn | partial'
def verdict (relatingCycles causationAcyclic loopOnlyAtFold loopedReachable foldRealizedOnTower : Bool) : Outcome :=
  if !relatingCycles then partial'
  else if !(causationAcyclic && loopOnlyAtFold) then shapeDrawn
  else if !loopedReachable then partial'
  else if foldRealizedOnTower then looped
  else acyclic
theorem ws5_verdict_eq : verdict true true true true false = Outcome.acyclic
theorem ws5_verdict_discriminates :
    verdict true true true true true = looped ∧ verdict true false true true false = shapeDrawn
  ∧ verdict false true true true false = partial' ∧ verdict true true true false false = partial'
theorem ws5_flags_justified (hinf) :
    ((p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ attendsT (reifyT cycleA) = cycleA)
  ∧ (¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x)
  ∧ (∀ t u : TCar, causalDep attendsT isTick t u → rankT t < rankT u)
  ∧ (Relation.TransGen (causalDep attendsF compF) om om)
  ∧ (¬ ∃ x : TCar, causalDep attendsT isTick x x)
```

## 2. Success criteria (restated mechanically)

1. Every reachable node of `TCar` has a nonempty successor set; a total finite section produces from any `x` a
   relatum whose sole successor is `x`, equal to `x` only when `attends x = {x}`; no inspection realises its own
   residue and none is self-total; no inspection is surjective. (WS1)
2. A directed 2-cycle between distinct nodes exists and reifies to a node sectioning its pattern. (WS2)
3. `causalDep attendsT isTick` sits inside strict `rankT`-increase and hence has no `Relation.TransGen` loop. (WS3)
4. Any `TransGen` loop of a strictly-rank-raising relation forces a self-edge `r z z`; the `TCar` relation has no
   self-edge; a self-edge relation IS realised on `FCar` and admits no strict-rank labelling. (WS4)
5. `verdict` computes `acyclic` on the certified flag tuple by `rfl`, reaches all four outcomes, and its five
   inputs are exactly the WS1–WS4 propositions. (WS5)

## 3. Audit checks (mechanical instructions)

- **(a)** Confirm no signature asserts a smallest or largest element absolutely: `ws1_no_pole_below` is `SHNE`
  (reachability-relative); `ws1_no_pole_above` is a section fact with no absolute bound. Flag if any theorem posits
  an absolute top/bottom quantity.
- **(b)** Confirm `causalDep`'s DEFINITION (D1) does not mention `rank`, so its acyclicity is not definitional;
  confirm `ws3_causal_rank_lift` is a SEPARATE hypothesis/theorem; and confirm `ws4_looped_reachable` exhibits a
  genuine self-edge (so a self-constituting relatum is NOT excluded by construction). Flag if acyclicity is baked
  into the definition of `causalDep`, or if no reachable self-edge witness exists (fork by fiat).
- **(c)** Confirm `verdict` returns `acyclic` ONLY when `relatingCycles = true` AND `loopedReachable = true` (trace
  the branches). If `verdict` would return `acyclic` from `causationAcyclic` alone (ignoring `relatingCycles`), the
  knot rests on well-foundedness alone — flag SERIOUS. Confirm `ws5_flags_justified` carries the `relatingCycles`
  proposition beside `causationAcyclic`.
- **(d)** Confirm `ws1_fold` and the second conjunct of `ws4_loop_only_at_fold` reduce to the imported diagonal
  facts (`ws2_residue_distinct`, `ws1_no_self_total_hold`), NOT to any subsingleton/import-collapse theorem. Flag
  if the fold rests on an import theorem.
- **(e)** Grep the identifiers for the forbidden content-words as WHOLE words (`\b`-delimited, case-insensitive):
  `time|loop|causal|fold|pole|self|here|there|god|choice|subjectivity`. Report any identifier (definition,
  theorem, or constructor name) that IS one of these as a standalone word. (Substrings glued by `_`/camelCase to
  other tokens, e.g. `causalDep`, `ws1_fold`, `Outcome.looped`, are NOT whole-word matches and are acceptable.)

## 4. Strip test

For each payoff, delete the interpretive reading and check the statement still stands as a bare fact:
- `ws1_fold` → "no hold realises the residue; no self-total hold exists."
- `ws3_causation_acyclic` → "a relation inside strict `ℕ`-rank-increase has no `TransGen` loop."
- `ws4_loop_only_at_fold` → "a loop in a rank-raising relation forces a self-edge; no self-total inspection."
- `ws4_looped_reachable` → "a node with a self-edge has a `TransGen` self-loop."
- `verdict` → "an `Outcome`-valued function of five booleans reaching four values."
Flag any payoff that does NOT survive the strip (i.e. is vacuous, circular, or depends on the interpretation).

## 5. Grading rubric

- **SERIOUS:** the verdict rests on it; the knot rests on well-foundedness alone rather than the coexistence and
  the fold (audit c); the fork is a fiat — `causalDep` defined as rank-increasing, or no reachable self-edge
  (audit b); the fold rests on an import rather than the diagonal (audit d); an outcome is decided without the
  computation; a name is a forbidden content-word (audit e); or an undisclosed narrowing.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed statement, an assumed-and-returned
  hypothesis, an over-strong name, a well-foundedness fact dressed as a coexistence).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings, each with a stable ID `Cn-Sm`, its grade, exact location (signature name),
and the defect. If you find nothing SERIOUS, say so explicitly.
