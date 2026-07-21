# WS4 design — The loop at the fold (the knot) (2.5)

**Prove that the SOLE candidate for a closed causal loop is the FOLD: among distinct relata causation is acyclic
(WS3), so a closed causal loop requires a relatum that is its own reification-constituent — the diagonal
self-membered point. Then the fork on that point: ACYCLIC (a degenerate fixed point, no closed timelike curve),
LOOPED (a genuine causal loop, time closes at the One), or SHAPE-DRAWN (drawn, undecidable). The fork must be
GENUINE: the LOOPED reading REACHABLE (a self-membered point with a causal self-loop is a real structure, not
excluded by construction), the verdict a discriminating function. The knot rests on the COEXISTENCE (WS2 cyclic
relating + WS3 acyclic causation + the fold's uniqueness), not on well-foundedness alone (audit c). The fold
rests on the P1 diagonal (audit d).**

## 1. Candidate constructions

1. **Assert ACYCLIC directly (rank is well-founded, so no loop).** REJECTED: the costume (charter 4.a). That is a
   true fact about the order, not the finding; it strips to "a well-founded relation is acyclic" with no cyclic
   relating and no fold content.
2. **Localize the loop to the fold by the rank spine, and fork on the fold as the diagonal (CHOSEN).** Prove
   `loop_forces_selfloop`: given the rank rises on every DISTINCT-relata edge, a `TransGen` loop forces a
   self-loop `causal z z` — a self-constituting relatum, the fold. Bundle this (rank) with the diagonal
   (`ws1_no_self_total_hold`: the totalizing self-point is unrealizable) into `ws4_loop_only_at_fold`. Then the
   fork: on the genuine tick carrier NO fold point exists (`ws4_no_fold_on_tower`, rank strictly raises → the
   verdict is ACYCLIC); the LOOPED reading is REACHABLE on a second carrier where a self-membered point Ω = {Ω}
   yields a genuine causal self-loop (`ws4_looped_reachable`), which admits NO rank-lift (`ws4_fold_no_rank`) —
   precisely the fold, where acyclicity could fail. So the fork is genuine (no fiat).

## 2. Triage

- **No costume (audit c).** `ws4_loop_only_at_fold` bundles the rank localization with the diagonal, and the
  VERDICT (WS5) requires the WS2 cyclic-relating flag and the LOOPED-reachable flag as well: strip WS2 and the
  verdict is not ACYCLIC. The knot rests on the coexistence, not on rank-well-foundedness alone.
- **Fork not by fiat (audit b).** `ws4_looped_reachable` exhibits a genuine closed causal loop on the fold
  carrier (`causalDep attendsF compF om om`, a `TransGen` self-loop), so LOOPED is a reachable structure;
  `ws4_fold_no_rank` shows that structure admits NO rank-lift, so acyclicity on the tick carrier is a substantive
  fact about the tower, not a definitional artifact. The causal relation is the SAME structural `causalDep` on
  both carriers.
- **The fold is the diagonal (audit d).** The second conjunct of `ws4_loop_only_at_fold` is
  `ws1_no_self_total_hold` — the fold-as-total-self-inspection is forbidden by the P1 diagonal, so the fold's
  self-reference is a degenerate fixed point. No import (Series 07's `ws2_import_theorem`) is invoked.
- **Strip test.** `ws4_loop_only_at_fold` strips to "a `TransGen` loop in a rank-raising relation forces a
  self-loop, and no self-total inspection exists"; `ws4_looped_reachable` to "a self-membered point has a
  self-loop"; `ws4_no_fold_on_tower` to "no self-membered composite on the finite carrier." Bare
  self-membership / cycle / well-foundedness facts.

## 3. Winning construction — typed signatures

```
-- General order spine.
theorem transgen_rank_lt {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (h : ∀ a b, r a b → rank a < rank b) : ∀ a b, Relation.TransGen r a b → rank a < rank b
theorem loop_forces_selfloop {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u)
    (x : X) (hloop : Relation.TransGen r x x) : ∃ z, r z z

-- Loop-only-at-fold, bundled with the diagonal (audit d): a causal loop forces a self-constituting relatum,
-- and the totalizing self-point is forbidden (rests on `ws1_no_self_total_hold`).
theorem ws4_loop_only_at_fold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (r : X → X → Prop) (rank : X → ℕ)
    (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u) :
    (∀ x, Relation.TransGen r x x → ∃ z, r z z) ∧ (¬ ∃ t, SelfTotal insp t)

-- The tick carrier realizes NO fold point (rank strictly raises): the ACYCLIC direction.
theorem ws4_no_fold_on_tower : ¬ ∃ x : TCar, causalDep attendsT isTick x x

-- The LOOPED-reachable witness (the fold carrier): a self-membered Ω = {Ω} yields a genuine causal self-loop,
-- admitting no rank-lift. The fork is not by fiat.
abbrev FCar : Type := Fin 1
def om : FCar := 0
def attendsF : FCar → Finset FCar := fun _ => {om}
def compF : FCar → Prop := fun _ => True
theorem ws4_looped_reachable : Relation.TransGen (causalDep attendsF compF) om om
theorem ws4_fold_no_rank :
    ¬ ∃ rank : FCar → ℕ, ∀ t u, causalDep attendsF compF t u → rank t < rank u
```

## 4. Why the fork is genuine (no fiat, no costume)

Two carriers, one structural causal relation. On the tick carrier the rank strictly raises (WS3), so no
self-membered composite exists (`ws4_no_fold_on_tower`) and causation is acyclic: ACYCLIC. On the fold carrier a
self-membered point Ω = {Ω} is posited, giving a genuine closed causal loop (`ws4_looped_reachable`) that admits
no rank-lift (`ws4_fold_no_rank`): LOOPED is a reachable structure, and the sole place it lives is the fold.
Because LOOPED is reachable, the tick carrier's acyclicity is not a definitional triviality (no fiat), and
because the verdict also demands the WS2 cyclic-relating flag, it is not the rank costume (audit c). The fold's
degeneracy — that the totalizing self-point is forbidden — is the P1 diagonal (`ws1_no_self_total_hold`), so the
ACYCLIC reading is the diagonal's, not the import's (audit d).

## 5. Outcome classes

- **ACYCLIC (expected):** the fold the sole candidate, not realized on the genuine tower (rank strictly raises),
  its self-reference a degenerate fixed point (the diagonal) → the computed verdict is ACYCLIC (WS5).
- **LOOPED (pre-registered, honest):** if the genuine tower itself realized a self-membered causal loop, the
  verdict would be LOOPED — time closes at the One — reported in its direction, the reading rewritten.
- **SHAPE-DRAWN:** if the fold is drawn as the sole candidate but its status on the genuine tower is undecidable
  from the structure, reported as the honest terminus, never a relabel.

## 6. Strip annotation

- `loop_forces_selfloop` / `ws4_loop_only_at_fold` → "a loop in a rank-raising relation forces a self-loop; no
  self-total inspection exists."
- `ws4_no_fold_on_tower` → "no self-membered composite on the finite carrier."
- `ws4_looped_reachable` → "a self-membered point has a self-loop (a reachable cycle)."
- `ws4_fold_no_rank` → "a self-loop admits no strict-rank labelling."
