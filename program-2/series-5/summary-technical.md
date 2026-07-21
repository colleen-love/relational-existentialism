# Series 2.5 — Technical summary

**Verdict: ACYCLIC** (computed by `P2S5.ws5_verdict_eq : verdict true true true true false = Outcome.acyclic`,
the five flags earned by `ws5_flags_justified`, none hand-set). The build is sorry-free, axiom-clean (Mathlib's
standard `propext` / `Classical.choice` / `Quot.sound`; the verdict computations depend on no axioms), gate-green
(`P2S5` imports `P2S4` only, reaching the chain transitively), and names-grep clean (every forbidden-word hit is
docstring prose). Namespace `P2S5`, built on the P1 diagonal and the Series 2.1 tick reached through `P2S4`.

## The construction

The two primitives Series 2.5 adds — built FRESH — are the causal relation and the fold, on two monomorphic
carriers at `Cardinal.{0}`.

**The causal relation (`ws3.lean`).** `@[reducible] def causalDep (attends : X → Finset X) (comp : X → Prop)
(t u : X) : Prop := comp u ∧ t ∈ attends u`: `u`, a reified composite (`comp u`), consumes its constituent `t`.
The definition mentions NO rank, so acyclicity is not definitional (audit b).

**The tick carrier `TCar = Fin 7`** (reached from `P2S1`): the ACYCLIC zone. It carries a genuine directed
attention cycle `p0 ⇄ p1` (relating loops), whose reification `kA` and higher closure `kC` give causal edges that
strictly raise `rankT` (base↦0, `kA`/`kB`↦1, `kC`↦2), and NO self-membered composite.

**The fold carrier `FCar = Fin 1`** (fresh, `ws4.lean`): the LOOPED-reachable zone. `attendsF _ = {om}`,
`compF = fun _ => True`, so `om` is a self-membered point `om = {om}` on which `causalDep` genuinely closes.

## The payoffs

**WS1 — the fold and the poles (`ws1.lean`).**
- `ws1_no_pole_below` — `∀ x : TCar, SHNE (outDest hinf attendsT) x` (`= ws1_tcar_SHNE`): no smallest, nothing
  bottoms out, reachability-relative.
- `ws1_no_pole_above` — for a total finite section `FinReify attends reify`, `attends (reify {x}) = {x}` and
  `reify {x} = x → attends x = {x}`: from any relatum a higher reified relatum, coinciding with `x` only at a
  self-membered fold point. `ws1_reify_nonvacuous` (`= ws1_reification_exists`) discharges the section
  non-vacuously.
- `ws1_fold` — `(∀ h, insp h ≠ residue insp) ∧ (¬ ∃ t, SelfTotal insp t)`: the largest self-inspection misses
  the residue point (`ws2_residue_distinct`), and the self-total seam is unrealizable (`ws1_no_self_total_hold`).
  The P1 diagonal, no import (audit d).
- `ws1_no_total_count` — `¬ Function.Surjective insp` (`= ws1_insp_not_surjective`): the whole cannot count
  itself (Cantor).

**WS2 — the relating loops (`ws2.lean`).**
- `ws2_relating_cycles` — `(p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ reifyT cycleA = kA ∧ attendsT (reifyT cycleA)
  = cycleA`: a directed 2-cycle between distinct base relata reifies to a composite sectioning its pattern. From
  `ws1_cycle_reifies`, by `decide`.

**WS3 — causation is acyclic (`ws3.lean`).**
- `transgen_rank_lt`, `causation_acyclic` — the general order spine: a relation inside strict `ℕ`-rank-increase
  has no `Relation.TransGen` loop (no axioms).
- `ws3_causal_rank_lift` — `∀ t u : TCar, causalDep attendsT isTick t u → rankT t < rankT u` (by `decide`): a
  composite outranks every constituent it consumes. PROVED, separate from the definition (audit b).
- `ws3_causation_acyclic` — `¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x`: no closed causal
  loop, from the rank-lift via `causation_acyclic`.

**WS4 — the loop at the fold (`ws4.lean`).**
- `loop_forces_selfloop` — if `rank` rises on every distinct-relata edge, a `TransGen` loop forces a self-edge
  `r z z` (`by_contra` + `transgen_rank_lt`).
- `ws4_loop_only_at_fold` — `(∀ x, TransGen r x x → ∃ z, r z z) ∧ (¬ ∃ t, SelfTotal insp t)`: the rank
  localization bundled with the P1 diagonal, so the named WS4 theorem rests on the diagonal (audit d).
- `ws4_no_fold_on_tower` — `¬ ∃ x : TCar, causalDep attendsT isTick x x` (by `decide`): the genuine tower
  realizes no self-membered composite (the ACYCLIC direction).
- `ws4_looped_reachable` — `Relation.TransGen (causalDep attendsF compF) om om`: a genuine reachable causal
  self-loop at the fold point (LOOPED reachable, no fiat, audit b).
- `ws4_fold_no_rank` — `¬ ∃ rank : FCar → ℕ, ∀ t u, causalDep attendsF compF t u → rank t < rank u`: the fold
  admits no rank-lift, precisely where the acyclicity argument breaks.

**WS5 — the verdict and the audit (`ws5.lean`).**
- `verdict : Bool⁵ → Outcome` (`Outcome := acyclic | looped | shapeDrawn | partial'`), gating `acyclic` behind
  `relatingCycles` AND `causationAcyclic && loopOnlyAtFold` AND `loopedReachable` AND `¬ foldRealizedOnTower`.
- `ws5_verdict_eq : verdict true true true true false = Outcome.acyclic` (by `rfl`, no axioms).
- `ws5_verdict_discriminates` — reaches `looped` (tower realizes the self-loop), `shapeDrawn` (causation not
  shown acyclic), and `partial'` (twice: no cyclic relating; LOOPED excluded by fiat): non-constant, no axioms.
- `ws5_flags_justified` — the five inputs earned by WS2 (`relatingCycles`), WS3 (`causationAcyclic`), WS4
  (`loopOnlyAtFold`, via `loop_forces_selfloop` on the rank-lift — NOT the bare rank-lift), WS4
  (`loopedReachable`), and the no-fold-on-tower fact (`foldRealizedOnTower = false`).
- Audit: `ws5_audit_no_absolute_frame` (a), `ws5_audit_fork_genuine` (b), `ws5_audit_knot_is_coexistence` (c),
  `ws5_audit_fold_is_diagonal` (d), `ws5_audit_names_not_terms` (e, the grep-certified placeholder).

## Discipline discharged

- **No poles decided absolutely (audit a):** no smallest is `SHNE` (reachability-relative); no largest is the
  reification section producing a fresh relatum from any pattern, with no absolute ceiling.
- **The fork not by fiat (audit b):** `causalDep`'s definition has no rank; its acyclicity is the proved
  `ws3_causal_rank_lift`; a genuine causal self-loop is reachable (`ws4_looped_reachable`) and admits no rank-lift
  (`ws4_fold_no_rank`), so the acyclicity of the tick carrier is a substantive fact, not a construction artifact.
- **The knot is the coexistence, not well-foundedness (audit c, the costume gate):** `verdict` returns `acyclic`
  ONLY with `relatingCycles` AND `loopedReachable` true; it does not strip to "a well-founded relation is
  acyclic." The relating genuinely cycles (WS2) WHILE causation does not (WS3), and the sole loop candidate is
  the fold (WS4). Verified in the blind design and blind code reviews (audit (c) pressed hardest in both).
- **The fold is the diagonal (audit d):** `ws1_fold` and the second conjunct of `ws4_loop_only_at_fold` are the
  P1 diagonal (`ws2_residue_distinct` / `ws1_no_self_total_hold`); no import/subsingleton-collapse theorem is
  invoked.
- **Names-not-terms (audit e):** the §6 grep is clean (hits are docstring prose only); no definition, theorem, or
  constructor is named for the temporal or topological content as a whole word. The general `{X : Type u}`
  payoffs auto-bind `κ` per-theorem so `κ` tracks `X`'s universe (recorded in `charter-status.md`).

## Provenance

Built on `P2S4` (reaching `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively). The fold (on the P1 diagonal
`ws1_no_self_total_hold` / `ws2_residue_distinct` / `ws1_insp_not_surjective`) and the causal relation
(`causalDep`) are built FRESH; the tick witness (`attendsT`, `rankT`, `reifyT`, `isTick`, `ws1_cycle_reifies`) is
reached from `P2S1`. Nothing below `P2S4` is imported directly; the closure gate enforces `^import (P2S4|P2S5)…`.
Program 1's permanent opens are carried untouched.
