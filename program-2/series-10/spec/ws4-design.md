# Series 2.10 WS4 design (`spec/ws4-design.md`) — the fork (RECOVERED-CORE vs NOT-RECOVERED), the knot

**Prove the fork on the built tick, honestly, neither side by fiat. The criterion is SATISFIABLE (a genuine measure-preserving bijective sub-dynamics is reachable, on a control dynamics) AND the BUILT reification tick has NO such core (the tick raises the measure on every reification edge). The verdict computes from the BUILT tick, and lands NOT-RECOVERED. The costume watch: a genuine core is measure-preserving and bijective, never the decodable section.**

## 1. The two sides (both on the four-element carrier and the SAME built rank `mu = rankM`)

**Side RECOVERED (the criterion is reachable — audit b, not a fiat).** The control dynamics `tickR` (WS3.ii) swaps the two rank-0 states and fixes the rest; `{e0, e0'}` is a nonempty measure-preserving bijective core.

```
/-- **A CORE IS REACHABLE (WS4, the criterion is not vacuous).** On the built rank, a genuine measure-preserving
bijective sub-dynamics EXISTS: `tickR` (the relabelling swap of the two rank-0 states) has the core `{e0, e0'}`. This
shows the fork is genuine — the NOT-RECOVERED finding on the built tick is discriminating, not a definitional
impossibility. `tickR` is a control, NOT the built reification tick. -/
theorem ws4_core_reachable :
    ∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D := by
  exact ⟨{e0, e0'}, ⟨e0, by decide⟩, by decide⟩
```

**Side NOT-RECOVERED (the built tick has no core — the expected close).** The built reification tick `tick` has no nonempty measure-preserving bijective sub-dynamics: its only bijective sub-dynamics is the 3-cycle `{e0, e1, e2}`, whose rank reads `0,1,2` and so cannot be preserved (derisking §4).

```
/-- **THE BUILT TICK HAS NO CORE (WS4, the NOT-RECOVERED headline).** For EVERY nonempty `D`, the built reification
tick is NOT a measure-preserving bijection on `D`: no rank-preserving bijective sub-dynamics exists. The one bijective
sub-dynamics (the 3-cycle `e0→e1→e2→e0`) raises the rank on its edges; every other nonempty `D` fails closure or
bijectivity. Proved by `decide` over the sixteen subsets of the carrier. The tick raises the measure at every scale;
the arrow is fundamental. -/
theorem ws4_no_core_built :
    ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D := by
  decide
```

## 2. Why this is the genuine fork (audit b), and the costume watch (audit c)

- **Both sides reachable, same carrier, same built rank.** `ws4_core_reachable` (a core exists for `tickR`) and `ws4_no_core_built` (no core for `tick`) are proved against the SAME `mu = rankM`. The criterion is satisfiable; the built tick just does not satisfy it. Neither side is hard-wired: a rigged criterion that no map could meet would make `ws4_core_reachable` false; a rigged criterion every map meets would make `ws4_no_core_built` false. Both hold, so the test discriminates.
- **Costume watch.** A genuine core is a measure-preserving BIJECTION (both `IsCore` clauses). The decodable section (WS3.i) is neither of this type nor measure-preserving, and never enters the fork. `ws4_no_core_built` rests on rank-preservation failing on a bijective sub-dynamics, not on the section.
- **No inverse smuggled (audit a).** `IsCore t mu D` requires `t` — here the built `tick` — to itself be the bijection of `D`. No inverse map is added; the search is over restrictions of the built tick.

## 3. Strip test and outcome classes

- **Strip test.** Delete "core," "reversible," "irreversible": "there is a nonempty `D` with `IsCore tickR rankM D`" and "for all nonempty `D`, `¬ IsCore tick rankM D`." Bare satisfiability / non-existence of a rank-preserving bijective restriction. No interpretive term carries the result.
- **RECOVERED-CORE (pre-registered surprise).** Had `ws4_no_core_built` failed — some nonempty `D` with `IsCore tick rankM D` — the verdict function returns `coreFound`. It does not materialise (`decide`).
- **SHAPE-DRAWN (pre-registered).** If the criterion were unsatisfiable (`ws4_core_reachable` false) the fork would be undecided → `shapeDrawn`. It does not materialise.

## 4. Audit hooks

- (a) no inverse smuggled — the bijection in `IsCore` is the built `tick` itself.
- (b) fork not by fiat — both sides reachable against the same built rank.
- (c) decodability is not reversal — the section is excluded from the fork; the core is the higher bar.
- (d) the measure is the built rank — `mu = rankM` in both theorems.
- (e) names-not-terms — `ws4_core_reachable`, `ws4_no_core_built` carry no forbidden content-word as a whole word.
