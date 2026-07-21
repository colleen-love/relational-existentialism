# Series 2.10 WS1 design (`spec/ws1-design.md`) — the tick as a map and its measure (the ground)

**FORMALIZE the tick as a total map on configurations together with the built measure it moves, so that "invertible" and "measure-preserving" are well-posed and non-trivial. Prove the setup genuinely MOVES: the tick changes the configuration and raises its measure — there is something to reverse.**

## 1. Objects (built on the imported chain; carrier and measure reused verbatim)

Import `P2S8` (reaching `P2S7 / … / P1` transitively); `open P2S7`. The configuration carrier and the measure are the BUILT objects of Series 2.7 (audit d: the measure is the built rank), not fresh gadgets.

```
abbrev Cfg : Type := P2S7.MCar                 -- = Fin 4;  states e0, e0', e1, e2
abbrev mu  : Cfg → ℕ := P2S7.rankM             -- THE MEASURE: the built reification rank

def tick : Cfg → Cfg := fun x => P2S7.reifyM {x}   -- THE TICK: the built reification map on the singleton pattern
```

`tick` unfolds (all `decide`/`rfl`): `tick e0 = e1`, `tick e1 = e2`, `tick e0' = e0`, `tick e2 = e0` (§ derisking §1). No new dynamics is built; the tick is the built `reifyM`.

## 2. The payoff signature

```
/-- **THE TICK MOVES (WS1).** The tick genuinely changes the configuration and RAISES its measure at the base
relatum: `tick e0 ≠ e0` and `mu (tick e0) = mu e0 + 1`. There is something to reverse; the ground is non-trivial. -/
theorem ws1_tick_moves :
    tick e0 ≠ e0
  ∧ mu (tick e0) = mu e0 + 1 := by
  refine ⟨by decide, by decide⟩
```

The measure-rise `mu (tick e0) = mu e0 + 1` is `rankM (reifyM {e0}) = rankM e0 + 1`, the content of `P2S7.ws2_tick_raises.1`; here discharged directly by `decide` over `Fin 4`, and cited from the built theorem in the WS5 audit (d).

## 3. Outcome classes and the strip test

- **Strip test.** Delete "tick," "moves": the bare fact is "a built map `f : Fin 4 → Fin 4` with `f e0 ≠ e0` and `rankM (f e0) = rankM e0 + 1`." Goes through as a plain arithmetic fact. No interpretive term carries it.
- **DISCONNECTED (pre-registered).** If the tick did not move (`tick e0 = e0` and `mu` unchanged) the ground would be degenerate; the verdict function returns `disconnected` on `¬tickMoves`. It does not materialise (`decide`).
- **No rigging.** The measure is `rankM`, imported. The tick is `reifyM`, imported. WS1 posits neither; it discharges the movement over the built objects.

## 4. Audit hooks

- (d) THE MEASURE IS THE BUILT RANK — `mu := P2S7.rankM` definitionally; the rise equals `ws2_tick_raises.1`.
- (e) NAMES-NOT-TERMS — identifiers `Cfg`, `mu`, `tick`, `ws1_tick_moves` carry no forbidden content-word as a whole word.
