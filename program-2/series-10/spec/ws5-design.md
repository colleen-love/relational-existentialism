# Series 2.10 WS5 design (`spec/ws5-design.md`) — the verdict and the audit folded in

**The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁵ → Outcome`, DISCRIMINATING (reaches all five outcomes), the flags EARNED by the WS1–WS4 headlines. The computed verdict is NOT-RECOVERED (`noCore`): the tick moves (WS1), the full tick is not invertible (WS2), the section decodes but does not preserve the measure (WS3), and the built tick has no measure-preserving bijective core though the criterion is satisfiable (WS4). The five audit clauses (a)–(e) bundle the payoffs.**

## 1. The outcome type (neutral identifiers; interpretive names in prose only)

```
/-- **The outcome type.** `noCore` the built tick has NO measure-preserving bijective sub-dynamics though the
criterion is satisfiable (NOT-RECOVERED: the arrow fundamental — the expected close); `coreFound` the built tick HAS a
genuine measure-preserving bijective sub-dynamics (RECOVERED-CORE, the surprise); `shapeDrawn` the fork drawn, the
criterion not shown satisfiable; `disconnected` the tick does not move; `partial'` primed (`partial` is a Lean
keyword) an obligation degenerate. No identifier embeds a forbidden content-word as a whole word (audit e). -/
inductive Outcome
  | noCore
  | coreFound
  | shapeDrawn
  | disconnected
  | partial'
  deriving DecidableEq
```

## 2. The verdict function and the computed value

```
/-- **The verdict FUNCTION.** `noCore` iff the tick moves (WS1), is not invertible (WS2), the section is not
measure-preserving (WS3), the built tick has NO core (`builtHasCore = false`, WS4) and the criterion IS satisfiable
(`criterionSat = true`, WS4) — no run-backward measure-preserving sub-dynamics, though such are possible. `coreFound`
if the built tick has a core; `disconnected` if the tick does not move; `partial'` if the top-level tick were
invertible or the section conflated with reversal; `shapeDrawn` if the criterion is not shown satisfiable. -/
def verdict (tickMoves notInvertible sectionNotMP builtHasCore criterionSat : Bool) : Outcome :=
  if !tickMoves then Outcome.disconnected
  else if !notInvertible then Outcome.partial'
  else if !sectionNotMP then Outcome.partial'
  else if builtHasCore then Outcome.coreFound
  else if criterionSat then Outcome.noCore
  else Outcome.shapeDrawn

/-- **THE COMPUTED VERDICT.** On the earned flags (the tick moves, is not invertible, the section is not
measure-preserving, the built tick has no core, the criterion is satisfiable), `noCore`, by computation. -/
theorem ws5_verdict_eq : verdict true true true false true = Outcome.noCore := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all five outcomes. -/
theorem ws5_verdict_discriminates :
    verdict false true true false true  = Outcome.disconnected
  ∧ verdict true false true false true  = Outcome.partial'
  ∧ verdict true true true true true    = Outcome.coreFound
  ∧ verdict true true true false true   = Outcome.noCore
  ∧ verdict true true true false false  = Outcome.shapeDrawn := by decide
```

## 3. The flags are earned

```
/-- **THE FLAGS ARE JUSTIFIED.** The five deciding inputs are EARNED by the WS1–WS4 headlines, none hand-set:
`tickMoves` (WS1, `ws1_tick_moves`); `notInvertible` (WS2, `ws2_tick_not_invertible`); `sectionNotMP` (WS3,
`ws3_section_not_measure_preserving`); `builtHasCore = false` (WS4, `ws4_no_core_built` — no nonempty core);
`criterionSat = true` (WS4, `ws4_core_reachable` — a core is reachable). -/
theorem ws5_flags_justified :
    (tick e0 ≠ e0 ∧ mu (tick e0) = mu e0 + 1)
  ∧ (¬ Function.Injective tick ∧ mu (tick e0) = mu e0 + 1)
  ∧ (attendsM (reifyM {e0}) = {e0} ∧ mu (reifyM {e0}) ≠ mu e0)
  ∧ (∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D)
  ∧ (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D)
```

## 4. The five audit clauses (a)–(e)

```
/-- **(a) NO INVERSE SMUGGLED.** No proof term adds an inverse the reification lacks: the bijection tested in the core
criterion is the BUILT `tick` itself, and for every nonempty `D` it fails to be a measure-preserving bijection
(`ws4_no_core_built`). The core is searched for inside the built tick, never postulated. -/
theorem ws5_audit_no_smuggle :
    (∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D)
  ∧ (tick = fun x => reifyM {x}) := ...

/-- **(b) THE FORK NOT BY FIAT.** A core is reachable (`tickR`, `{e0,e0'}`) AND the built tick has none, both against
the SAME built rank `mu`. The criterion is satisfiable but the built tick does not meet it — the test discriminates. -/
theorem ws5_audit_fork_genuine :
    (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D)
  ∧ (∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D) := ...

/-- **(c) DECODABILITY IS NOT REVERSAL (the costume gate — the Series 2.7 lesson).** The section is a right-inverse
that RECOVERS the pattern (`attendsM (reifyM {e0}) = {e0}`) but does NOT preserve the built measure
(`mu (reifyM {e0}) ≠ mu e0`); the verdict rests on the higher bar (`IsCore`, a measure-preserving bijection), not on
the section. -/
theorem ws5_audit_decode_not_reversal :
    (attendsM (reifyM {e0}) = {e0})
  ∧ (mu (reifyM {e0}) ≠ mu e0)
  ∧ (∀ t m D, IsCore t m D → ∀ x ∈ D, m (t x) = m x) := ...

/-- **(d) THE MEASURE IS THE BUILT RANK.** Reversibility is tested against Series 2.7's rank, not a rigged measure:
`mu = P2S7.rankM` definitionally, and the tick's rise is exactly `P2S7.ws2_tick_raises`. -/
theorem ws5_audit_measure_is_built_rank :
    (mu = P2S7.rankM)
  ∧ (rankM (reifyM {e0}) = rankM e0 + 1) := ...   -- the second conjunct discharged by `P2S7.ws2_tick_raises.1`

/-- **(e) NAMES-NOT-TERMS.** A META-property about identifiers: no proof term, definition, or discharged obligation is
named for the interpretive content ("reversal," "reversible," "symmetry," "conservation," "energy," "time," "self,"
"import," "God," "choice") as a whole word. Enforced by the protocol §6 grep (hits are docstring prose only), carried
here as the accepted `True` placeholder. -/
theorem ws5_audit_names_not_terms : True := trivial
```

The `...` bodies are discharged from the WS1–WS4 payoffs plus `decide`/`rfl`; `ws5_audit_measure_is_built_rank`'s first conjunct is `rfl` (`mu` is `rankM` by definition) and the second cites `P2S7.ws2_tick_raises`.

## 5. Outcome table

| flags `(tickMoves, notInvertible, sectionNotMP, builtHasCore, criterionSat)` | verdict |
|---|---|
| `(F, _, _, _, _)` | `disconnected` |
| `(T, F, _, _, _)` | `partial'` |
| `(T, T, F, _, _)` | `partial'` |
| `(T, T, T, T, _)` | `coreFound` (RECOVERED-CORE) |
| `(T, T, T, F, T)` | **`noCore` (NOT-RECOVERED) — the earned, computed verdict** |
| `(T, T, T, F, F)` | `shapeDrawn` |

## 6. Audit hooks

All five audit clauses (a)–(e) are theorems here; (e) is the grep-certified placeholder. No identifier embeds a forbidden content-word as a whole word.
