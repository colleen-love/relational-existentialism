# Series 2.10 (The Reversal) — technical summary

**Status: BUILT and reviewed. Verdict `noCore` (NOT-RECOVERED / IRREVERSIBLE), computed. The full development is `program-2/series-10/formal/P2S10/` (`ws1`–`ws5`, `P2S10`, `AxiomCheck`); it compiles sorry-free, axiom-clean (standard three), gate-green, names-grep clean. Imports `P2S8` only; `P2S7 / … / P2S0 / P1` transitive.**

## 1. What is built

The carrier and the measure are IMPORTED from Series 2.7, reused verbatim (audit d): `Cfg := P2S7.MCar` (`= Fin 4`; states `e0, e0', e1, e2`) and the measure `mu := P2S7.rankM` (the reification rank; `mu e0 = mu e0' = 0`, `mu e1 = 1`, `mu e2 = 2`). The tick under study is the BUILT reification map on the singleton pattern:

```
tick x : Cfg := reifyM {x}          -- tick e0 = e1, tick e1 = e2, tick e0' = e0, tick e2 = e0
```

a tail `e0'` feeding the 3-cycle `e0 → e1 → e2 → e0`. Two more objects:

```
tickR x : Cfg := if x = e0 then e0' else if x = e0' then e0 else x   -- a CONTROL: the rank-0 swap
IsCore t m D : Prop :=                                               -- the core criterion (the higher bar)
    (∀ x ∈ D, t x ∈ D) ∧ (D.image t = D)
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y) ∧ (∀ x ∈ D, m (t x) = m x)
```

`IsCore t m D` says `t` is a measure-preserving bijection of the finite `D`: closed, surjective onto `D`, injective on `D` (⇒ a bijection `D → D`), and rank-preserving. A decidability instance (`decIsCore`, by `unfold; infer_instance`) lets the WS4 quantifier-over-subsets discharge by `decide`.

## 2. The theorems

| Theorem | Content |
|---|---|
| `ws1_tick_moves` | `tick e0 ≠ e0 ∧ mu (tick e0) = mu e0 + 1` — the tick moves and raises the measure |
| `ws2_tick_not_invertible` | `¬ Function.Injective tick ∧ (∃ x, mu (tick x) ≠ mu x) ∧ mu (tick e0) = mu e0 + 1` — not a bijection (`tick e0' = tick e2 = e0`), not measure-preserving |
| `ws3_section_not_measure_preserving` | `attendsM (reifyM {e0}) = {e0} ∧ mu (reifyM {e0}) = mu e0 + 1 ∧ mu (reifyM {e0}) ≠ mu e0` — the section decodes but does not preserve the rank (decodability ⊊ reversibility) |
| `ws3_core_criterion` | `(∀ t m D, IsCore t m D → (∀ x ∈ D, m (t x) = m x) ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y)) ∧ (∃ D, D.Nonempty ∧ IsCore tickR mu D)` — the criterion entails the full higher bar AND is satisfiable |
| `ws4_core_reachable` | `∃ D, D.Nonempty ∧ IsCore tickR mu D` — a measure-preserving bijective sub-dynamics exists on the built rank (`D = {e0, e0'}`) |
| `ws4_no_core_built` | `∀ D, D.Nonempty → ¬ IsCore tick mu D` — the BUILT tick has NO nonempty core (`decide` over the 16 subsets) |
| `ws5_verdict_eq` | `verdict true true true false true = Outcome.noCore` (`rfl`) |
| `ws5_verdict_discriminates` | the five-input verdict reaches all five outcomes |
| `ws5_flags_justified` | the five deciding flags are the WS1–WS4 facts |
| `ws5_audit_no_smuggle` / `_fork_genuine` / `_decode_not_measure_preserving` / `_measure_is_built_rank` / `_names_not_terms` | audit (a)–(e) |

## 3. The mathematics

The construction is the elementary finite-dynamics fact that a self-map is a bijection on a finite set `D` only if `D` is a union of its cycles (periodic points), and a bijection preserves a labelling `m` iff `m` is constant on each cycle. The built tick's periodic set is the single 3-cycle `{e0, e1, e2}`; its rank labelling is `0, 1, 2`, non-constant, so the 3-cycle is a bijective sub-dynamics that does NOT preserve the measure. The pre-periodic point `e0'` (mapped into the cycle, never returning; not in the range of `tick`, since `reifyM` never outputs `e0'`) cannot lie in any bijective `D`. Hence no nonempty `D` clears both `IsCore` clauses — `ws4_no_core_built`, discharged by `decide` over `Finset (Fin 4)`.

The distinction the series turns on is made three ways, all against the SAME built rank `mu = rankM`:

1. **Right-inverse (decodable section) ≠ measure-preservation.** `attendsM` is a right-inverse to `reifyM` on the used pattern (`attendsM (reifyM {e0}) = {e0}`), but the composite raises the rank (`rankM (reifyM {e0}) = rankM e0 + 1`, imported `P2S7.ws2_tick_raises`). Type-wise `attendsM : Cfg → Finset Cfg` (state to pattern) is not even an iterable state sub-dynamics. `ws3_section_not_measure_preserving`, audit (c).
2. **Bijection ≠ measure-preserving bijection.** The 3-cycle is a bijection of `{e0,e1,e2}` that raises the rank; `IsCore` demands both clauses, so it is not a core. The higher bar is used, never bijectivity or decodability alone. Audit (d).
3. **The fork is genuine, not a fiat.** `IsCore` is satisfiable on `mu` (`tickR` on `{e0,e0'}`, a swap of two rank-0 states — `ws4_core_reachable`) and unsatisfiable by the built `tick` (`ws4_no_core_built`), both against the same `mu`. Audit (b).

No inverse is smuggled: `IsCore` in `ws4_no_core_built` / `ws5_audit_no_smuggle` tests the built `tick` itself (`tick = fun x => reifyM {x}`, `rfl`); `tickR` is a separate control (a relabelling), used only as the positive satisfiability witness, never as an inverse of `tick`. Audit (a).

## 4. The verdict

`verdict : Bool⁵ → Outcome` with `Outcome ∈ {noCore, coreFound, shapeDrawn, disconnected, partial'}`. On the earned flags `(tickMoves, notInvertible, sectionNotMP, builtHasCore, criterionSat) = (true, true, true, false, true)` it computes `noCore` (`ws5_verdict_eq`, `rfl`). `builtHasCore = false` is earned by `ws4_no_core_built`; `criterionSat = true` by `ws4_core_reachable`. The function discriminates (all five outcomes reached, `ws5_verdict_discriminates`); the flags are the WS1–WS4 statements (`ws5_flags_justified`). The verdict is the residue of the built theorems, not a premise: `coreFound` (RECOVERED-CORE), `shapeDrawn`, `disconnected`, `partial'` were all reachable in the function and none realized.

## 5. Charter-label → built-name map (audit e; deviations in `charter-status.md` §5)

`ws3_section_is_not_reversal` → `ws3_section_not_measure_preserving`; `ws4_reversible_core_reachable` → `ws4_core_reachable`; `ws4_irreversible_reachable` → `ws4_no_core_built`; outcomes REVERSIBLE-CORE / IRREVERSIBLE → `coreFound` / `noCore`. The words "reversal"/"reversible"/"symmetry"/"conservation"/… appear only in docstring prose; no proof term, definition, or discharged obligation carries a forbidden whole-word identifier (§6 grep clean).

## 6. Checks

`lake build P2S10 P2S10.AxiomCheck` succeeds. `#print axioms` over every payoff: each depends only on `propext` / `Classical.choice` / `Quot.sound` (or no axioms: `ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_audit_names_not_terms`). `scripts/gate.sh`: `P2S10` imports resolve only to `P2S8` / `P2S10` / Mathlib. Names grep clean (prose only). Full default `lake build` passes (no regression). Blind design review (Phase C, 2 rounds → 0 SERIOUS) and blind code review (Phase F → 0 SERIOUS / 0 REAL / 1 COSMETIC, the accepted `True` names placeholder).
