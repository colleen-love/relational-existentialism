# Series 2.10 design index (`spec/README.md`) — THE REVERSAL

**The design layer for the second tier-1 probe of Phase 3, the most consequential. Read `reversal-derisking.md` first (the paper gate: the section decodes but does not preserve the built rank, and the honest search finds NO measure-preserving bijective sub-dynamics inside the built tick, though the criterion is satisfiable). This README fixes the shared objects, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All six files plus the de-risking are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported chain (quantified, never named as content)

Series 2.10 imports `P2S8` only; `P2S7 / … / P2S0 / P1` are reached transitively. Working material, reused verbatim:

- **The tick and its reification section** — `P2S1.attendsT`/`P2S1.reifyT`, and the same shape at `P2S7` (`attendsM`/`reifyM`): `attends (reify s) = s` on the used patterns (a right-inverse — the DECODER). The tick under study is `reify {·}`, the reification map on a singleton pattern.
- **The built measure (the rank)** — `P2S7.rankM : MCar → ℕ`, the reification-tower height, the measure the tick moves and that a genuine reversal must PRESERVE (audit d). Not a fresh gadget.
- **The arrow** — `P2S7.ws2_tick_raises`: the reification tick STRICTLY raises the rank (`rankM (reifyM {e0}) = rankM e0 + 1`).
- **The collapse engine / the diagonal** — `AttentionDistinguishes`, `P1.Reader` (`ws2_residue_free`) — reached transitively; the identification that makes the tick non-injective, and self-reference-as-creation, the obstruction to reversal.

The invertibility question is the ONE thing Series 2.10 adds (§3); the measure that must be preserved is the built `rankM`.

## 2. The shared objects (built on the imported carrier and rank; `formal/P2S10/ws1..ws5`)

```
abbrev Cfg : Type := P2S7.MCar               -- = Fin 4;  states e0, e0', e1, e2  (the configurations)
abbrev mu  : Cfg → ℕ := P2S7.rankM           -- THE MEASURE: the built reification rank (audit d)

def tick  : Cfg → Cfg := fun x => reifyM {x}                                    -- THE TICK: the built reification map
def tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x  -- a CONTROL: the rank-0 swap

-- THE CORE CRITERION: a rank-preserving bijective sub-dynamics (the higher bar), decidable over Finset Cfg.
def IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D) ∧ (D.image t = D)
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y) ∧ (∀ x ∈ D, m (t x) = m x)

-- Decidability instance (so `ws4_no_core_built`, `ws4_core_reachable` discharge by `decide` over Finset Cfg):
instance decIsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Decidable (IsCore t m D) := by
  unfold IsCore; infer_instance
```

The tick unfolds (all `decide`/`rfl`): `tick e0 = e1`, `tick e1 = e2`, `tick e0' = e0`, `tick e2 = e0` — a tail `e0'` feeding a 3-cycle `e0→e1→e2→e0`. Everything downstream is a finite fact on `Fin 4`: `decide`/`rfl`/`omega`-checkable.

## 3. The primitive: what Series 2.10 adds

Exactly one thing: the INVERTIBILITY question about the built tick, made precise as a measure-preserving bijection, and the sharp distinction between a decodable section and a genuine dynamical reversal. It proves the tick genuinely moves (WS1), the full tick is not invertible (WS2), decodability is strictly weaker than reversal and states the core criterion (WS3), and the fork — a core reachable on a control vs no core in the built tick — reaches a computed value (WS4/WS5). No new dynamics is built; the reversibility of the BUILT tick is the question, and the measure is `rankM`.

## 4. The discipline (the no-smuggling gate + the costume gate, first-class — the T1-S1 lesson)

- **No inverse smuggled (audit a, the phase sin).** `IsCore t m D` requires the BUILT map `t` (= `tick`) to itself be the bijection of `D`; no inverse map is postulated. The search is over restrictions of the built tick, and finds none (`ws4_no_core_built`).
- **Decodability is not reversal (audit c, the costume gate — the Series 2.7 lesson).** The section is a right-inverse (`attendsM (reifyM {e0}) = {e0}`) that DECODES the pattern but does NOT preserve the built rank (`rankM (reifyM {e0}) ≠ rankM e0`) and is not even a state-to-state sub-dynamics. A "reversal" that strips to the section is the look-alike. The verdict rests on `IsCore` (a measure-preserving bijection), never on the section.
- **The measure is the built rank, the higher bar (audit d).** `mu = P2S7.rankM`; the tick's rise IS `P2S7.ws2_tick_raises`. The core criterion demands bijection AND rank-preservation; bijectivity alone (the 3-cycle) is not enough.
- **The fork not by fiat (audit b).** The criterion is satisfiable on the built rank (`tickR`, `{e0,e0'}`) AND the built tick fails it — both against the same `mu`. Neither side is hard-wired; the test discriminates.
- **NOT-RECOVERED honorable, SHAPE-DRAWN / DISCONNECTED pre-registered.** If no measure-preserving bijective sub-dynamics exists inside the built tick (the expected case), the series lands `noCore` — the arrow is fundamental, the sharpest specification the program returns, reported in full and never relabelled into a pseudo-recovery on the section. `disconnected` (the tick does not move) and `shapeDrawn` (the criterion not shown satisfiable) are reachable in the verdict function; neither materialises.

## 5. Cross-workstream triage

| WS | Object | Headline(s) | Costume foreclosed |
|----|--------|-------------|--------------------|
| WS1 | `tick`, `mu` | `ws1_tick_moves` | the ground is non-trivial; the measure is the built rank, the tick the built reification |
| WS2 | `tick` | `ws2_tick_not_invertible` | not a bijection (non-injective) and not measure-preserving (raises) — the honest one-way start |
| WS3 | `attendsM`, `IsCore` | `ws3_section_not_measure_preserving`, `ws3_core_criterion` | the section decodes but does not preserve the measure; the criterion is the higher bar, satisfiable |
| WS4 | `tick`, `tickR`, `IsCore` | `ws4_core_reachable`, `ws4_no_core_built` | both sides genuine on the same rank; no inverse smuggled; the built tick has no core |
| WS5 | `verdict` | `ws5_verdict_eq (= noCore)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)–(e) | computed, not hand-set |

## 6. The outcomes (WS5)

`noCore` (the built tick has no measure-preserving bijective sub-dynamics though the criterion is satisfiable — NOT-RECOVERED, the arrow fundamental, the expected close, the sharpest specification: the next iteration must add a reversible substrate or accept statistical recovery), `coreFound` (the built tick HAS a genuine measure-preserving bijective sub-dynamics — RECOVERED-CORE, the surprise, opening conservation and the quantum reconstruction, reported only if it clears the higher bar), `shapeDrawn` (the criterion not shown satisfiable), `disconnected` (the tick does not move), `partial'` (degenerate; `partial` is a Lean keyword).

## 7. Names-in-prose rule (audit e)

The concept-words — reversal, reversible, symmetry, conservation, energy, time, self, import, God, choice — appear only in docstring prose. Every proof term, definition, and discharged obligation carries a NEUTRAL name (`tick`, `tickR`, `mu`, `IsCore`, `verdict`, `Outcome`, `ws*`, `ws2_tick_not_invertible` — "invertible" is not a forbidden word). No headline embeds a forbidden content-word as a whole word; in particular the WS3/WS4 headlines are named for the measure/bijection/section (`ws3_section_not_measure_preserving`, `ws4_no_core_built`), never for "reversal"/"reversible." The §6 grep runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt.
