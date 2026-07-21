# Program 2 Series 5 (2.5) — Design index (`spec/README.md`)

**THE LOOP, and the fold it closes on. This is the design batch for Series 2.5: THE FOLD (the topology of the
whole — no poles, closed through the diagonal, the largest bending into the smallest) as the ground, and the
LOOP question (whether the causal/temporal relation can close). It fixes the imported chain, the primitives (the
fold and the causal relation, built fresh), the discipline (the knot on the coexistence not on well-foundedness,
the fork not by fiat, the fold on the diagonal), the cross-workstream triage, the outcome classes, and the
names-in-prose rule. Committed as one batch with `ws1-design.md`…`ws5-design.md` before any `formal/` file
exists (Phase B gate).**

---

## 1. The imported chain (reached, not rebuilt)

Series 2.5 imports **`P2S4` only** and reaches `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively (the layered
chain; the gate enforces `^import (P2S4|P2S5)…`). Its working material, reached through the chain:

| Piece | Origin (transitive) |
|---|---|
| The diagonal (makes the fold): `ws1_no_self_total_hold`, `ws2_residue_distinct`, `ws2_residue_free`, `ws1_insp_not_surjective`, `residue`, `Hold`, `HoldPred`, `SelfTotal` | `P1.Core` |
| The reification section: `FinReify`, `ws1_reification_exists`, `ws1_finreify_injective` | `P2S0` |
| The attention carrier: `attends`/`outDest`, `SHNE`, `ws1_bound_is_finite_attention` | `P2S0` / `P1.Core` |
| The tick witness `TCar = Fin 7`: `attendsT`, `rankT`, `reifyT`, `p0`/`p1`/`kA`/`kB`/`kC`, `cycleA`, `isTick`, `ws1_cycle_reifies`, `ws1_tcar_SHNE`, `ws4_causal_order_endogenous` | `P2S1` |
| **The fold** (no poles; the largest bending into the smallest through the diagonal) and **the causal relation** (`causalDep`, a structural reification-dependency) | **built fresh at S5** |

**Series 2.5 adds exactly two things:** THE FOLD (WS1, the topology of the whole via the diagonal) and the LOOP
question (whether `causalDep` can close). Nothing below `P2S4` is imported directly.

## 2. The primitives, built fresh

### 2.1 The causal relation (a structural reification-dependency)

```
@[reducible] def causalDep {X : Type u} (attends : X → Finset X) (comp : X → Prop) (t u : X) : Prop :=
  comp u ∧ t ∈ attends u
```

`u`, a reified composite (`comp u`), consumes its constituent `t` (`t ∈ attends u`). NO rank in the definition
(audit b): its acyclicity is PROVED from the rank-lift (`ws3_causal_rank_lift`, by `decide` on `TCar`), not
stipulated. On `TCar`, `comp := isTick`; the causal edges run base → composite (`p0 → kA`, `kA → kC`), upward.

### 2.2 The fold (the diagonal, the self-membered point)

The fold is the DIAGONAL's work, never an import's. The totalizing self-inspection produces a residue point no
hold contains (`ws2_residue_distinct` — the largest bends into the smallest) and the self-total seam Ω = {Ω} is
unrealizable (`ws1_no_self_total_hold`). At the level of the causal relation, a fold point is a SELF-CONSTITUTING
relatum `causalDep x x` (a composite that is its own constituent) — the sole candidate for a closed causal loop
(WS4). On the genuine tick carrier no such point exists (rank strictly raises); its LOOPED alternative is
reachable on a second carrier where a self-membered point Ω = {Ω} is posited.

### 2.3 The two witnesses

Both at `Cardinal.{0}` on `Fin`, monomorphic (as in S0/S1/S4).

- **The tick carrier `TCar = Fin 7`** (reached from `P2S1`): the ACYCLIC zone. It carries a genuine directed
  attention cycle `p0 ⇄ p1` (WS2, relating loops) whose reification `kA` and higher closure `kC` give causal
  edges that strictly raise `rankT` (WS3, acyclic), and NO self-membered composite (`ws4_no_fold_on_tower`).
  Cyclic relating with acyclic causation, on one structure.
- **The fold carrier `FCar = Fin 1`** (built fresh): the LOOPED zone. A self-membered point `om`
  (`attendsF om = {om}`, `compF om`) yields a genuine causal self-loop (`ws4_looped_reachable`,
  `Relation.TransGen (causalDep attendsF compF) om om`) that admits NO rank-lift (`ws4_fold_no_rank`). It shows
  LOOPED is a reachable structure — the fork is not decided by fiat — and that the sole place a loop can live is
  the fold, where the rank argument breaks.

## 3. The discipline (the honesty invariants, transcribed)

- **The knot on the coexistence, not well-foundedness (audit c, the Phase-2 costume gate).** The verdict
  (WS5) is ACYCLIC only with the WS2 cyclic-relating flag AND the WS4 LOOPED-reachable flag true; it does not
  strip to "a well-founded relation is acyclic." The finding is that the relating GENUINELY cycles (WS2) while
  causation GENUINELY does not (WS3), and the sole candidate for a loop is the fold (WS4).
- **The fork not by fiat (audit b).** `causalDep` is structural (no rank in the definition); acyclicity is
  PROVED (`ws3_causal_rank_lift`), and LOOPED is genuinely reachable (`ws4_looped_reachable`), so a
  self-constituting relatum is not excluded by construction.
- **The fold is the diagonal (audit d).** `ws1_fold` and the diagonal conjunct of `ws4_loop_only_at_fold` are
  `ws2_residue_distinct` / `ws1_no_self_total_hold`, the P1 diagonal; no seated import (Series 07) is invoked.
- **No poles decided absolutely (audit a).** No smallest is `SHNE` (reachability-relative); no largest is the
  reification section producing a fresh relatum from any pattern, no absolute ceiling.
- **Names-not-terms (audit e).** No proof term, definition, or discharged obligation is named "time," "loop,"
  "causal," "fold," "pole," "self," "here," "there," "God," "choice," or "subjectivity" as content. The carriers
  use neutral names (`causalDep`, `TCar`, `FCar`, `om`, `rankT`, `Outcome.acyclic`/`looped`); the interpretive
  words live only in docstring prose. Audit e is enforced by the protocol §6 grep, not by a proof term.

## 4. Cross-workstream triage

| WS | Payoff | Strips to |
|---|---|---|
| WS1 | the fold and the poles: no smallest, no largest, the largest bending into the smallest, the whole uncountable from within | no leaf; a section yielding a fresh relatum from any pattern; no hold realises the residue; no self-total hold; no surjection onto contents |
| WS2 | the relating genuinely cycles and reifies | a directed 2-cycle in a relation that reifies into a relatum sectioning its pattern |
| WS3 | causation is acyclic: the reification-dependency raises rank, no return | a relation inside strict `ℕ`-rank-increase has no `TransGen` loop |
| WS4 | the loop at the fold: the fold the sole candidate, LOOPED reachable, no fiat, no costume | a `TransGen` loop in a rank-raising relation forces a self-loop; a self-membered point has a self-loop admitting no rank-lift; no self-total inspection |
| WS5 | the verdict computed + audit a–e | an `Outcome`-valued function of five booleans, `= acyclic` by `rfl`, discriminating by `decide`, flags earned by the WS1–WS4 headlines |

## 5. Outcome classes (WS5)

`inductive Outcome | acyclic | looped | shapeDrawn | partial'` (neutral names; no forbidden content-name).
`acyclic` is the computed verdict on the certified flags (the relating loops, causation is acyclic, the fold is
the sole candidate and is not realized on the genuine tower); `looped` if the genuine tower realized a
self-membered causal loop (time closes at the One), reported in its direction; `shapeDrawn` if the fold is drawn
as the sole candidate but its status is undecidable; `partial'` if an obligation lands degenerate (no cyclic
relating, or LOOPED excluded by fiat).

## 6. Module layout (`P2S5` namespace, registered at Phase E)

`P2S5.lean` imports `P2S5.ws1`…`P2S5.ws5`; `P2S5/wsN.lean` one per workstream; `P2S5/AxiomCheck.lean` runs
`#print axioms`. `ws1` imports `P2S4` (the chain); `ws2`…`ws5` import their predecessor `ws` files. Namespace
`P2S5`, mirroring `program-1/series-13/formal/Series13/`. Gate: `check program-2/series-5
"^import (P2S4|P2S5)(\.[A-Za-z0-9_]+)*$"`.

---

*No em dashes in final academic copy. The fold this batch designs is the shape of the whole; the loop is whether
time can close on it. The verdict is computed, never hand-set; the fork is genuine (LOOPED reachable on the fold
carrier); the knot rests on the coexistence of cyclic relating and acyclic time, not on rank being well-founded
alone.*
