# Series 2.6 — Technical summary

**Series 2.6 (THE THREAD) builds, on the imported chain `P2S5 → … → P2S1 → P2S0 → P1`, the WEAK CONTINUITY of the
self through time and computes whether it is recoverable. Three levels of sameness are separated over a labelled
lift `destL` with plain reduct `plainOf destL`: PLAIN bisimilarity (trivial on any `SHNE` carrier by the collapse
engine `ws1_atomless_bisim`), the WEAK continuity (recoverability of a coarse continuity lift), and STRICT
identity (bisimilarity of the full rank lift). The verdict is COMPUTED: `SHAPE-DRAWN` — strict identity fails, the
single line is an import, and the weak continuity is recoverable on one carrier and an import on another, so its
recoverability is self-relative. The build is sorry-free, axiom-clean on the standard three (several payoffs on
fewer), gate-green, and names-clean. Namespace `P2S6`, `Cardinal.{0}`.**

## The imported machinery (reached transitively through `P2S5`, never imported directly)

- **The recoverability / import test** (`P1.Core`): `Recoverable destL := ∀ R, IsBisim (plainOf destL) R →
  IsBisimL destL R`; `ws4_recoverable_not_import` (a recoverable label lifts a plain bisimulation); the collapse
  engine `ws1_atomless_bisim` (any two `SHNE` states are plain-bisimilar); `LkObj`, `plainOf`, `pkSingle`.
- **The rank lift and the attention-distinction** (`P1.Reader` / `P2S0`): `rankLift dest lab`,
  `AttentionDistinguishes destL x y := (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x
  y)`.
- **The tick carrier** (`P2S1`): `TCar = Fin 7`, `attendsT`, `rankT`, `reifyT`, `kA`/`kB`/`kC`, `isTick`,
  `causal`, `ws1_tcar_SHNE`, `plainOf_rankLiftT`, `rankLiftT_val`; and the LINEARIZATION IMPORT
  `ws4_linearization_import` (for any `ord` distinguishing the concurrent pair `kA`,`kB`, the ordered lift is not
  `Recoverable`) and `ws4_causal_order_endogenous`.

## What Series 2.6 adds

Exactly two objects, built fresh: (1) the WEAK CONTINUITY, a continuity lift over the relating coarser than the
rank lift; (2) the reading of the single lived line as the self's linearization import. Two general recoverability
lemmas carry the fork:

- `plainOf_rankLift_gen : plainOf (rankLift dest lab) = dest`.
- **`const_first_recoverable (destL) (c) (∀ x, ∀ p ∈ (destL x).1, p.1 = c) : Recoverable destL`** — the RECOVERABLE
  horn: a lift all of whose edge-labels share one value lifts every plain bisimulation (first coordinates always
  match; second coordinates matched by the plain bisimulation).
- **`distinguishes_not_recoverable (destL) (x y) (AttentionDistinguishes destL x y) : ¬ Recoverable destL`** — the
  IMPORT horn (contrapositive of `ws4_recoverable_not_import`).

## The workstreams

**WS1 — strict identity fails across a tick (the trivial ground).** `succDep t u := isTick t ∧ isTick u ∧ t ∈
attendsT u` (the tick-successor, an alias of `causal`), witnessed on `(kA,kC)`, `(kB,kC)` (`ws1_succ_witnessed`).
`ws1_strict_fails (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA`: the reified
successor `kC` (`rankT kC = 2`) is plain-bisimilar to its constituent `kA` (`rankT kA = 1`) via the collapse
engine, yet no rank-bisimulation relates them (the edge `(⟨rankT kC⟩, kA)` forces `rankT kC = rankT kA`,
`decide`-false). Strict identity fails; the costume, walled out of the verdict.

**WS2 — the weak continuity (recoverable, or import?).** Two fresh carriers, both `SHNE`, over one continuity-lift
family:

- **Merged carrier `MCar = Fin 2`** (`m0 ⇄ m1`, `rankM = 0,1`): `mergeLift` tags every edge with the uniform mark
  `true`. `ws2_cont_recoverable : Recoverable (mergeLift hinf)` via `const_first_recoverable`. Non-vacuous: its
  plain reduct is the nonempty merged 2-cycle (`ws_mcar_SHNE`), so the collapse engine gives a rich plain
  bisimulation that the constant mark lifts.
- **Cut carrier `CCar = Bool`** (`c0 → c1` directional): `cutLift` tags `c0`'s edge with the active mark `c0`,
  `c1`'s with the passive mark `c1`; its plain reduct is the symmetric 2-cycle (both `SHNE`, `cut_SHNE`).
  `ws2_cont_is_import : ¬ Recoverable (cutLift hinf)` via `distinguishes_not_recoverable` (plain-bisimilar by the
  collapse engine; label-separated by `cutLift_label_sep`). The `P2S0.ws3_direction_not_recoverable` mechanism,
  built fresh.
- **`ws2_weaker_than_strict (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0 ∧
  Recoverable (mergeLift hinf)`** — over the ONE plain relating `outDest hinf attendsM`, the rank lift (strict
  identity) separates `m1`,`m0` while the continuity lift (weak) is recoverable: the weak continuity holds where
  strict fails. Constant mark `true`, not `rankM` relabelled: genuinely weaker, not a fiat (audit b).

**WS3 — the single line is the linearization import.** `ws3_line_is_import (hinf) : ∀ ord, ord kA ≠ ord kB → ¬
Recoverable (rankLift (outDest hinf attendsT) ord)`, reduced to `(ws4_linearization_import hinf ord h).2`. The
partial causal order is endogenous (`ws3_partial_order_endogenous = ws4_causal_order_endogenous`: witnessed,
rank-constrained, `kA`,`kB` incomparable); the total line over it is the import. `ws3_line_not_scalar : rankT kA =
rankT kB` shows the tower rank cannot linearize the concurrent pair, so the 1D line rests on the linearization
import, not on scalar rank (audit d).

**WS4 — the fork (the knot).** `ws4_woven_reachable`/`ws4_severed_reachable`/`ws4_carrier_relative` package both
horns (WOVEN and SEVERED reachable, neither forced — the continuity self-relative, audit a). Mortality companion,
on the directional knowing the lifts encode (`cutKnows`, `mergeKnows`): `ws4_cessation_relative (hinf) : (∃ x :
CCar, ∀ y, ¬ cutKnows y x) ∧ ¬ Recoverable (cutLift hinf)` — nothing knows `c0` (a moment nothing holds, MORTAL),
and the same asymmetric knowing is the import; `ws4_conservative_reachable : ∀ x : MCar, ∃ y, mergeKnows y x` —
every moment is known (CONSERVATIVE). One structure with the continuity lift (Phase D, finding C2-S1).

**WS5 — the verdict.** `inductive Outcome | woven | severed | shapeDrawn | partial'`. The verdict is a total
function of six booleans:

```
verdict strictFails lineIsImport wovenReachable severedReachable carrierDecided carrierWoven :=
  if !strictFails || !lineIsImport then partial'
  else if !(wovenReachable && severedReachable) then partial'
  else if !carrierDecided then shapeDrawn
  else if carrierWoven then woven
  else severed
```

- `ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn` (by `rfl`, computed).
- `ws5_verdict_discriminates` reaches all four outcomes (by `decide`).
- `ws5_flags_justified` earns the FOUR deciding flags from the WS1–WS4 headlines (`ws1_strict_fails`,
  `ws3_line_is_import`, `ws2_cont_recoverable`, `ws2_cont_is_import`), none hand-set. The two META-flags
  (`carrierDecided`, `carrierWoven`) are disclosed (finding C3-S1): `ws5_carrier_relative_verdict` grounds
  `carrierDecided = false` (both carriers reachable ⇒ no canonical carrier forced ⇒ `shapeDrawn`; `carrierWoven`
  irrelevant, the branch is not reached).
- Audit clauses (a)–(e): `ws5_audit_no_absolute` (continuity FOR a carrier, both reachable, the line the import),
  `ws5_audit_fork_genuine` (both reachable + weaker-than-strict), `ws5_audit_knot_not_strict` (`verdict true false
  … = partial'`, `verdict true true false false … = partial'`: strict alone never decides — the costume gate),
  `ws5_audit_line_is_import` (the linearization import + `rankT kA = rankT kB` + the endogenous partial order),
  `ws5_audit_names_not_terms : True` (the grep-certified placeholder).

## The computed verdict

`verdict true true true true false false = Outcome.shapeDrawn`, by `rfl`. Strict identity fails (WS1) and the
single line is an import (WS3) — the ground. A recoverable weak continuity exists (`ws2_cont_recoverable`, WOVEN)
and a non-recoverable one exists (`ws2_cont_is_import`, SEVERED), both reachable, neither forced
(`ws5_carrier_relative_verdict`), so the recoverability of the weak continuity is SELF-RELATIVE and undecidable
from within: **SHAPE-DRAWN**. Not by relabel: the pre-registered SEVERED is falsified by the merged carrier's
recoverable continuity, WOVEN by the cut carrier's import, and the verdict is the residue of the computation.

## Audit / hygiene

- **Sorry-free**; **axiom-clean**: every payoff reduces to `propext` / `Classical.choice` / `Quot.sound` or fewer
  (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_audit_names_not_terms` depend on NO axioms; `ws3_line_not_scalar`
  on `propext` only), certified by `P2S6.AxiomCheck`.
- **Gate-green**: `scripts/gate.sh` confirms `program-2/series-6` imports resolve only to `P2S5`/`P2S6`/Mathlib.
- **Names-not-terms**: no identifier is a forbidden content-word as a whole word; the interpretive words ("self,"
  "thread," "persistence," "life," "death," "time," "timeline") appear only in docstring prose. Renames from the
  charter's provisional targets are recorded in `charter-status.md` §2.
- **Blind reviews**: Phase C (design) and Phase F (code) each returned ZERO SERIOUS; two REAL design findings
  (C2-S1 mortality carrier, C3-S1 meta-flag disclosure) were Fixed at Phase D; all else COSMETIC.

## What is not done

No absolute persistence is asserted (continuity is FOR a carrier). No proof term names the interior of the self or
the content of continuity. Program 1's four permanent opens (the compass, the direction of convergence, the
differentiating act, the classification of out-of-image imports) stand untouched; Series 2.6 draws the
self-relativity of persistence and of lived time sharper and closes none.
