/-
`series-10/formal/Series10.lean`

Series 10 — **Reification is the generator.** The aggregator root.

The program's founding equation `Ω ≅ F(Ω)` read as a generator, and the response to Series 09's honest
limitation: on a FIXED carrier the free residue could only MOVE (a moving hole is still one hole). Series
10 lets the free residue REIFY into a new relatum via `reify : PkObj κ Ω → Ω` (a section of `dest`, the
forward map of `Ω ≅ F(Ω)`), so the carrier GROWS.

The spine (WS1) is **productive blindness, Discharged**: the reified self-relation is FREE, and
recoverability would reconstruct a self-total hold (`ws1_free_reification` = `ws2_residue_is_import`
lifted), so the growth is genuine BECAUSE self-reference cannot close (`ws1_no_self_total_hold`). The
payoff (WS2) is **genuine growth at the labelled level**: the reified relatum's free label survives the
bisimulation quotient (`ws2_growth_strict` = `ws4_label_survives_quotient`), landing on the free-import
horn (`ws2_growth_is_free_label`), so the carrier does not label-bisimulation-embed into the prior — the
break of the Series 07 collapse Series 09's bisimulation-invariant moving hole could not make; the
plain-level collapse persists (`ws2_plain_collapse_persists`) and is disclosed honestly.

The tower (WS3) is genuine carrier growth (`towerN`/`reifyStep`, not an external `List`), preserving
`SHNE` (`ws3_reify_preserves_SHNE`, no leaf), with the ONE endogenous order `prec` (from reification
sequences, `ws3_order_endogenous`) and the imported-ordinal branch refuted. The structural heart (WS4):
**CLOSE is forbidden by the diagonal** (`ws4_close_forbidden`, a totality-relatum is a self-total hold),
an Impossibility; the dichotomy is exhaustive. The central open (WS5): the fold is TESTED — the
per-step / reifiable-pattern fold is Discharged-on-scaffold (`ws5_fold_on_scaffold`, distributed
reflexivity, all large κ), but the full crown (every free residue folded — a residue is a `HoldPred`, not
a κ-bounded pattern) and κ-removal are open, so the verdict is **Partial** with FATAL pre-registered. The
verdict (WS7) is `reificationEstablished`, with the two promoted checks — bookkeeping (growth not-embed,
not a `List`) and κ-by-fiat (fold reflexivity, all large κ) — the spine of the audit.

This file is SELF-CONTAINED: every Series 09/08/07/04 lemma is transcribed into `Series10/wsNN.lean` and
re-namespaced `Series10.WSn` — nothing is imported from `series-09/`, `series-08/`, `series-07/`,
`series-04/`, or `archive/`. `Series10.AxiomCheck` runs `#print axioms` over every headline. Sorry-free;
axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws1
import Series10.ws2
import Series10.ws3
import Series10.ws4
import Series10.ws5
import Series10.ws6
import Series10.ws7
