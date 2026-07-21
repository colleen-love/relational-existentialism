# Series 2.7 — Technical summary

**THE LEDGER, the physics capstone. Series 2.7 constructs a self-relative measure of distinction `Q := rankM` (the
reification rank) FRESH on the imported carrier, and proves: the measure is non-trivial with its value-differences
genuine imports (WS1); a reification-tick preserves it within the plain-bisimulation quotient — the self's sight —
because the reified relatum is plain-bisimilar to its constituent (WS2, conserved-relative, the global failing); every
change in the measure is an import, resting on Series 07 (WS3); and at the diagonal, the free-lunch crux reaches both
FREE-LUNCH and CONSERVED, neither forced (WS4). The verdict is computed (WS5): CONSERVED-RELATIVE. Namespace `P2S7`,
importing `P2S6` only. Sorry-free, axiom-clean on the standard three, gate-green, names grep clean. Blind design
review (Phase C) and blind code review (Phase F) each returned zero SERIOUS at their final pass.**

## The imported machinery (reached transitively through `P2S6`, never imported directly)

| Piece | Origin (transitive) |
|---|---|
| The recoverability / import test: `Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `ws4_recoverable_not_import`, `ws1_atomless_bisim` (collapse engine), `LkObj`, `PkObj`, `SHNE` | `P1.Core` / `P2S0` |
| The rank-labelled lift and the attention-distinction: `rankLift`, `AttentionDistinguishes` | `P1.Reader` / `P2S0` |
| The P1 diagonal (the free-lunch test object): `Hold`, `HoldPred`, `diag`, `residue`, `ResidueRecoverable`, `ws2_residue_free`, `ws1_coincidence_not_identity_witness` | `P1.Core` |
| The tick (reification-under-attention), `outDest`, `finsetToPk` | `P2S1` / `P2S0` |

## What Series 2.7 adds

Exactly one object, built fresh and de-risked on paper first: the **measure `Q := rankM`** on the witness carrier
`MCar = Fin 4` (two base relata `e0`, `e0'` at rank 0; a reified relatum `e1 = reifyM {e0}` at rank 1; a higher
reified relatum `e2 = reifyM {e1}` at rank 2), together with the measure lift `destML = rankLift (outDest attendsM)
rankM`. `rankM` is defined structurally (`if x = e1 then 1 else if x = e2 then 2 else 0`), with no reference to its
conservation or rise. The WS4 fork uses a decidable bookkeeping skeleton (`Qc B = B.card`, `diagStep B d = insert d
B`) DISCLOSED as a skeleton and conjoined with — not derived from — the genuine residue facts.

## The workstreams

- **WS1 — the measure, non-trivial (`ws1_rank_nontrivial`).** `rankM e1 = 1 ≠ 0 = rankM e0`, `∃ x y, rankM x ≠
  rankM y` (not constant), and the difference is a genuine import: `AttentionDistinguishes (destML) e1 e0` — `e1`
  plain-bisimilar to `e0` (the collapse engine, both `SHNE`) yet rank-lift-separated (`rankM_sep_general`, the
  `ws2_many_general` mechanism). So a `Q`-difference is a `¬ Recoverable` distinction; the measure is genuine and
  not rigged.
- **WS2 — the tick conserves `Q` in-sight (`ws2_tick_conserves`).** The pointwise section (`attendsM (reifyM {e0}) =
  {e0}`, `reifyM {e0} = e1`) plus the plain-bisimilarity `∃ R, IsBisim (plainOf destML) R ∧ R (reifyM {e0}) e0`
  (the collapse engine). The reified product is plain-indistinguishable from its constituent, so no in-sight measure
  separates them: the tick adds no in-sight distinction. The label rank does change (`= 1 ≠ 0`, WS1) — that change is
  the import (WS3), invisible in-sight. Local conservation, the global failing.
- **WS3 — the import is the sole source (`ws3_change_is_source`, `ws3_source_nonvacuous`).** `∀ x y, rankM x ≠ rankM
  y → AttentionDistinguishes (destML) x y` (every `Q`-change over the plain quotient is an import) and `¬ Recoverable
  (destML)` (the whole measure lift is an import) via `ws4_recoverable_not_import` (Series 07). The general
  separation `rankM_sep_general` (an outgoing edge forces the label coordinates equal under a label-bisim) supplies
  the label-apart half; the collapse engine supplies the plain-alike half. The source is non-vacuous (`e1` vs `e0`).
- **WS4 — the free-lunch crux (`ws4_free_lunch_reachable`, `ws4_conserved_reachable`, `ws4_crux_both_reachable`).**
  FREE-LUNCH reachable: from one self-inspecting position `h0`, the diagonal yields two DISTINCT free residues
  (`ws1_coincidence_not_identity_witness`, `residue insp₁ ≠ residue insp₂`, each `¬ ResidueRecoverable` by
  `ws2_residue_free`), with no import crossing — self-reference manufactures distinct non-recoverable distinctions
  from within (count skeleton: `Qc` rises). CONSERVED reachable: the residue is still free universally
  (`ws2_residue_free`) but relocates onto an already-latent slot (count skeleton: `Qc` holds). Both reachable,
  neither forced — the crux is relative. The knot rests on the diagonal (the residue), not import-ness.

## The computed verdict

`verdict : Bool⁶ → Outcome` with `Outcome = {conservedRel, monotoneOnly, freeLunch, global, disconnected, partial'}`.
`ws5_verdict_eq : verdict true true true true true false = Outcome.conservedRel` by `rfl`. `ws5_verdict_discriminates`
reaches all six constructors by `decide`. `ws5_flags_justified` earns the deciding flags from the WS1–WS4 payoffs
(`ws1_rank_nontrivial`, `ws2_tick_conserves`, `ws3_change_is_source`, `ws4_free_lunch_reachable`,
`ws4_conserved_reachable`); the meta-flag `globalForced` is honestly `false`. **The computed verdict is
CONSERVED-RELATIVE**: a non-trivial measure, conserved in-sight, sourced only by the import, the free-lunch crux open
both ways, no global conservation asserted.

## Audit / hygiene

- **(a) no global conservation** (`ws5_audit_no_global`): conservation is FOR the in-sight plain-bisim relating,
  changed at the import; the label rank does change; `global` is returned only under `globalForced = true` (false).
- **(b) the fork not by fiat** (`ws5_audit_fork_genuine`): both fork sides reachable, the measure non-trivial.
- **(c) the knot is the diagonal-as-source, not import-ness** (`ws5_audit_knot_is_diagonal`): import-ness alone
  (`changeIsSource = true`, `freeLunchReachable = false`) yields `partial'`; the WS4 payoffs rest on `ws2_residue_free`.
- **(d) change is an import** (`ws5_audit_change_is_source`): `= ws3_change_is_source`, resting on Series 07.
- **(e) names-not-terms** (`ws5_audit_names_not_terms : True`, the disclosed placeholder): the §6 grep is clean —
  no identifier embeds a forbidden content-word; hits are docstring prose and the Lean `import` keyword only.
- **Build:** `lake build P2S7 P2S7.AxiomCheck` compiles; sorry-free; axioms are a subset of `propext` /
  `Classical.choice` / `Quot.sound` (`ws4_crux_both_reachable` uses only `propext` / `Quot.sound`; the three
  `verdict`/`decide` theorems use none); gate green (`(P2S6|P2S7)` closure).

## What is not done (by design)

No global conservation is asserted (the phase thesis; the global fails, GR-style). The free-lunch crux is not
resolved — both readings are reachable and the direction is self-relative, undecidable from within. The measure is a
measure FOR a self, in-sight; the import that sources it stays quantified, never named. Program 1's four permanent
opens are untouched: Series 2.7 adds none and closes none. It draws the self-relativity of the ledger, and the
failure of the global, sharpest.
