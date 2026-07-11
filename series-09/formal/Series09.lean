/-
`series-09/formal/Series09.lean`

Series 09 — **Self-reference is the engine.** The aggregator root.

The program's return to its founding thesis, and the response to Series 08's honest Partial: Series 08's
perspective spine COINCIDED with relational identity (`ws1_symmetric_states_bisimilar`), leaving open
whether no-god's-eye is separable from relational identity. Series 09 changes the engine from perspective
to self-reference.

The spine (WS1) is **Discharged as an Impossibility proved, INDEPENDENT of relational identity**: on a
hold-reflexive carrier (a hold ranges over the space of holds via `insp : Hold dest → HoldPred dest`),
no hold contains its own complete content — the self-total fixed-point equation `insp t = diag insp` has
no solution, by the Cantor/Lawvere diagonal `insp t t ↔ ¬ insp t t` (`ws1_no_self_total_hold`). The
proof term references ONLY `insp` and propositional logic; it contains NO `IsBisim`, NO
`BehaviorallyIdentified`, NO `ws1_symmetric_states_bisimilar` — the coincidence is NOT re-hit, certified
by `ws1_diagonal_not_bisim`. This is the repair Series 08 could not make: no-self-total-hold is the
separable second fact.

From the spine, three consequences from ONE position: plurality — the residue is free (not recoverable),
distinct from every hold, with NO second position in the premise (`ws2_residue_free`,
`ws2_residue_distinct`), repairing Series 08's circularity; forced dynamics — the re-diagonalization map,
serial because the residue always exists (`ws3_dynamics_forced`), on the ONE endogenous tower order
`prec` (`ws3_order_endogenous`), with (NL)+(NF) discharged and the imported index refuted; depth —
accumulated blind spots, each re-diagonalization opening a fresh one (`ws4_new_blind_spot`), reach as
trace. The central open law — monotonicity of the residue — is TESTED, not assumed: the kill condition
fires from re-diagonalization's OWN mechanism (holding a blind spot CLOSES it, `ws5_kill_condition`),
so strict monotonicity is Refuted and the bound is mere non-triviality; the "ever-deepening self" is
retracted (WS5/WS6). The verdict is `selfReferenceEstablished` (WS7), with the spine certified
diagonal-not-bisimulation.

This file is SELF-CONTAINED: every Series 08/07/04 lemma is transcribed into `Series09/wsNN.lean` and
re-namespaced `Series09.WSn` — nothing is imported from `series-08/`, `series-07/`, `series-04/`, or
`archive/`. `Series09.AxiomCheck` runs `#print axioms` over every headline. Sorry-free; axiom-clean
beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series09.ws1
import Series09.ws2
import Series09.ws3
import Series09.ws4
import Series09.ws5
import Series09.ws6
import Series09.ws7
