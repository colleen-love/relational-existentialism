# Relational Existentialism — Series 09: Technical Status Summary

*A machine-checked proof that self-reference cannot close — the self-total hold is a denied diagonal fixed point, independent of relational identity — and the finding that the residue this opens is free, generates plurality from one position, forces dynamics, and does not grow monotonically.*

## 1. The headline

> **On a hold-reflexive carrier, no hold contains its own complete content: the self-total hold is the fixed point a Cantor/Lawvere diagonal denies, and its non-existence is independent of relational identity. The residue this leaves is free, distinct from one position, and is the first difference.**

The spine is `ws1_no_self_total_hold`: on a carrier where a hold can range over holds, the self-total fixed-point equation `insp t = diag insp` has no solution, by the diagonal `insp t t ↔ ¬ insp t t`. This is the repair of Series 08's Partial: Series 08's no-god's-eye collapse *coincided* with relational identity (`ws1_symmetric_states_bisimilar` — the positionless node's states are all bisimilar, so the collapse was not a separate fact). Series 09's spine derives its contradiction from the totality's own defining equation, not from a bisimulation, so no-self-total-hold is the separable second fact Series 08's third review named as the open question.

## 2. Verification status

- **`sorry`-free:** no proof-position `sorry`, `admit`, `native_decide`, `sorryAx`, `opaque`, `unsafe`, or custom `axiom` anywhere in `ws1`–`ws7` (grep-clean).
- **No custom axioms:** every headline theorem rests only on Mathlib's standard three — `propext`, `Classical.choice`, `Quot.sound`.
- **The single most important check, machine-run:** `ws1_no_self_total_hold`'s proof term is a Cantor/Lawvere diagonal (`insp t t ↔ ¬ insp t t`), containing no `IsBisim`, no `BehaviorallyIdentified`, no `ws1_symmetric_states_bisimilar`. The coincidence rule is satisfied: the spine is independent of relational identity, verified at the term level. `ws1_diagonal_not_bisim` carries the independence; `ws7_coincidence_check` contrasts the spine (denies a fixed point) with the symmetric-states bisimulation (produces one) in a single statement.
- **In-build verification:** `Series09/AxiomCheck.lean` imports the whole build and runs `#print axioms` on every headline across WS1–WS7. Committed at [`spec/axiom-check-log.md`](./spec/axiom-check-log.md) against Lean 4 v4.15.0 / Mathlib v4.15.0. The whole package (Series 07 + 09) builds clean, sorry-free, warning-free, axiom-clean.
- **Closure:** `scripts/gate.sh` confirms `series-09/formal/` imports resolve only to Series 09's own roots plus Mathlib — nothing transcribed is imported across series.

## 3. What is proved

- **The spine (Impossibility, independent).** `ws1_no_self_total_hold`. The self-total hold is a denied diagonal fixed point. Twin carrier hazards guarded: the carrier is genuinely hold-reflexive (a hold ranges over holds, not a mere self-loop `dest x ∋ x` which Series 08 showed collapses by coincidence — `ws1_unrestricted_carrier_inconsistent` handles the Russell-too-strong direction).
- **Plurality from one position.** `ws2_residue_free` / `ws2_residue_distinct`: the residue is distinct and free (not recoverable), a corollary of the spine, with no second position in the premise — the direct repair of Series 08's circularity (`x↾(x,y) ≠ y↾(y,x)` had needed `x ≠ y` assumed).
- **Forced dynamics.** `ws3_dynamics_forced`: no reachable stage is Complete, forced from the spine, on the endogenous order `prec`.
- **Depth / layering.** `ws4_residue_moves`: on the strengthened re-inspection map (which holds the *whole* prior residue, not a point-edit), re-inspection closes the prior residue; `ws4_depth_is_tower` for the accumulation.
- **Monotonicity, settled Partial.** `ws5_retention_refuted` / `ws5_kill_condition`: the kill condition fires from re-diagonalization's own mechanism — holding a blind spot at `h₀` flips the diagonal there, so re-diagonalizing *closes* the blind spot it holds. Strict monotonicity Refuted; bound is mere non-triviality; the ever-deepening self retracted (`ws6_monotonicity_retracted`). Verdict datum `ws5_monotonicity_verdict = .partialV`, justified by theorems.

## 4. The verdict

`ws7_verdict = Series09Verdict.selfReferenceEstablished` by `rfl` on the discharged `Audit`, whose flagship field `diagonalNotBisim` carries the spine's independence, so the verdict cannot be hand-set. `coincident` / `monismStands` / `Circular` are live but untriggered — the only route to them is a failed audit.

## 5. Scope and honest limits

- The universal forms of layering and monotonicity are defended theses floored by the mechanized core (WS6), as every prior series' "forced answer" was.
- The spine is proved on a hold-reflexive witness; the fully universal "every hold-reflexive carrier admits the diagonal" is the expected un-rangeable-quantifier Partial. One non-coincident diagonal instance is enough to show no-god's-eye is separable from relational identity, which is the repair.
- The epistemic-vs-constitutive status of the residue's persistence is left open by design (the atom-or-will door, inherited).

## 6. The seed for Series 10

Series 09's residue is bisimulation-invariant: it *moves* on a fixed field but its shape is the same everywhere, so two towers relating alike are still collapsible by the Series 07 engine. A moving hole is still one hole. Making the free residue into a genuine, proliferating *many* — by reifying it into a new relatum that grows the carrier — is the question Series 09 hands to Series 10.
