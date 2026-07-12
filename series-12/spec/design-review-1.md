# WS4 Purchase-Witness, Design Instructions (do this BEFORE the Phase C build)

**Why this exists.** The WS4 design (`ws4-design.md`) correctly locates the series' one uncertain obligation and correctly fences it off from the two fake answers (the `labelLoop` re-hit; no-mechanism-by-collapse). But it does NOT discharge it. In `ws4_with_A_plurality`, the two hard facts

- `hmem : y ∈ (A.att (reify s)).reads`
- `hpurchase : ¬ ∃ R, IsBisimL (labelledBy dest A.dir) R ∧ R (reify s) y`

are taken as HYPOTHESES. The theorem is a one-line unfolding of `RealFor`; it proves "IF purchase THEN RealFor," which is trivially true and says nothing about whether purchase is ever satisfiable. The M1 discharge in `ws2-design.md` (`ws2_exogenous`) likewise takes purchase as a hypothesis and defers it to WS4. So the positive side of the whole series currently rests on an assumption neither workstream constructs.

This task closes that hole. Produce a design doc, `ws4-witness-design.md`, for a CONCRETE model that discharges `hpurchase` with NO purchase-like hypothesis, and that self-classifies the `dir` it had to use. This design must exist and be reviewed before any Lean is built for WS4.

## Where it goes

- Write the design at `series-12/spec/ws4-witness-design.md`.
- It is a new WS4 sub-artifact; register it in `series-12/spec/README.md` §6 (cross-workstream triage) as `WS4-witness`, owned by WS4, consumed by WS2 (M1 discharge) and WS5 (verdict).
- The Lean it specifies will land in `series-12/formal/Series12/ws4_witness.lean` at build time (Phase C), imported by `ws4.lean`. Do NOT build it now; design only.

## What the design must contain

### 1. A concrete carrier, reification section, and direction, all explicit, no parameters left open

Fix a specific `X`, a specific `dest : X → PkObj κ X` that is atomless (every state `SHNE`), a specific `reify : PkObj κ X → X` with `IsReify dest reify`, a specific `s : PkObj κ X` and `y : X`, and a specific direction `dir : X → L`. Nothing here may be a hypothesis; every object is a closed term. The design gives the definitions and the paper argument that:

- `dest` is atomless: `∀ x, SHNE dest x` (or at least `SHNE` at every state reached from `reify s` and `y`).
- `IsReify dest reify` holds (`∀ s, dest (reify s) = s`), and `reify s` is a genuine tower relatum: `s.1 ≠ ∅`, `∀ z ∈ s.1, SHNE dest z`, so `ws3_reify_preserves_SHNE` applies and `reify s` is `SHNE`.
- Consequently `reify s` and `y` ARE plain-bisimilar (`ws2_reify_bisim_embeds` applies). This is REQUIRED, not avoided: if the design picks a `dest` where `reify s` and `y` are already plain-distinct, it has smuggled in an atom and is disqualified. The witness must live on a carrier where the plain quotient genuinely merges them, and the label alone separates them.

### 2. The discharge of `hpurchase`, as a closed theorem

State and give the full proof strategy (to the point a build can follow it mechanically) for:

```lean
theorem ws4_purchase_witness :
    ¬ ∃ R, IsBisimL (labelledBy dest dir) R ∧ R (reify s) y
```

with `dest`, `dir`, `reify`, `s`, `y` the CONCRETE terms of §1, NO `hpurchase` hypothesis, NO purchase-like antecedent. Recall the definitions this must engage:
- `labelledBy dest dir x = PkMap (fun w => (dir w, w)) (dest x)`, so each successor `w` of `x` carries label `dir w`.
- `IsBisimL` requires matched successors to have EQUAL labels (`p.1 = q.1`) AND related targets.
- The proof obligation is therefore: any candidate label-bisimulation `R` relating `reify s` and `y` must match a successor of one against a successor of the other with equal `dir`-labels, and the design must show this fails, some successor of `reify s` carries a `dir`-label no successor of `y` can match (or vice versa).

The design must show the proof does NOT secretly reduce to `ws4_label_survives_quotient` on `labelLoop` (that theorem is about the fixed two-state `⟨true⟩`/`⟨false⟩` coalgebra and mentions no tower object; reusing its shape on two ad-hoc states with `reify`/`reifyStep` absent is the forbidden re-hit). `reify`, and the fact that `reify s`'s successors are `s.1` (via `IsReify`), MUST be load-bearing in the proof.

### 3. Also discharge `hmem` concretely

Give the concrete `A.att (reify s)` (a `FiniteAttention (labelledBy dest dir)`) with `y ∈ reads`, `reads.Finite`, `focus = reify s`, and `grounded` (every read state is `SReaches`-reachable from `reify s`). Show `y` is genuinely reachable from `reify s` in the plain structure, so `hmem` is honestly satisfiable, not just posited. If `y` is NOT reachable from `reify s`, the whole `RealFor` witness is ill-typed against `grounded`; the design must confirm reachability or pick a `y` that is reached.

### 4. THE SELF-CLASSIFICATION (the point of the whole exercise)

Having built `dir`, the design must answer, explicitly and in prose, ONE question and defend the answer:

> **Is this `dir` genuine tower-purchase, or a relabeled two-element tag (the `labelLoop` failure in disguise)?**

Give the criterion sharply. `dir` is genuine tower-purchase iff its distinguishing power comes from the REIFICATION STRUCTURE, e.g. `dir w` depends on `w`'s position in the `reifyStep`/`towerN` order (`prec`), or on a reification-invariant property that `reify s` has and `y` lacks, so that the SAME `dir` discipline distinguishes reified relata from their pre-images GENERALLY, across the tower, not just at one hand-picked pair. `dir` is a relabeled tag iff it distinguishes `reify s` from `y` only because it literally hard-codes "is this the element `reify s`?" (a two-valued indicator on one distinguished point), which is `labelLoop` with `X` renamed and carries no tower content.

The design must state which one its `dir` is, and:

- **If genuine tower-purchase:** show the `dir` generalizes, state the general form (`ws4_purchase_general`: for any `reify s` and any prior `y` it bisim-embeds with, `dir` built from the tower order separates them), and confirm `reify`/`reifyStep`/`prec` are load-bearing in the general statement. This is the `mechanismExists` witness; WS4's `ws4_with_A_plurality` then instantiates against it with `hpurchase` DISCHARGED, not assumed.
- **If it collapses to a two-element tag:** say so plainly. Then the honest terminus is `noMechanism`, the import has no tower-purchase, only point-tagging purchase, which is the `labelLoop` gadget relabeled and is the forbidden re-hit if reported as success. The design routes to `ws4_const_dir_no_purchase` / the no-mechanism verdict, and states the precise obstruction: every `dir` that separates the pair separates it as a bare indicator on one point, carrying no reification content. Report it as the tested no-purchase claim (charter §6.2), NEVER as the Series 07 collapse.

Do not decide this in advance. Build the concrete `dir`, attempt both the specific discharge (§2) and the generalization (§4), and let which one succeeds determine the verdict. The failure to generalize is itself a result and must be reported, not hidden.

### 5. Outcome classes for the witness design

- **Purchase-witnessed (tower-genuine):** §2 discharges with no hypothesis AND §4 generalizes with `prec`/`reifyStep` load-bearing. Routes to `mechanismExists`. This is the argued-expected outcome.
- **Purchase-witnessed (point-tag only):** §2 discharges but §4 shows the `dir` is a bare indicator that does not generalize. Routes to `noMechanism` (tested no tower-purchase), reported honestly, NOT laundered as success and NOT a re-derivation of the collapse.
- **Purchase-refuted:** §2 cannot be discharged on any atomless carrier where the pair genuinely bisim-embeds (every label that separates them forces a plain-distinction, i.e. re-introduces an atom). Routes to `noMechanism`, and is the sharpest possible finding, it would mean the import cannot separate a genuinely-merged pair at all.

### 6. The strip test on the witness

`ws4_purchase_witness` must strip (deleting "mechanism/import/direction/attention/purchase/tower") to a bare labelled-bisimulation fact on a concrete coalgebra: "for this explicit `dest`/`dir`, no `IsBisimL` relation relates these two explicit plain-bisimilar states." If it strips to `ws4_label_survives_quotient` (the two-Boolean fact), it is the re-hit and is flagged SERIOUS.

## The discipline for this task specifically

1. **No hypothesis may carry the purchase.** The deliverable's headline theorem has `dest`, `dir`, `reify`, `s`, `y` as closed terms and no purchase-like antecedent. If the executor finds itself writing `(hpurchase : …)` again, it has reproduced the hole, not filled it.
2. **The pair MUST plain-bisim-embed.** Confirm `ws2_reify_bisim_embeds` applies to the chosen `reify s`, `y`. A carrier where they are already plain-distinct is disqualified (a hidden atom).
3. **`reify` load-bearing.** `reify`, `IsReify`, and the reification order must appear in the discharge and (if claimed) the generalization. A discharge that never mentions the tower is the `labelLoop` re-hit.
4. **Self-classify honestly (§4).** The design's job is not to reach `mechanismExists`; it is to determine, on a concrete model, whether the necessary import has genuine tower-purchase or only point-tag purchase, and to report which. A well-defended `noMechanism` here is a first-class success and the honest close of the program if that is what the math yields.
5. **If it will not go through, report the precise obstruction** in `charter-status.md` routed to WS4, and do not build past it into the assembled `ws4.lean`.

## Deliverable

`series-12/spec/ws4-witness-design.md`: the concrete carrier/`reify`/`dir`/`s`/`y` (§1), the closed `ws4_purchase_witness` discharge with full strategy (§2), the concrete `att` discharging `hmem` (§3), the self-classification with either the generalization or the honest no-purchase obstruction (§4), outcome classes (§5), strip test (§6). Registered in `README.md` §6 as `WS4-witness`. No Lean built yet; this is the design that tells us, before Phase C, whether the positive terminus is real.
