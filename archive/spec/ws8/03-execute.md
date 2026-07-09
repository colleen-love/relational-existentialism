This is a large multi-obligation "holes" workstream. Before writing, I need to check several design goals against my *actual* upstream definitions — a few look subtly false as literally stated (a recurring pattern). Let me pull the exact upstream signatures.

My analysis is confirmed: `WQRel` mirrors `PkRel` exactly, so `PkRel_le_comp` ports directly — meaning **`WQPreservesWeakPullback` is provable positively**, and the design's A5 impossibility is false against these definitions. Let me read the exact ws4 defs to port.

Confirmed. This reveals a significant finding: my `WQRel` is the sup-based Barr lifting (identical to `PkRel`), so **`WQPreservesWeakPullback` is provable positively** by porting `PkRel_le_comp` — the design's A5 impossibility is false against these definitions (it assumed a ⊗-coupled lifting the formalization doesn't use). Several other design goals (D2's set-inequality form) are also subtly false. I'll deliver the honest true versions. Let me write ws8.lean.

ws8 compiled first try. Now import in Series3.lean, full build, and axiom check.

All six WS8 theorems depend on only `[propext, Classical.choice, Quot.sound]` — no new axioms, sorry-free. Let me remove the temp block and commit.

Only header prose matches. Clean. Let me commit and push.

Done. Merged `main`, wrote `series-3/formal/ws8.lean`, imported it in `Series3.lean`, added `"ws8"` to the lakefile roots. **Full build compiles, sorry-free.**

**`#print axioms` result** — the bar is met across all six theorems:
```
wq_preserves_weak_pullback   : [propext, Classical.choice, Quot.sound]
ws3_weak_law_canonical       : [propext, Classical.choice, Quot.sound]
ws7_general_branching_false  : [propext, Classical.choice, Quot.sound]
ws7_iv_branching             : [propext, Classical.choice, Quot.sound]
ws6_no_global_observer       : [propext, Classical.choice, Quot.sound]
ws6_substantive_standpoints  : [propext, Classical.choice, Quot.sound]
```
**No new axioms.**

### What's proved (holes A–E)
- **A (positive — discharges a WS4 open obligation).** `wq_preserves_weak_pullback` proves `WQPreservesWeakPullback Q κ` for *every* `Q`, by porting `ws2.PkRel_le_comp` with `WQMap`.
- **B2.** `ws3_weak_law_canonical` — the WS3 Egli–Milner weak law is the **unique** (`∃!`) map satisfying the unit + multiplication laws, via `destEquiv` injectivity (upgrades WS3's `∃`).
- **D1-neg + D2.** `ws7_general_branching_false` (the universal floor is unachievable — empty state) and `ws7_iv_branching` (the honest `alg`-relative floor).
- **E2 + E1.** `ws6_no_global_observer` (no view from nowhere) and `Standpoint`/`ws6_substantive_standpoints` (positioned views with content).

### Three honest corrections, flagged in the header
Working against the *actual* formalized definitions surfaced several design signatures that are false as literally stated:
1. **A5's impossibility (`¬ WQPreservesWeakPullback`) is false** — my WS4 `WQRel` is the sup-based Barr lifting (identical to `PkRel`), with no ⊗-coupling of leg weights, so preservation simply holds. The design's impossibility targeted a ⊗-weighted composition the formalization never used. I proved the positive instead — a stronger, honest outcome that also **discharges the WS4 Layer-C obligation I'd earlier left open**.
2. **D2's `str x₁ ≠ str x₂` hypothesis is insufficient** (a singleton-successor state and the empty state have distinct `str` but union to out-degree 1). I proved the true point-based form.
3. **C is deferred** — the design itself calls it the one obligation with no upstream lever and quarantines the replicator-Jacobian analytic node; no `sorry` stands in for it, and the `ws7` Banach scaffold is ready to consume any future contraction proof.

All consistent with the WS4 `pentagon`-erratum / WS6 F3 discipline established earlier. Pushed to `claude/charter-design-lean-proof-k1l3zl`.
