WS7 is the collector — it imports from ws2/ws4/ws5/ws6. The design was written against idealized upstream signatures that differ from what I actually built (e.g. `GradedWeakLawCoherence` doesn't thread `hQsmall`; `Bisim`/`.dest` differ; `Łuk`/`luk_card` don't exist). Let me confirm the actual signatures I must bind to.

This is the collector workstream, written against idealized upstream signatures that differ from what I built (no `hQsmall` threading in WS4; different `Bisim`/`Łuk`/`.dest`). I'll bind to the actual API. Let me build in two stages — first the collector core (static band, retro-validation, status types, assembly), then the dynamical spine. Stage 1:

Universe mismatch — `Luk n : Type 0` forces `luk_card_le` to work over `Cardinal.{0}`. Let me fix its signature.

Stage 1 (the collector core) compiles. Now stage 2 — the dynamical spine (`FlooredSimplex` with its metric/complete instances, invariance B0, the Banach fixed-point, and the Lipschitz bound). Let me add it.

One error left. Let me look at line 226.

`IsClosed.inter` needs an explicit intersection. Let me rewrite the conjunction set first.

Full WS7 compiles. Now import in Series03.lean, full build, and axiom check.

All seven WS7 theorems depend on only `[propext, Classical.choice, Quot.sound]` — no new axioms, sorry-free. Let me remove the temp block and commit.

Only header prose matches. Clean. Let me commit and push.

Done. Merged `main`, wrote `series-03/formal/ws7.lean`, imported it in `Series03.lean`, added `"ws7"` to the lakefile roots. **Full build compiles, sorry-free.**

**`#print axioms` result** — the bar is met across all seven checked theorems:
```
ws7_band_and_retro       : [propext, Classical.choice, Quot.sound]
ws7_static_band          : [propext, Classical.choice, Quot.sound]
ws7_retro_validate       : [propext, Classical.choice, Quot.sound]
ws7_attention_fixed_point: [propext, Classical.choice, Quot.sound]
mutationStep_maps_into   : [propext, Classical.choice, Quot.sound]
mutation_lipschitz       : [propext, Classical.choice, Quot.sound]
luk_card_le              : [propext, Classical.choice, Quot.sound]
```
**No new axioms.**

### What's proved (the WS7 v3 collector)
- **C1 static band (Discharged, witness form).** `ws7_static_band` — ≥2 distinct states, no maximal state, weak-pullback preservation, assembled from ws2/ws6.
- **C5 retro-validation (Discharged at one tuple).** `ws7_retro_validate` — at a concrete `(κ₀, Łₙ)` the WS2 characterization, no-maximal, WS6 split, and WS4 graded-law coherence all survive, with `#Łₙ ≤ κ₀` *proved* (`luk_card_le`) and re-exported as a typed premise (v3 fix 4).
- **Richness split (v3 fix 5).** `RichnessWitness` discharged; `GeneralBranching` held **open** (`RichnessGeneralStatus.open_iv_blocking`), never derived from the witness.
- **Scope boundary (v3 fix 6).** `CarrierScope.set_cofix_only` — WS7 makes no claim on the zero-object face / criterion (vi).
- **Dynamical spine (C3).** The full `FlooredSimplex` with `MetricSpace` + `CompleteSpace` instances, `mutationStep_maps_into` (B0 invariance), `mutation_lipschitz` (the `(1−μ)·L_R μ` bound in the sup metric), and `ws7_attention_fixed_point` (Banach via `ws5_attention_converges`). Convergence class **deferred to Lemma B** — whether the replicator-mutator actually contracts — left open, exactly as the design's terminal status states.
- **Assembly** `ws7_band_and_retro` (not `ws7_resolved`): dynamics `deferred`, richness-general `open_iv_blocking`, scope `set_cofix_only`.

### Honest adaptations, flagged in the header
The v3 design was written against an idealized upstream. I bound to the **actual** API: my WS4 `GradedWeakLawCoherence` doesn't thread `hQsmall` (so `ws7_retro_validate` carries it as a recorded/re-exported premise); the witness is `Luk n = Fin (n+1)`; `GeneralBranching` uses the real carrier API; and the `Łₙ` parts fix `κ₀ : Cardinal.{0}` (as `ws4_graded_coherence_Luk` does). All documented — consistent with the prior workstreams' discipline.

This completes the full WS1–WS7 Series-03 formalization on `claude/charter-design-lean-proof-k1l3zl`, every workstream sorry-free and axiom-free beyond the standard three.
