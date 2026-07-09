This is a category-theory-heavy design. Before writing, one issue I need to flag: the design's F3 theorem `ws6_empty_standpoint : (∀u, obs u) ∨ (∀u, ¬obs u)` is **false as stated** — since `PositionFree obs` holds vacuously for *every* `obs` (via `endo_eq_id`), the disjunction would force every predicate to be constant, which fails for any non-constant `obs` on a ≥2-element carrier. The design itself says F3 is "vacuous" and criterion (vi) is *not* discharged; but the literal signature it wrote is unprovable. I'll realize the honest vacuity witness (`∀ obs, PositionFree obs`, which is true and is exactly the "no substantive constraint" content) and document the defect — mirroring how I handled the WS4 pentagon erratum and WS5's missing `Nonempty`.

Let me verify my read of `endo_eq_id` and the upstream names, then write.

Signatures confirmed. Now let me write `ws6.lean`.

Several issues. The key one is that `instD` as a plain field isn't found by typeclass resolution for later fields — it needs to be an instance-implicit field `[instD : ...]`. Let me look at the cascade points and fix.

The error line numbers don't match my mental map. Let me look at the actual error locations.

The root issue is `instD` as a plain field isn't found by typeclass resolution. Let me make it instance-implicit, and fix the cardinal lemma name.

The bundled category-instance field causes TC diamonds. The robust fix is to make the source category `D` and its `[Category D]` explicit *parameters* rather than bundled fields — a cleaner equivalent. Let me restructure.

Let me look at the assembly and relative-bottom errors.

Let me fix the remaining issues: the `distinct` proof, `eq_of_tgt`'s implicit `Y`, the `standpoint_vacuous` closing, and the field's `obs` type annotation.

`ULift.up.inj` isn't the right name. Let me coerce through the defeq to `ULift Bool` and use `simp`.

ws6 compiles. Now import in Series3.lean, full build, and axiom check.

All theorems axiom-clean (`ws6_poles_split` doesn't even need `propext`). Let me remove the temp checks and commit.

Only header prose matches. Clean. Let me commit and push.

Done. Merged `main`, wrote `series-3/formal/ws6.lean`, imported it in `Series3.lean`, added `"ws6"` to the lakefile roots. **Full build compiles, sorry-free.**

**`#print axioms` result** — the bar is met:
```
ws6_split_and_no_maximal  : [propext, Classical.choice, Quot.sound]
ws6_poles_split           : [Classical.choice, Quot.sound]   (no propext)
ws6_no_maximal            : [propext, Classical.choice, Quot.sound]
ws6_embedding_nonvacuous  : [propext, Classical.choice, Quot.sound]
ws6_standpoint_vacuous    : [propext, Classical.choice, Quot.sound]
ws6_relative_bottom       : [propext, Classical.choice, Quot.sound]
```
**No new axioms** beyond Mathlib's standard three.

### What's proved (the design's charter-authorized split)
- **F4 — pole-coincidence split (Impossibility-proved, scoped).** `ws6_poles_split`: a faithful carrier-embedding cannot land entirely in zero objects (the "atom = everything" trivialization is fatal), via **terminality**. `ws6_embedding_nonvacuous` certifies the hypothesis is inhabited (a hand-rolled single-object non-zero category) and that `coincide` carries the weight. `ws6_no_faithful_zero_host` is the named open obligation (D2).
- **F2 — no maximal element (Discharged, by κ-fiat).** `ws6_no_maximal`, discharging WS1's declared hand-off.
- **F3 — empty standpoint (Open/vacuous → criterion (vi) shortfall).** `ws6_standpoint_vacuous`.
- **F5 — relative bottom (Partial-by-construction).** `ws6_relative_bottom`.
- **Assembly** `ws6_split_and_no_maximal` (not `ws6_resolved`), keeping criterion (vi) out of the discharged bundle.

### Two honest deviations, flagged in the header
1. **The design's F3 signature is false as stated.** `ws6_empty_standpoint : (∀u,obs u) ∨ (∀u,¬obs u)` cannot be proved — since `endo_eq_id` makes `PositionFree obs` hold vacuously for *every* `obs`, that disjunction would force every predicate to be constant, refuted by any non-constant `obs`. The design's own prose says F3 is "vacuous" and (vi) is not discharged; the literal disjunction over-shoots into an untruth. I realized the honest vacuity witness `∀ obs, PositionFree obs` — true, and exactly the "no substantive standpoint constraint" content that leaves (vi) Open.
2. **A faithful-formalization choice:** `FaithfulCarrierEmbedding` takes the source category `D` and its `[Category D]` as explicit parameters rather than a bundled instance field, to avoid a typeclass diamond — an equivalent phrasing, noted in the docstring.

Both mirror the prior workstreams' discipline (WS4 pentagon erratum, WS5 `Nonempty`). Pushed to `claude/charter-design-lean-proof-k1l3zl`. WS6 lands as **Partial** — precisely the terminal class the charter §8.1 pre-registers.
