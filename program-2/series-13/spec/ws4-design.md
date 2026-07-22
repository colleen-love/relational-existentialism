# WS4 design — the fork (GRAVITATIONAL vs INERT) (the knot) (2.13)

**Prove the fork, each pole pre-registered, neither by fiat. `ws4_inert_reachable`: a configuration pair (same adjacency, different grain) where the imported distance is INVARIANT — geometry decoupled from the grain (which Series 2.4's distinctness of the two axes suggests is the case). `ws4_gravitational_reachable`: the GRAVITATIONAL pole of the grain-test is genuinely inhabited — there is a distance over configurations that DOES vary with the grain at fixed adjacency (the counterfactual foil) — so the test is two-sided and the imported distance's INERT is substantive, not vacuous. The costume watch: GRAVITATIONAL is inhabited only by the foil; the imported distance is INERT, never a grain-weighted distance defined to curve.**

## Imported / prior objects

- WS1-WS3: `adjDist`, `foilDist`, `grainDependent`, `cfgFlat`, `cfgBump`.

## Signatures

```lean
-- INERT REACHABLE (WS4). A configuration pair with the SAME adjacency and DIFFERENT grain on which the
-- imported distance is invariant — geometry decoupled from the grain. Reached by the imported distance.
theorem ws4_inert_reachable :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2
  ∧ (∀ x y, adjDist cfgFlat x y = adjDist cfgBump x y)

-- GRAVITATIONAL REACHABLE (WS4). The GRAVITATIONAL pole of the grain-test is genuinely inhabited: at fixed
-- adjacency, the grain-weighted foil DOES vary with the grain (`grainDependent foilDist cfgFlat cfgBump`),
-- so the test is two-sided and not hard-wired to INERT. The foil is NOT the imported distance (there is a
-- configuration and pair where they differ), so this inhabits the pole WITHOUT smuggling: the imported
-- distance is not among the grain-dependent distances (that is `ws4_inert_reachable` / `ws3_grain_test`).
theorem ws4_gravitational_reachable :
    cfgFlat.1 = cfgBump.1
  ∧ grainDependent foilDist cfgFlat cfgBump
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
```

## Proofs

- `ws4_inert_reachable`: `⟨rfl, (grains differ at p3), fun x y => rfl⟩`. Same adjacency `aChain`, so `adjDist cfgFlat = adjDist cfgBump = pathDist aChain` definitionally. Verified in the prototype.
- `ws4_gravitational_reachable`: `⟨rfl, ⟨p0, p3, by decide⟩, ⟨cfgBump, p0, p3, by decide⟩⟩`. `foilDist cfgFlat p0 p3 = 3 ≠ 4 = foilDist cfgBump p0 p3` (the grain bump at `p3` moves the foil); `foilDist cfgBump p0 p3 = 4 ≠ 3 = adjDist cfgBump p0 p3`. Verified.

## Strip test

Delete "GRAVITATIONAL," "INERT," "grain," "geometry," "gravity": `ws4_inert_reachable` reads `(same first component) ∧ (different second component) ∧ (adjDist agrees)` — a fact that a projection ignores the second component. `ws4_gravitational_reachable` reads `(same first component) ∧ (foilDist disagrees) ∧ (foilDist ≠ adjDist somewhere)` — a fact that a non-projection distinguishes the second component and is a different function. Both survive.

## Costume watch (audit b — the fork not by fiat)

- Both poles are genuinely reachable: INERT by the imported distance (`ws4_inert_reachable`), GRAVITATIONAL by the foil (`ws4_gravitational_reachable`). The verdict function (WS5) reaches both `inert` and `sourced` and `shapeDrawn`, so the machinery is not hard-wired.
- The grain genuinely changes between `cfgFlat` and `cfgBump` (`cfgFlat.2 ≠ cfgBump.2`), so the test's input is non-trivial — we really did pack more of the measure into the region and hold the connections fixed.
- The GRAVITATIONAL pole is inhabited by a distance PROVED distinct from the imported one, so nothing is smuggled: the honest content is that the grain-dependence test HAS a positive side (some distances gravitate), and the model's OWN distance is on the INERT side. That is the substantive NOT-RECOVERED, grounded in Series 2.4's proof that space and the measure are distinct axes.
