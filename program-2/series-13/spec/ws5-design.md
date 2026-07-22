# WS5 design — the verdict and the audit folded in (2.13)

**The verdict is COMPUTED, never hand-set: INERT (WS1 a non-constant grain and a non-trivial distance, WS2 the distance a function of the adjacency, WS3 the imported distance invariant under grain-change and no by-hand coupling, WS4 INERT reached by the imported distance and GRAVITATIONAL inhabited only by the foil — geometry decoupled from the grain, no gravity, the NOT-RECOVERED grounded in Series 2.4's DISTINCTNESS); SOURCED (the imported distance genuinely grain-dependent — GRAVITATIONAL, not reached here); SHAPE-DRAWN (the fork drawn, neither forced, or the baseline unestablished); PARTIAL (degenerate, or the object under test a grain-weighted gadget). The five audit clauses (a)-(e) bundle the payoffs.**

## Imported / prior objects

- WS1: `ws1_grain_and_metric_nontrivial`. WS2: `ws2_metric_from_adjacency`, `ws2_metric_reads_adjacency`. WS3: `ws3_grain_test`, `ws3_no_by_hand_coupling`. WS4: `ws4_inert_reachable`, `ws4_gravitational_reachable`.

## The outcome type and verdict function (universe-free, neutral names)

```lean
namespace P2S13
open P2S9

-- The outcome type. `inert` the imported distance invariant under grain-change at fixed adjacency —
-- geometry decoupled from the grain, no gravity, the NOT-RECOVERED (the expected close, grounded in
-- Series 2.4's DISTINCTNESS); `sourced` the imported distance genuinely varies with the grain — the grain
-- sources the geometry, gravity recovered, scoped to a proportionality (not reached here); `shapeDrawn`
-- the fork drawn, neither pole forced, or the baseline unestablished; `partial'` degenerate (`partial` is a
-- Lean keyword) — the ground trivial, or the object under test a grain-weighted gadget (the smuggle guard).
-- No identifier embeds a forbidden content-word (`sourced`, not `gravitational`, is clear of "gravity").
inductive Outcome
  | sourced
  | inert
  | shapeDrawn
  | partial'
  deriving DecidableEq

-- The verdict FUNCTION of six earned flags (parameters carry NEUTRAL names, clear of the forbidden fragments
-- "metric"/"import" — C1-S4):
--   grainNonConstant  — the grain is non-constant (WS1)
--   distNonTrivial    — the distance is non-trivial (WS1)
--   distFromAdj       — the distance is a function of the adjacency (WS2)
--   couplingEarned    — the distance under test reads only the adjacency, not the grain (WS3)
--   forkTwoSided      — the grain-test's GRAVITATIONAL pole is inhabited (WS4, fork not by fiat)
--   couplingPresent   — the IMPORTED distance varies with the grain at fixed adjacency (WS3/WS4)
def verdict (grainNonConstant distNonTrivial distFromAdj couplingEarned forkTwoSided couplingPresent : Bool) : Outcome :=
  if !couplingEarned then Outcome.partial'                        -- the object under test is a grain-weighted gadget: smuggle
  else if !(grainNonConstant && distNonTrivial) then Outcome.partial'   -- the ground is degenerate
  else if !distFromAdj then Outcome.shapeDrawn                    -- the baseline is unestablished
  else if !forkTwoSided then Outcome.shapeDrawn                   -- the test is one-sided: fork by fiat
  else if couplingPresent then Outcome.sourced                   -- the imported distance is sourced by the grain: GRAVITATIONAL
  else Outcome.inert                                             -- the imported distance is invariant: INERT
```

## Signatures

```lean
-- THE COMPUTED VERDICT. On the earned flags (a non-constant grain and non-trivial distance, the distance a
-- function of the adjacency, the coupling earned, the fork two-sided, the imported distance NOT grain-
-- dependent), `inert` — INERT, by computation.
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.inert

-- Falsifiability: the verdict DISCRIMINATES, reaching all four outcomes.
theorem ws5_verdict_discriminates :
    verdict true true true true true false  = Outcome.inert
  ∧ verdict true true true true true true   = Outcome.sourced       -- if the imported distance gravitated
  ∧ verdict true true true true false false = Outcome.shapeDrawn    -- one-sided test: fork by fiat
  ∧ verdict true true true false true false = Outcome.partial'      -- object under test a grain-weighted gadget
  ∧ verdict false true true true true false = Outcome.partial'      -- the ground is degenerate

-- THE FLAGS ARE JUSTIFIED: the six deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set. The
-- last is the NEGATION (the imported distance is NOT grain-dependent), justifying `importedGrainDep = false`.
theorem ws5_flags_justified :
    (∃ x y : S, grainBump x ≠ grainBump y)                                  -- grainNonConstant (WS1)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')          -- metricNonTrivial (WS1)
  ∧ (∀ c1 c2 : Config, c1.1 = c2.1 → ∀ x y, adjDist c1 x y = adjDist c2 x y) -- metricFromAdj (WS2)
  ∧ (∀ c x y, adjDist c x y = pathDist c.1 x y)                             -- couplingEarned (WS3)
  ∧ (grainDependent foilDist cfgFlat cfgBump)                              -- forkTwoSided (WS4)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump)                             -- importedGrainDep = false (WS3/WS4: INERT)
```

## The five audit clauses (a)-(e)

```lean
-- (a) THE COUPLING IS EARNED, NOT DEFINED (the no-smuggling gate, at the capstone). The distance under test
-- reads the adjacency component ONLY; the single grain-weighted object (the foil) is a DISTINCT object, not
-- the distance under test. No proof term defines the distance as a function of the grain and recovers it.
theorem ws5_audit_coupling_earned :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)

-- (b) THE FORK NOT BY FIAT. INERT reachable by the imported distance and GRAVITATIONAL inhabited by the foil,
-- both from the SAME test; the grain genuinely changes (`cfgFlat.2 ≠ cfgBump.2`); the verdict discriminates.
theorem ws5_audit_fork_genuine :
    (¬ grainDependent adjDist cfgFlat cfgBump)
  ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (cfgFlat.2 ≠ cfgBump.2)
  ∧ (verdict true true true true false false = Outcome.shapeDrawn)

-- (c) THE DISTANCE IS THE BUILT ONE. The distance under test is the imported adjacency-distance (a function
-- of the adjacency), and it genuinely RESPONDS to the adjacency (not a rigged constant): a different
-- adjacency gives a different distance.
theorem ws5_audit_metric_is_built :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y)

-- (d) THE SCOPE IS DISCLOSED. At most a grain-dependence test on the model's own distance is claimed; the
-- verdict is INERT (no coupling claimed of the imported distance), which claims even less than a
-- proportionality. No Einstein field equation, no area law (Bekenstein / holographic) — the forward-note.
theorem ws5_audit_scope :
    (verdict true true true true true false = Outcome.inert)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump)

-- (e) NAMES-NOT-TERMS. The four Outcome values are pairwise DISTINCT (a non-vacuous fact): the verdict's
-- codomain is a genuine four-way discrimination among NEUTRALLY-named outcomes (`sourced`/`inert`/
-- `shapeDrawn`/`partial'`), none named for the interpretive content. The full identifier property (no proof
-- term named "gravity," "curvature," "curve," "mass," "geometry," "metric," "spacetime," "self," "import,"
-- "God," "choice") is a META-property about the source text, enforced by the protocol §6 mechanical grep
-- (hits are docstring prose / the Lean `import` keyword only) — the real teeth. (Replaces the vacuous `: True`
-- house placeholder — C1-S1.)
theorem ws5_audit_names_not_terms :
    Outcome.sourced ≠ Outcome.inert ∧ Outcome.inert ≠ Outcome.shapeDrawn
  ∧ Outcome.shapeDrawn ≠ Outcome.partial' ∧ Outcome.sourced ≠ Outcome.partial'

-- THE VERDICT IS INERT, assembled. With every flag earned by the WS1-WS4 headlines, the computed verdict is
-- `inert`: the imported distance is invariant under grain-change at fixed adjacency. Geometry decoupled from
-- the grain — no gravity — the honest NOT-RECOVERED that Series 2.4's DISTINCTNESS of space and the measure
-- foretold, and the specification for the next iteration: couple the two axes 2.4 kept apart.
theorem ws5_the_verdict : verdict true true true true true false = Outcome.inert
```

## Proofs (by hand, checked)

- `ws5_verdict_eq`, `ws5_verdict_discriminates`: `rfl` / `by decide` (finite Bool computation). Verified in the prototype.
- `ws5_flags_justified`: `⟨ws1_grain_and_metric_nontrivial.1, ws1_grain_and_metric_nontrivial.2, (fun c1 c2 h x y => (ws2_metric_from_adjacency c1 c2 h x y)), (fun _ _ _ => rfl), ws4_gravitational_reachable.2.1, ws3_grain_test cfgFlat cfgBump rfl⟩`.
- `ws5_audit_coupling_earned`: `ws3_no_by_hand_coupling`.
- `ws5_audit_fork_genuine`: `⟨ws3_grain_test cfgFlat cfgBump rfl, ws4_gravitational_reachable.2.1, ws4_inert_reachable.2.1, rfl⟩`.
- `ws5_audit_metric_is_built`: `⟨fun _ _ _ => rfl, ws2_metric_reads_adjacency⟩`.
- `ws5_audit_scope`: `⟨ws5_verdict_eq, ws3_grain_test cfgFlat cfgBump rfl⟩`.
- `ws5_audit_names_not_terms`: `by decide` (the four outcomes pairwise distinct via `DecidableEq`).
- `ws5_the_verdict`: `ws5_verdict_eq`.

## The computed verdict

On this world's earned flags — `grainNonConstant = true`, `metricNonTrivial = true` (`ws1_grain_and_metric_nontrivial`), `metricFromAdj = true` (`ws2_metric_from_adjacency`), `couplingEarned = true` (`ws3_no_by_hand_coupling`), `forkTwoSided = true` (`ws4_gravitational_reachable`), `importedGrainDep = false` (`ws3_grain_test`) — `verdict = Outcome.inert`: **INERT**, geometry decoupled from the grain. The imported distance reads the adjacency and is blind to the grain; packing more of the measure into a region does not bend the distances around it. This is the honest NOT-RECOVERED that Series 2.4's proof that space and the measure are DISTINCT axes foretold. The specification for the next iteration: couple the two axes 2.4 kept apart. The full Einstein equation and the area law (Bekenstein / holographic) are the disclosed forward-note.

## Costume watch

- The verdict is COMPUTED from the flags (`rfl`), never hand-set; it DISCRIMINATES (all four outcomes reachable); the flags are EARNED (each a WS1-WS4 headline). INERT rests on the imported distance being invariant under grain-change (a structural fact — `adjDist` has no channel to the grain), not on a definition; the GRAVITATIONAL pole genuinely inhabited (the foil), so INERT is substantive, not a fiat; the scope disclosed (INERT claims less than a proportionality — no Einstein/area-law). No name is a term.
