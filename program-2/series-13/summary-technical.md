# Series 2.13 (The Curve): technical summary

**Verdict: INERT. `ws5_verdict_eq : verdict true true true true true false = Outcome.inert`, computed from the earned flags, never hand-set. Build: sorry-free, axiom-clean (standard three or fewer), gate-green, names-grep clean. The capstone of Phase 3 and the last series of the built arc.**

## Imports and reuse

Namespace `P2S13`. Imports `P2S9` only (the cone); reaches Series 2.4's distance / Series 2.7's grain / `P2S8 / … / P2S0 / P1` transitively; does NOT import the quantum sub-arc `P2S11`/`P2S12` or the reversibility fork `P2S10`. Gate line: `check program-2/series-13 "^import (P2S9|P2S13)(\.[A-Za-z0-9_]+)*$"`. The objects are re-seated FRESH on the witness carrier `S := Fin 4`, faithful to the imported constructions (the Series 2.9 precedent: `P2S9` re-seats the Series 2.4 world/metric as `Fin 5` with a fresh `dist`).

## The objects

```
abbrev Adj := S → Finset S ;  abbrev Grain := S → ℕ ;  abbrev Config := Adj × Grain
def stepBall (a : Adj) : ℕ → S → Finset S            -- within-n-steps reachable set
def pathDist (a : Adj) (x y : S) : ℕ                  -- Series 2.4's stepsFrom re-seated: least step-count, sentinel 4; reads a ONLY
def adjDist  (c : Config) (x y : S) : ℕ := pathDist c.1 x y            -- the imported distance under test; reads c.1 (the adjacency) ONLY
def foilDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y + c.2 y    -- the counterfactual foil; reads c.1 AND c.2 (the grain)
def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y
```

The whole INERT result is structural: `adjDist` is `pathDist ∘ (·.1)`, and `pathDist`/`stepBall` take no `Grain` argument, so there is no channel through which the grain `c.2` could influence the imported distance. The carriers `cfgFlat := (aChain, grainFlat)` and `cfgBump := (aChain, grainBump)` share the adjacency `aChain` and differ only in the grain (at `p3`).

## The workstreams

- **WS1 (ground).** `ws1_grain_and_metric_nontrivial` — the grain is non-constant (`grainBump p3 = 1 ≠ 0`) AND the distance takes ≥2 distinct values (`pathDist aChain p0 p1 = 1 ≠ 3 = pathDist aChain p0 p3`). A varying source and a non-trivial geometry: the test is non-degenerate.
- **WS2 (baseline).** `ws2_metric_from_adjacency (h : c1.1 = c2.1) : ∀ x y, adjDist c1 x y = adjDist c2 x y` — the distance is a function of the adjacency (`simp only [adjDist, h]`). `ws2_metric_reads_adjacency : ∃ x y, pathDist aChain x y ≠ pathDist aStar x y` — it genuinely RESPONDS to the adjacency (3 vs 1), not a rigged constant.
- **WS3 (anti-costume core).** `ws3_grain_test (h : c1.1 = c2.1) : ¬ grainDependent adjDist c1 c2` — at fixed adjacency the imported distance is INVARIANT under grain-change (INERT). `ws3_grain_test_witnessed` — same on `cfgFlat`/`cfgBump` (same adjacency, `grainFlat ≠ grainBump`). `ws3_no_by_hand_coupling : (∀ c x y, adjDist c x y = pathDist c.1 x y) ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)` — the object under test reads the adjacency only, and the one grain-weighted object (the foil) is a DISTINCT object (`foilDist cfgBump p0 p3 = 4 ≠ 3`). The no-smuggling gate.
- **WS4 (the knot).** `ws4_inert_reachable` — a config pair, same adjacency, different grain, `adjDist` invariant: the INERT pole, reached by the imported distance. `ws4_gravitational_reachable` — the GRAVITATIONAL pole inhabited by the foil (`grainDependent foilDist cfgFlat cfgBump`), which is proved distinct from `adjDist`: the test is two-sided, no fiat, without smuggling. GRAVITATIONAL is not reached by the imported distance (that is the INERT finding).
- **WS5 (verdict and audit).** `Outcome` with constructors `sourced`/`inert`/`shapeDrawn`/`partial'` (the GRAVITATIONAL outcome neutrally named `sourced`, clear of "gravity"). `verdict` is a total function of six Bool flags; `ws5_verdict_eq` computes `inert` on the earned flags `true true true true true false` (`rfl`); `ws5_verdict_discriminates` reaches all four constructors (`decide`); `ws5_flags_justified` supplies each flag from a WS1-WS4 headline (the trailing `couplingPresent = false` justified by `ws3_grain_test`: the imported distance is NOT grain-dependent). Audit clauses `ws5_audit_coupling_earned` (a), `ws5_audit_fork_genuine` (b), `ws5_audit_metric_is_built` (c), `ws5_audit_scope` (d), `ws5_audit_names_not_terms` (e, the four outcomes pairwise distinct, non-vacuous). `ws5_the_verdict : verdict … = Outcome.inert`.

## The no-smuggling gate (audit a), the clause the series lives or dies on

No object defines the distance as a function of the grain and recovers it. The distance under test, `adjDist`, is `pathDist c.1` — it has no syntactic access to `c.2`, so its invariance under grain-change is structural, not a coincidence to be tuned. The single grain-reading object, `foilDist`, is exhibited ONLY to witness that the grain-test has a genuine positive side (audit b, fork not by fiat), and is PROVED distinct from `adjDist`; the verdict rests on `adjDist` alone. The blind Phase F reviewer pressed hardest here and confirmed the `inert` verdict does not smuggle in the foil: `couplingPresent = false` is justified by `adjDist`'s grain-blindness, and the foil's grain-dependence only justifies `forkTwoSided`, whose falsity would give `shapeDrawn`, never `inert`.

## Reviews

Both blind phases ran and are on record (P3-D1 satisfied). Phase C (design, `blind-seed-C.md`): round 1 one SERIOUS (a vacuous `: True` audit-(e) certificate) closed Fixed and params renamed; round 2 zero SERIOUS, audits (a)/(b) PASS. Phase F (code, `blind-seed-F.md`): zero SERIOUS, zero REAL, two COSMETIC, all 17 signatures proved verbatim, audits (a)-(e), the strip test, and the axiom pass all PASS; blindness confirmed (files-read list audited).

## Mechanical checks (protocol §6)

```
lake build P2S13 P2S13.AxiomCheck   # succeeds (and the full lake build)
grep -rn "sorry" formal             # none
P2S13.AxiomCheck                    # every payoff: subset of {propext, Classical.choice, Quot.sound}; four depend on none
scripts/gate.sh                     # OK program-2/series-13 (imports resolve to P2S9/P2S13 + Mathlib)
names grep                          # all hits docstring prose / the import keyword; no forbidden word on a code identifier
```

## Result

INERT, the honest NOT-RECOVERED. The model's own metric (Series 2.4's directed distance, a function of the adjacency) is decoupled from the grain (Series 2.7's measure of distinction): changing the grain at fixed adjacency does not move the distance, structurally. This is the outcome Series 2.4's proof that space and the measure are DISTINCT axes foretold, gravity being precisely their coupling. The specification for the next iteration is exact: couple the two axes Series 2.4 kept apart. The full Einstein field equation and the area law (Bekenstein / holographic) are the disclosed forward-note. As the terminal series of Phase 3 and the built arc, this landing closes both; Program 1's four permanent opens stand untouched, and the grain-does-not-curve-the-metric question joins the standing catalogue of what the ontology does not yet own.

## Note to Tier 1 (program-level close)

Phase 3 and the built arc are ready to be composed at the program level. The recovery test ran its full course: a light cone from finite attention (2.9, CONE), an irreversibility fork (2.10), destructive interference (2.11, INTERFERING), the rebit Born rule (2.12, BORN), and here the capstone gravity test (2.13, INERT). The kinematics recovered; the metric-grain coupling did not, on the world's own metric, in the direction Series 2.4 foretold. The composition should record the arc as: quantum kinematics recovered, gravity not, with INERT the precise, foundation-grounded specification for a future iteration that couples space and the measure.
