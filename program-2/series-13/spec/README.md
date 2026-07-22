# Series 2.13 design index (`spec/README.md`) — THE CURVE

**The design layer for the capstone of Phase 3 and the last series of the built arc. Read `grain-derisking.md` first (the paper gate: take Series 2.4's imported directed distance and Series 2.7's imported grain, build two configurations with the SAME adjacency but DIFFERENT grain, and test whether the distance differs — it does NOT; the imported distance is a function of the adjacency alone, invariant under grain-change; the expected verdict is INERT, grounded in Series 2.4's proof that space and the measure are DISTINCT axes). This README fixes the imported object, the one added primitive, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All files (`grain-derisking.md`, `README.md`, `ws1..ws5-design.md`) are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported object (quantified, never named as content)

Series 2.13 imports `P2S9` only; `P2S8 / P2S7 / … / P2S4 / … / P2S0 / P1` are reached transitively. It does NOT import the quantum sub-arc `P2S11`/`P2S12` or the reversibility fork `P2S10` (their content is not reused). Working material, all built and axiom-checked upstream:

- **The distance** (Series 2.4, `P2S4.stepsFrom x y := sInf {n | reachIn attendsW n x y}`): the shortest DIRECTED attention-path length, a function of the ADJACENCY alone (it takes no grain argument). The candidate curved geometry.
- **The grain** (Series 2.7, `P2S7.rankM : MCar → ℕ`, the reification rank, `ws1_rank_nontrivial`: non-constant, a genuine import): the measure of distinction. The candidate source.
- **The adjacency** (the directed reachability structure): exactly the input the distance reads.

The distance and grain are re-seated FRESH on this series' witness carrier `S := Fin 4` (the Series 2.9 precedent: `P2S9` re-seats the Series 2.4 world/metric as `Fin 5` with a fresh `dist`), faithful to the imported constructions — the distance a decidable fuel-computed least-path-length `pathDist` (definitionally Series 2.4's `stepsFrom`, a function of the adjacency alone), the grain a non-constant measure `grain : S → ℕ` over the relata. Nothing is rigged: the distance is the genuine directed graph-distance, and it is proved to RESPOND to the adjacency (not a dead constant) while being BLIND to the grain.

## 2. The one added primitive (built FRESH at S13; `formal/P2S13/ws1..ws5`)

Series 2.13 adds exactly one thing — the reading of the grain as a possible SOURCE of the distance, together with the grain-dependence test (does the imported distance vary with the grain at fixed adjacency?):

```lean
abbrev Adj    : Type := S → Finset S              -- the adjacency (directed reachability)
abbrev Grain  : Type := S → ℕ                     -- the measure of distinction over the relata
abbrev Config : Type := Adj × Grain               -- a world: an adjacency and a grain on it

-- the imported distance, read as a distance over configurations: it reads the adjacency component ONLY.
def adjDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y

-- the grain-dependence test: does a distance change when only the grain changes?
def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y
```

Everything downstream is a decidable fact on `Fin 4` (`decide`/`rfl`/`simp`). The test holds the adjacency fixed (`c1.1 = c2.1`) and changes the grain, and asks whether `adjDist` moves. It does not: `adjDist` is `pathDist ∘ (·.1)`, so same adjacency forces equal distance — INERT. No grain-weighted distance is the recovered object.

## 3. The discipline (the no-smuggling gate, PROMOTED first-class, at the capstone)

- **The coupling is EARNED, not defined (audit a, the phase sin here).** No object defines the distance as a function of the grain and calls that the recovery. `adjDist c = pathDist c.1` reads only the adjacency (proved, `ws3_no_by_hand_coupling`). The single grain-weighted object, `foilDist c x y := pathDist c.1 x y + c.2 y`, is a COUNTERFACTUAL FOIL exhibited ONLY to witness the test's positive side (audit b); it is proved DISTINCT from `adjDist` and the verdict rests on `adjDist` alone. This is the Series 2.12 `partsWeight` pattern (a built alternative the discipline fences off), never the recovery.
- **The fork not by fiat (audit b).** INERT is genuinely reachable (`adjDist` invariant under grain-change — `ws4_inert_reachable`) and GRAVITATIONAL is a genuinely inhabited pole of the test (`foilDist` DOES vary with the grain — `ws4_gravitational_reachable`), so the verdict discriminates and the imported distance's INERT is substantive, not vacuous. The distance is not a rigged constant: it RESPONDS to the adjacency (`ws2_metric_reads_adjacency`) while being blind to the grain — genuinely INERT, not dead.
- **The distance is the built one (audit c).** `adjDist` is the imported directed path-distance (Series 2.4's `stepsFrom`, re-seated faithfully), a function of the adjacency, not a fresh grain-weighted gadget. It responds to the adjacency and equals the genuine graph-distance on the carriers.
- **The scope is disclosed (audit d).** At most a grain-dependence test on the model's own distance is claimed; the verdict is INERT, which claims even less than a proportionality. No theorem claims a full Einstein field equation, nor the area law (Bekenstein / holographic, information bounded by boundary not volume) — the disclosed forward-note.
- **INERT honorable, GRAVITATIONAL / SHAPE-DRAWN pre-registered.** INERT (geometry decoupled from the grain — no gravity) is the honest NOT-RECOVERED grounded in Series 2.4's DISTINCTNESS, and the specification for the next iteration: couple the two axes 2.4 kept apart. GRAVITATIONAL (the imported distance sourced by the grain) does not materialise (§ grain-derisking), but is pre-registered and reachable/discriminated in the verdict function. SHAPE-DRAWN joins the standing opens.

## 4. Cross-workstream triage

| WS | Object | Headline(s) | Costume foreclosed |
|----|--------|-------------|--------------------|
| WS1 (ground) | `grain`, `pathDist` | `ws1_grain_and_metric_nontrivial` | a non-constant grain (a varying source) and a non-trivial distance (a geometry it could bend); non-degenerate test |
| WS2 | `adjDist`, `pathDist` | `ws2_metric_from_adjacency`, `ws2_metric_reads_adjacency` | the distance a function of the adjacency, and genuinely responsive to it — not a rigged constant |
| WS3 (anti-costume core) | `adjDist`, `grainDependent`, `foilDist` | `ws3_grain_test`, `ws3_no_by_hand_coupling` | the imported distance INVARIANT under grain-change at fixed adjacency; the object under test reads only the adjacency, not the grain-weighted foil |
| WS4 (the knot) | `adjDist`, `foilDist` | `ws4_inert_reachable`, `ws4_gravitational_reachable` | INERT reached by the imported distance; GRAVITATIONAL inhabited only by the foil — the fork genuine, no fiat |
| WS5 | `verdict` | `ws5_verdict_eq (= inert)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)-(e) | computed, not hand-set |

## 5. The outcomes (WS5)

`inert` (the imported distance is invariant under grain-change at fixed adjacency → INERT, geometry decoupled from the grain, no gravity, the NOT-RECOVERED grounded in Series 2.4's DISTINCTNESS — the expected close and a specification: couple the two axes), `sourced` (the imported distance genuinely varies with the grain → GRAVITATIONAL, the grain sources the geometry, an equation-of-state shape, scoped to a proportionality — pre-registered, reachable in the verdict function, not witnessed here), `shapeDrawn` (the fork drawn, neither pole forced, or the baseline unestablished), `partial'` (degenerate; `partial` is a Lean keyword — the ground trivial, or the object under test a grain-weighted gadget: the smuggle guard). The GRAVITATIONAL outcome is named `sourced` (the grain sources the distance) to keep every identifier clear of the forbidden content-words "gravity"/"curve"/"curvature".

## 6. Names-in-prose rule (audit e)

The concept-words — gravity, curvature, curve, mass, geometry, metric, spacetime, self, import, God, choice — appear only in docstring prose. Every proof term, definition, and constructor carries a NEUTRAL name: `pathDist` / `adjDist` (the distance — "metric" is forbidden as a term-name, so the neutral `dist` stem is used), `grain`, `Adj` / `Config`, `grainDependent`, `foilDist`, `verdict`, `Outcome`, `sourced` / `inert` / `shapeDrawn` / `partial'`, `ws*`. No headline embeds a forbidden content-word as a whole word: `sourced` (not `gravitational`, clear of "gravity"), `adjDist`/`pathDist` (not `metric`). The §6 grep `\b(gravity|curvature|curve|mass|geometry|metric|spacetime|self|import|god|choice)\b` runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt. The grep treats `_` and camelCase as word-internal, so the semantic check (protocol §5) is the real teeth: NO proof term is NAMED for the interpretive content, checked by the blind reviewer.

## 7. Module registration (recorded at Phase B, applied at Phase E)

Namespace `P2S13`. At Phase E, in `lake/lakefile.toml`:
```
[[lean_lib]]
name = "P2S13"
srcDir = "../program-2/series-13/formal"
roots = ["P2S13", "P2S13.AxiomCheck"]
```
append `"P2S13"` to `defaultTargets`; in `scripts/gate.sh` add `check program-2/series-13 "^import (P2S9|P2S13)(\.[A-Za-z0-9_]+)*$"`. Layout: `formal/P2S13.lean` (imports `P2S13.ws1`…`P2S13.ws5`), `formal/P2S13/wsN.lean`, `formal/P2S13/AxiomCheck.lean`, mirroring `program-2/series-9/formal/P2S9/`.
