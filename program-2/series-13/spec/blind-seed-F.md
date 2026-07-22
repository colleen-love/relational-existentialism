# Blind seed — Phase F (code review). Series 2.13.

You are reviewing built Lean 4 (Mathlib) CODE for whether it PROVES the claimed signatures. You are BLIND: you see the code and the claims below and NOTHING of their motivation. Judge only the code against the contracts here.

## Files you MAY read

- This file (`spec/blind-seed-F.md`).
- The Lean sources ONLY:
  - `program-2/series-13/formal/P2S13/ws1.lean`
  - `program-2/series-13/formal/P2S13/ws2.lean`
  - `program-2/series-13/formal/P2S13/ws3.lean`
  - `program-2/series-13/formal/P2S13/ws4.lean`
  - `program-2/series-13/formal/P2S13/ws5.lean`
  - `program-2/series-13/formal/P2S13.lean`, `program-2/series-13/formal/P2S13/AxiomCheck.lean`

You must NOT read: `charter.md`, `charter-status.md`, `protocol.md`, any `charter-extension` file, any `summary*` file, `grain-derisking.md`, `spec/README.md`, or any `ws*-design.md`. Treat the docstring/comment PROSE in the Lean files as non-authoritative motivation — judge the theorem STATEMENTS and PROOFS, not the comments. If you read a forbidden file, stop and report it (the review is discarded and re-run).

## The objects (defined in the code; carrier `S := Fin 4`, distinguished `p0 p1 p2 p3 : S`)

```lean
abbrev Adj    := S → Finset S ;  abbrev Grain := S → ℕ ;  abbrev Config := Adj × Grain
def stepBall (a : Adj) : ℕ → S → Finset S   -- within-n-steps reachable set
def pathDist (a : Adj) (x y : S) : ℕ         -- least step-count reaching y from x, sentinel 4; reads a ONLY
def adjDist  (c : Config) (x y : S) : ℕ := pathDist c.1 x y            -- reads c.1 ONLY
def foilDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y + c.2 y    -- reads c.1 AND c.2
def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y
def aChain, aStar : Adj ; def grainFlat, grainBump : Grain ; def cfgFlat := (aChain, grainFlat) ; def cfgBump := (aChain, grainBump)
```

## The claimed signatures (the code must PROVE exactly these, sorry-free)

```lean
namespace P2S13
theorem ws1_grain_and_metric_nontrivial :
    (∃ x y : S, grainBump x ≠ grainBump y) ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')
theorem ws2_metric_from_adjacency (c1 c2 : Config) (h : c1.1 = c2.1) : ∀ x y, adjDist c1 x y = adjDist c2 x y
theorem ws2_metric_reads_adjacency : ∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y
theorem ws3_grain_test (c1 c2 : Config) (h : c1.1 = c2.1) : ¬ grainDependent adjDist c1 c2
theorem ws3_grain_test_witnessed : cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2 ∧ ¬ grainDependent adjDist cfgFlat cfgBump
theorem ws3_no_by_hand_coupling : (∀ c x y, adjDist c x y = pathDist c.1 x y) ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
theorem ws4_inert_reachable : cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2 ∧ (∀ x y, adjDist cfgFlat x y = adjDist cfgBump x y)
theorem ws4_gravitational_reachable :
    cfgFlat.1 = cfgBump.1 ∧ grainDependent foilDist cfgFlat cfgBump ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
inductive Outcome | sourced | inert | shapeDrawn | partial'
def verdict (grainNonConstant distNonTrivial distFromAdj couplingEarned forkTwoSided couplingPresent : Bool) : Outcome
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.inert
theorem ws5_verdict_discriminates : (five rows, all four constructors reached)
theorem ws5_flags_justified :
    (∃ x y, grainBump x ≠ grainBump y) ∧ (∃ x y x' y', pathDist aChain x y ≠ pathDist aChain x' y')
  ∧ (∀ c1 c2, c1.1 = c2.1 → ∀ x y, adjDist c1 x y = adjDist c2 x y) ∧ (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (grainDependent foilDist cfgFlat cfgBump) ∧ (¬ grainDependent adjDist cfgFlat cfgBump)
theorem ws5_audit_coupling_earned : (∀ c x y, adjDist c x y = pathDist c.1 x y) ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
theorem ws5_audit_fork_genuine :
    (¬ grainDependent adjDist cfgFlat cfgBump) ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (cfgFlat.2 ≠ cfgBump.2) ∧ (verdict true true true true false false = Outcome.shapeDrawn)
theorem ws5_audit_metric_is_built : (∀ c x y, adjDist c x y = pathDist c.1 x y) ∧ (∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y)
theorem ws5_audit_scope : (verdict true true true true true false = Outcome.inert) ∧ (¬ grainDependent adjDist cfgFlat cfgBump)
theorem ws5_audit_names_not_terms :
    Outcome.sourced ≠ Outcome.inert ∧ Outcome.inert ≠ Outcome.shapeDrawn ∧ Outcome.shapeDrawn ≠ Outcome.partial' ∧ Outcome.sourced ≠ Outcome.partial'
theorem ws5_the_verdict : verdict true true true true true false = Outcome.inert
```

## Your task

1. **Proves-the-claim.** For each theorem, confirm the code proves EXACTLY the stated signature (no weaker restatement, no added hypothesis silently discharged, no `sorry`, no `admit`, no `native_decide` masking a false claim). Confirm `verdict` is a total function and `ws5_verdict_discriminates` genuinely reaches all four constructors (trace the `if`-chain by hand). Confirm `verdict`'s definition matches the seed. Confirm the reported verdict (`ws5_verdict_eq` / `ws5_the_verdict`) is `Outcome.inert`.
2. **Audit (a) — earned, not defined (PRESS HARDEST).** The distance whose verdict is reported is `adjDist`. Confirm from the DEFINITION that `adjDist c x y = pathDist c.1 x y` — i.e. it reads the FIRST component `c.1` and has NO syntactic access to the second component `c.2`. Confirm `pathDist`'s definition reads only its `Adj` argument (no `Grain`/`c.2` anywhere in `pathDist`/`stepBall`). Confirm the ONLY function reading `c.2` is `foilDist`, and that it is proved DISTINCT from `adjDist` (`ws3_no_by_hand_coupling` / `ws5_audit_coupling_earned` second conjunct, via a real witness where they differ) and is NOT the object whose verdict is reported. If the reported verdict rested on a distance reading `c.2`, or if `pathDist`/`adjDist` secretly took a grain argument, grade SERIOUS. Judge: is the invariance of `adjDist` under changing `c.2` STRUCTURAL (no access) or a coincidence?
3. **Audit (b) — the fork not by fiat.** Confirm BOTH poles hold on the SAME config pair `(cfgFlat, cfgBump)` whose second components genuinely differ (`cfgFlat.2 ≠ cfgBump.2`, a real witness at some node): `¬ grainDependent adjDist cfgFlat cfgBump` AND `grainDependent foilDist cfgFlat cfgBump`. Confirm `verdict` reaches `sourced`, `inert`, `shapeDrawn`, `partial'`. If either pole is excluded by construction, or the pair does not actually differ, grade SERIOUS.
4. **Audit (c) — the distance is the built one.** Confirm `adjDist` is `pathDist ∘ (·.1)` (not a fresh `c.2`-reader, not a rigged constant) and `pathDist` genuinely responds to its `Adj` argument (`ws2_metric_reads_adjacency` / `ws5_audit_metric_is_built`: `pathDist aChain ≠ pathDist aStar` somewhere).
5. **Audit (d) — scope.** Confirm NO theorem asserts an equality of `pathDist`/`adjDist` to a functional of the grain `c.2` (an Einstein-style field equation), nor a bound of any grain-sum by a boundary cardinality (an area law). The reported verdict is `inert` (a grain-INdependence result). If any signature overclaims, grade SERIOUS.
6. **Names grep (audit e).** Run: `grep -rniE "\b(gravity|curvature|curve|mass|geometry|metric|spacetime|self|import|god|choice)\b" program-2/series-13/formal`. Confirm every hit is docstring/comment prose or the Lean `import` keyword — NO proof term, def, or constructor is NAMED a bare forbidden content-word. (Composites like `adjDist`, `ws2_metric_from_adjacency`, `ws4_gravitational_reachable` where the word is `_`-delimited/camelCase word-internal are acceptable to the mechanical grep; judge whether any DEFINITION or CONSTRUCTOR identifier IS the interpretive content-word — the distances should be `pathDist`/`adjDist`/`foilDist`, the outcome constructors `sourced`/`inert`/`shapeDrawn`/`partial'`.)
7. **Strip test.** For each headline, delete "grain, distance, adjacency, coupling, source, invariant, geometry, gravity" and confirm it still reads as a bare arithmetic/logical fact (a non-constancy, an inequality, a projection/congruence, an existence of a distinguishing pair, a Bool computation).
8. **Axioms.** Confirm `AxiomCheck.lean` reports only `propext`, `Classical.choice`, `Quot.sound` (or a subset / none) for every payoff — no other axiom, no `sorryAx`.

## Grading rubric

- **SERIOUS:** the code does not prove the claimed signature; a `sorry`/`admit`/`sorryAx`/non-standard axiom; the reported verdict rests on a distance reading `c.2` (audit a); a pole excluded by construction or the config pair does not differ (audit b, fork by fiat); the distance a rigged constant or a fresh `c.2`-reader (audit c); a scope overclaim — an Einstein-style equation or area law (audit d); a DEFINITION or CONSTRUCTOR named a forbidden content-word (audit e); `verdict` not reaching a claimed constructor; an undisclosed narrowing between the claimed signature and the proved one.
- **REAL:** a genuine gap correctly labelled once fixed (an over-strong docstring, a near-`rfl` lemma dressed as content, a hypothesis assumed-and-returned, an interpretive `ws*` theorem-label).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

Grade each finding SERIOUS / REAL / COSMETIC with a stable ID (`F1-S1`, …), the exact location (file:theorem), and the precise defect. Press HARDEST on audit (a): is the distance whose verdict is reported genuinely blind to the grain `c.2`, or does the `inert` outcome smuggle in the `c.2`-reading `foilDist`? If nothing is SERIOUS, state so explicitly. Return a structured list of findings, and at the very end, on its own line, confirm: "Files read: <list>".
