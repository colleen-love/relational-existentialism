# Blind seed — Phase C (design review, round 2). Series 2.13.

You are reviewing a set of Lean 4 (Mathlib) DESIGN signatures for coherence and non-vacuity. You are BLIND: you see the mathematical objects and claims below and NOTHING of their motivation. Judge only what is written here. Do not speculate about interpretation. Read ONLY this file.

---

## 1. The objects (namespace `P2S13`, carrier `S := Fin 4`, distinguished `p0 p1 p2 p3 : S`)

```lean
abbrev S : Type := Fin 4
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2 ; def p3 : S := 3

abbrev Adj    : Type := S → Finset S      -- a directed edge assignment
abbrev Grain  : Type := S → ℕ             -- a ℕ-labelling of the nodes
abbrev Config : Type := Adj × Grain

-- nodes reachable from x within n steps of a.
def stepBall (a : Adj) : ℕ → S → Finset S
  | 0,     x => {x}
  | (n+1), x => insert x ((a x).biUnion (fun y => stepBall a n y))

-- a directed path-length: least step-count reaching y from x, sentinel 4 if unreachable within 3 steps.
def pathDist (a : Adj) (x y : S) : ℕ :=
  if y ∈ stepBall a 0 x then 0
  else if y ∈ stepBall a 1 x then 1
  else if y ∈ stepBall a 2 x then 2
  else if y ∈ stepBall a 3 x then 3
  else 4

def adjDist  (c : Config) (x y : S) : ℕ := pathDist c.1 x y            -- reads the first component only
def foilDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y + c.2 y    -- reads both components

def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y

-- concrete carriers
def aChain : Adj := fun x => if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else ∅
def aStar  : Adj := fun x => if x = 0 then {1,2,3} else ∅
def grainFlat : Grain := fun _ => 0
def grainBump : Grain := fun x => if x = p3 then 1 else 0
def cfgFlat : Config := (aChain, grainFlat)
def cfgBump : Config := (aChain, grainBump)
```

Given facts you may treat as computable/true: `pathDist aChain p0 p1 = 1`, `pathDist aChain p0 p3 = 3`, `pathDist aChain p3 p0 = 4`, `pathDist aStar p0 p3 = 1`, `foilDist cfgBump p0 p3 = 4`, `grainBump p3 = 1`, `grainFlat p3 = 0`, `cfgFlat.1 = cfgBump.1 = aChain`.

## 2. The theorem signatures under review

```lean
-- WS1
theorem ws1_grain_and_metric_nontrivial :
    (∃ x y : S, grainBump x ≠ grainBump y)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')

-- WS2
theorem ws2_metric_from_adjacency (c1 c2 : Config) (h : c1.1 = c2.1) :
    ∀ x y, adjDist c1 x y = adjDist c2 x y
theorem ws2_metric_reads_adjacency : ∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y

-- WS3
theorem ws3_grain_test (c1 c2 : Config) (h : c1.1 = c2.1) : ¬ grainDependent adjDist c1 c2
theorem ws3_grain_test_witnessed :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2 ∧ ¬ grainDependent adjDist cfgFlat cfgBump
theorem ws3_no_by_hand_coupling :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)

-- WS4
theorem ws4_inert_reachable :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2
  ∧ (∀ x y, adjDist cfgFlat x y = adjDist cfgBump x y)
theorem ws4_gravitational_reachable :
    cfgFlat.1 = cfgBump.1
  ∧ grainDependent foilDist cfgFlat cfgBump
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)

-- WS5
inductive Outcome | sourced | inert | shapeDrawn | partial'  deriving DecidableEq
def verdict (grainNonConstant distNonTrivial distFromAdj couplingEarned forkTwoSided couplingPresent : Bool) : Outcome :=
  if !couplingEarned then Outcome.partial'
  else if !(grainNonConstant && distNonTrivial) then Outcome.partial'
  else if !distFromAdj then Outcome.shapeDrawn
  else if !forkTwoSided then Outcome.shapeDrawn
  else if couplingPresent then Outcome.sourced
  else Outcome.inert
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.inert
theorem ws5_verdict_discriminates :
    verdict true true true true true false  = Outcome.inert
  ∧ verdict true true true true true true   = Outcome.sourced
  ∧ verdict true true true true false false = Outcome.shapeDrawn
  ∧ verdict true true true false true false = Outcome.partial'
  ∧ verdict false true true true true false = Outcome.partial'
theorem ws5_flags_justified :
    (∃ x y : S, grainBump x ≠ grainBump y)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')
  ∧ (∀ c1 c2 : Config, c1.1 = c2.1 → ∀ x y, adjDist c1 x y = adjDist c2 x y)
  ∧ (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump)
theorem ws5_audit_coupling_earned :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
theorem ws5_audit_fork_genuine :
    (¬ grainDependent adjDist cfgFlat cfgBump)
  ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (cfgFlat.2 ≠ cfgBump.2)
  ∧ (verdict true true true true false false = Outcome.shapeDrawn)
theorem ws5_audit_metric_is_built :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y)
theorem ws5_audit_scope :
    (verdict true true true true true false = Outcome.inert)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump)
theorem ws5_audit_names_not_terms :
    Outcome.sourced ≠ Outcome.inert ∧ Outcome.inert ≠ Outcome.shapeDrawn
  ∧ Outcome.shapeDrawn ≠ Outcome.partial' ∧ Outcome.sourced ≠ Outcome.partial'
```

## 3. Success criteria (restated mechanically; judge the DESIGN against these)

1. There is a non-constant `Grain`-labelling and the path-length `pathDist aChain` takes at least two distinct values. [WS1]
2. `adjDist` is invariant under changing the second component of a `Config` at fixed first component, AND `pathDist` genuinely varies across two different `Adj` (`aChain` vs `aStar`). [WS2]
3. `adjDist c` depends only on `c.1` (so is not `grainDependent` at fixed `c.1`), and `foilDist` is a genuinely DIFFERENT function from `adjDist`. [WS3]
4. There is a `Config` pair, same first component, different second component, on which `adjDist` is invariant (`ws4_inert_reachable`); and `foilDist` IS grain-dependent on that same pair while being distinct from `adjDist` (`ws4_gravitational_reachable`). [WS4]
5. `verdict` is a total function of six flags computing `inert` on the earned flags and reaching all four constructors; each flag equals a proved headline. [WS5]

## 4. The audit checks (a)-(e), as MECHANICAL instructions

- **(a) Earned, not defined.** The distance whose verdict is reported is `adjDist`. Confirm `adjDist c x y = pathDist c.1 x y` for all `c,x,y` (it reads the FIRST component only — no dependence on `c.2`). Confirm the ONLY function that reads `c.2` (`foilDist`) is proved DISTINCT from `adjDist` (`ws3_no_by_hand_coupling` second conjunct) and is NOT the object whose verdict is reported. If the reported verdict rested on a distance that reads `c.2`, grade SERIOUS. Judge: is the invariance of `adjDist` a structural fact (it has no access to `c.2`) or a coincidence?
- **(b) The fork not by fiat.** Confirm BOTH: `¬ grainDependent adjDist cfgFlat cfgBump` (one pole) and `grainDependent foilDist cfgFlat cfgBump` (the other pole), on the SAME config pair with `cfgFlat.2 ≠ cfgBump.2` (the second component genuinely differs). Confirm `verdict` reaches `sourced`, `inert`, `shapeDrawn`, and `partial'` (discriminates). If either pole were excluded by construction, or the two configs did not actually differ, grade SERIOUS.
- **(c) The distance is the built one.** Confirm `adjDist` is the path-length `pathDist` composed with the first projection (not a fresh function reading `c.2`), and that `pathDist` genuinely responds to its `Adj` argument (`pathDist aChain ≠ pathDist aStar` somewhere). If the distance were a rigged constant (responds to nothing) OR a fresh gadget reading `c.2`, grade SERIOUS.
- **(d) Scope.** Confirm NO signature claims more than a grain-dependence test on `adjDist`. The reported verdict is `inert` (no dependence claimed of `adjDist`). Confirm no signature asserts an Einstein-style field equation (an equality of `pathDist` to a functional of `c.2`) or an area law (a bound of any node-labelling sum by a boundary cardinality). If any signature overclaims such, grade SERIOUS.
- **(e) Names.** Grep the signatures: no theorem/def/constructor identifier may BE a forbidden content-word as its name — the forbidden set: gravity, curvature, curve, mass, geometry, metric, spacetime, self, import, god, choice. (Underscored/camelCase composites that merely CONTAIN a fragment are acceptable to the mechanical grep; judge whether any identifier is NAMED for the interpretive content, e.g. a def literally named `metric` or a constructor `gravitational`.)

## 5. Strip test

For each headline, delete the words "grain," "distance," "adjacency," "coupling," "source," "invariant," "geometry," "gravity" and confirm the statement still reads as a bare arithmetic/logical fact (a non-constancy, an inequality, a projection/congruence, an existence of a distinguishing pair). If a headline becomes vacuous or circular once stripped, grade it.

## 6. Grading rubric

- **SERIOUS:** the design cannot support its claim; the reported verdict rests on a distance that reads `c.2` (audit a); a pole is excluded by construction or the config pair does not differ (audit b, fork by fiat); the distance is a rigged constant or a fresh `c.2`-reading gadget (audit c); a scope overclaim — an Einstein-style equation or area law (audit d); a name is a term (audit e); or a signature is vacuous/circular.
- **REAL:** a genuine gap correctly labelled once fixed (an over-strong name, an assumed-and-returned hypothesis, a mislabeled conjunct, a docstring overclaim).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

## 7. Your task

For EACH signature: (1) is the design COHERENT and NON-VACUOUS — could it be proved as stated on the given computable facts, and does it say something with content? (2) Run the audit checks (a)-(e) and the strip test. (3) Grade each finding SERIOUS / REAL / COSMETIC with a stable ID (`C1-S1`, `C1-S2`, …), the exact location (theorem/def name), and the precise defect. Press HARDEST on (a): is the distance whose verdict is reported (`adjDist`) genuinely blind to the second component `c.2`, or does the reported outcome smuggle in the `c.2`-reading `foilDist`? Return a structured list of findings. If you find nothing SERIOUS, say so explicitly.
