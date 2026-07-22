# WS3 design — the coupling is earned, not defined (the anti-costume core) (2.13)

**Test the grain-dependence of the model's OWN distance, WITHOUT defining a grain-weighted distance as the recovery. Two fronts: (i) `ws3_grain_test` — hold the adjacency FIXED and change the grain: the imported distance is INVARIANT (INERT); (ii) `ws3_no_by_hand_coupling` — the distance under test is the imported adjacency-distance `adjDist`, a function of the adjacency, NOT a distance defined as a function of the grain. The no-smuggling gate, at the capstone.**

## Imported / prior objects

- WS1/WS2: `pathDist`, `adjDist`, `grainDependent`, `foilDist`, `cfgFlat`, `cfgBump`.

```lean
-- the grain-dependence test: does a distance change when only the grain changes (adjacency fixed)?
def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y

-- THE COUNTERFACTUAL FOIL: a by-hand grain-weighted distance. NOT the recovered object; exhibited ONLY in
-- WS4 to witness the test's positive side (audit b). Proved DISTINCT from `adjDist` here.
def foilDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y + c.2 y
```

## Signatures

```lean
-- THE GRAIN TEST — INVARIANT (WS3, the anti-costume core). For any two configurations with the SAME
-- adjacency, the imported distance is not grain-dependent: changing the grain at fixed adjacency does not
-- move `adjDist`. INERT — geometry decoupled from the grain.
theorem ws3_grain_test (c1 c2 : Config) (h : c1.1 = c2.1) : ¬ grainDependent adjDist c1 c2

-- witnessed on the grain-derisking carriers: same adjacency, different grain, distance invariant.
theorem ws3_grain_test_witnessed :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2 ∧ ¬ grainDependent adjDist cfgFlat cfgBump

-- NO BY-HAND COUPLING (WS3, the no-smuggling gate). The distance under test reads the adjacency component
-- ONLY (it is not a function of the grain); and the grain-weighted foil is a DISTINCT object (there is a
-- configuration and pair where `foilDist ≠ adjDist`), so the metric under test is not the smuggle.
theorem ws3_no_by_hand_coupling :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y)
```

## Proofs

- `ws3_grain_test`: `rintro ⟨x, y, hxy⟩; exact hxy (by simp only [adjDist, h])`. The witness `x y` of grain-dependence would need `adjDist c1 x y ≠ adjDist c2 x y`, but `adjDist c = pathDist c.1` and `c1.1 = c2.1`, so they are equal — contradiction. Verified in the prototype.
- `ws3_grain_test_witnessed`: `⟨rfl, (grains differ at p3), ws3_grain_test cfgFlat cfgBump rfl⟩`. `cfgFlat.2 ≠ cfgBump.2` by `congrFun … p3` (`0 ≠ 1`). Verified.
- `ws3_no_by_hand_coupling`: `⟨fun _ _ _ => rfl, ⟨cfgBump, p0, p3, by decide⟩⟩`. `adjDist c = pathDist c.1` definitionally; `foilDist cfgBump p0 p3 = 3 + 1 = 4 ≠ 3 = adjDist cfgBump p0 p3`. Verified.

## Strip test

Delete "grain," "coupling," "distance," "geometry," "gravity": `ws3_grain_test` reads `(c1.1 = c2.1) → ¬ ∃ x y, adjDist c1 x y ≠ adjDist c2 x y` — a bare "equal on the first component determines the value." `ws3_no_by_hand_coupling` reads `(adjDist projects the first component) ∧ (foilDist and adjDist differ somewhere)` — a projection fact and a distinctness fact. Both survive; no content rides on the words.

## Costume watch (audit a — pressed hardest)

- `adjDist` is `pathDist ∘ (·.1)`: it has NO channel to the grain. The invariance `ws3_grain_test` is therefore structural, not a tuned coincidence — the honest INERT.
- The ONLY grain-weighted object, `foilDist`, is the counterfactual foil, proved DISTINCT from `adjDist` (`ws3_no_by_hand_coupling`, second conjunct). No theorem sets the distance under test equal to a grain-functional. The verdict (WS5) reads `adjDist`, never `foilDist`. This is the Series 2.12 `partsWeight` discipline: the alternative is built to be REFUTED / fenced off, never recovered.
