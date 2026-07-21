# Series 2.10 WS3 design (`spec/ws3-design.md`) — decodability is not reversal, and the core criterion (the crux)

**Two things. (i) The reification SECTION is a right-inverse that RECOVERS the reified pattern but does NOT preserve the built measure — decodability is strictly weaker than a dynamical reversal (the costume gate). (ii) State exactly what a genuine reversible core requires: a rank-preserving bijective tick-restriction (the higher bar), and show the criterion is genuine (entails rank-preservation) and satisfiable — so WS4 can test whether any sub-dynamics meets it on the BUILT tick.**

## 1. (i) The section decodes but does not preserve the measure

The section `attendsM` is the right-inverse to `reifyM` on the used patterns (`P2S7.sectionM_e0`): `attendsM (reifyM {e0}) = {e0}`. It DECODES the reified product into its constituent pattern. But the tick that produced the product RAISED the rank (`rankM (reifyM {e0}) = rankM e0 + 1`), so the section does not undo a measure-preserving motion.

```
/-- **THE SECTION DECODES BUT DOES NOT PRESERVE THE MEASURE (WS3.i, the costume gate).** The section is a
right-inverse on the pattern (`attendsM (reifyM {e0}) = {e0}` — it recovers the reified constituent), YET the tick
that produced the reified state raised the built rank (`mu (reifyM {e0}) = mu e0 + 1 ≠ mu e0`). So decodability is
strictly weaker than a dynamical reversal: recovering the pattern does not lower the measure the tick raised. Passing
the section off as a reversal is the look-alike (the exact Series 2.7 lesson). -/
theorem ws3_section_not_measure_preserving :
    attendsM (reifyM {e0}) = {e0}                 -- decodes (right-inverse on the pattern)
  ∧ mu (reifyM {e0}) = mu e0 + 1                  -- but the tick raised the rank
  ∧ mu (reifyM {e0}) ≠ mu e0 := by               -- so the section is NOT measure-preserving
  refine ⟨by decide, by decide, by decide⟩
```

(Type note, in prose: the section has type `Cfg → Finset Cfg` — state to pattern — so it is not even of the type of an iterable sub-dynamics; it is a decoder, not a reversal. The measure conjunct is the operative strip-tested fact.)

## 2. (ii) The core criterion (the higher bar), stated decidably

```
/-- **THE CORE CRITERION.** A genuine reversible core is a nonempty sub-domain `D` on which the map `t` is a
MEASURE-PRESERVING BIJECTION: closed, surjective onto `D`, injective on `D` (⇒ a bijection of the finite `D`), AND
rank-preserving (`m (t x) = m x`). BOTH clauses are required; bijectivity that raises the rank is not a core, and the
decodable section is a still weaker, different thing. `m` is the BUILT rank. -/
def IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D)
  ∧ (D.image t = D)
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y)
  ∧ (∀ x ∈ D, m (t x) = m x)

/-- **THE CRITERION IS GENUINE AND SATISFIABLE (WS3.ii).** (a) `IsCore` ENTAILS rank-preservation — it is the higher
bar, not decodability. (b) It is SATISFIABLE on the built rank by a genuine dynamics: the relabelling swap `tickR` of
the two rank-0 states has the measure-preserving bijective core `{e0, e0'}`. So the criterion is real, not vacuous;
WS4 tests whether the BUILT tick meets it. -/
theorem ws3_core_criterion :
    (∀ t m D, IsCore t m D → ∀ x ∈ D, m (t x) = m x)                 -- entails the higher bar
  ∧ (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D) := by         -- satisfiable on the built rank
  refine ⟨fun t m D h x hx => h.2.2.2 x hx, ⟨{e0, e0'}, ⟨e0, by decide⟩, by decide⟩⟩
```

with the control dynamics (built on the same carrier and the SAME built rank):

```
def tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x   -- swap the two rank-0 states
```

## 3. Strip test and outcome classes

- **Strip test (i).** Delete "reversal," "section": "a built right-inverse `g` with `attends (reify {e0}) = {e0}` while `rankM (reify {e0}) ≠ rankM e0`." A bare right-inverse / non-preservation fact.
- **Strip test (ii).** Delete "core," "reversible": "a decidable predicate on `(t, m, D)` requiring `t` a rank-preserving bijection of `D`, which entails `m (t x) = m x` and is satisfied by a swap." A bare bijection / measure-preservation predicate.
- The verdict function returns `partial'` on `¬sectionNotMP` (decodability conflated with reversal — the mis-set the whole series guards against); it does not materialise.

## 4. Audit hooks

- (a) NO INVERSE SMUGGLED — `IsCore` requires `t` itself to be the bijection; no separate inverse is postulated.
- (c) DECODABILITY IS NOT REVERSAL — `ws3_section_not_measure_preserving` is exactly this separation; `IsCore` is the higher bar.
- (d) THE MEASURE IS THE BUILT RANK — `m` instantiated at `mu = rankM` in `ws3_core_criterion` and downstream.
- (e) NAMES-NOT-TERMS — `IsCore`, `tickR`, `ws3_section_not_measure_preserving`, `ws3_core_criterion` carry no forbidden content-word as a whole word ("reversal"/"reversible" appear only in docstring prose).
