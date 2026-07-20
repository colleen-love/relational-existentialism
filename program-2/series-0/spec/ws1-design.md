# WS1, The carrier and reification (blocking, the construction)

**Design doc. Series 0, the blocking workstream. Owns: the ATTENTION CARRIER (`attends : X → Finset X`), the directed knowing / symmetric relating / passive in-attention read from it, the view of finite out-attention as a `PkObj κ`-coalgebra (`finsetToPk`, `outDest`), the symmetric reduct (`symDest`), and the REIFICATION SECTION on the FINITE functor (`FinReify`, adapting P1's `IsReify`), proved to EXIST non-vacuously and the bound proved finite with no cardinal ceiling. WS1 is blocking: if the finite-attention functor admits no reification section, the series reports OBSTRUCTED and WS2–WS5 stand on nothing.**

*Series 0 IMPORTS the P1 foundation (README §2.1). WS1 DEFINES the carrier (README §2.2) and adapts the reification section to `Finset`. The one signature risk is discipline 1 (the cardinal ceiling): a bound that unfolds to "attention ranges over a κ-bounded set" rebuilds the Series 11 §4.4 wall. The construction risk is discipline-independent: the finite functor may admit no section (OBSTRUCTED, pre-registered).*

## The object at stake

The charter's WS1 (§2): define `attends`, the directed and symmetric relating, knowing, and in-attention; establish the generating coalgebra is the finite out-attention and its reification section and tower exist, so "to relate is to create" has a home; prove the ontological bound is finite attention with no cardinal ceiling. The design's burden: state the reification at exactly the right strength — a section on the FINITE functor (`Finset X → X` with `attends (reify s) = s`), NOT a total `IsReify` on the full `PkObj κ` (which the finite functor cannot satisfy, its images being finite while `PkObj κ` carries infinite sets). The pre-registered obstruction: no finite section exists.

**Ambient theory.** README §2.1 (imported `PkObj`, `IsReify`, `ws1_reify_injective`), §2.2 (`attends`, `finsetToPk`, `outDest`, `sym`, `knows`, `attendedBy`, `symDest`).

## Candidates (framings of the WS1 reification obligation)

### C1, a section on the FINITE functor `FinReify` (the lead)

```lean
/-- **Reification on the finite functor.** A section of `attends`: `attends (reify s) = s` for all finite `s`. -/
def FinReify {X : Type u} (attends : X → Finset X) (reify : Finset X → X) : Prop :=
  ∀ s : Finset X, attends (reify s) = s
theorem ws1_finreify_injective {X} (attends) (reify) (h : FinReify attends reify) :
    Function.Injective reify
theorem ws1_reification_exists :
    ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X),
      FinReify attends reify ∧ Function.Injective reify
```

Reify over the FINITE patterns, exactly the finite-attention functor `F = Finset`. Existence is discharged on a carrier where `Finset X ≃ X` (an infinite `X`, `Cardinal.mk_finset_of_infinite`): set `reify := e`, `attends := e.symm`; then `attends (reify s) = e.symm (e s) = s`, and `reify` is a bijection, so the section is non-vacuous (`Ω ≅ F(Ω)` realized).

- **Ambient:** `Cardinal.mk_finset_of_infinite`, `Cardinal.eq`, an equiv `e : Finset X ≃ X`.
- **Success condition (GROUND, WS1 half):** `ws1_reification_exists` typechecks with a genuine (bijective) section.
- **Failure mode:** *the finite functor admits no section (OBSTRUCTED).* Foreclosed HERE by the cardinal equivalence for infinite `X`; but pre-registered as the honest terminus were the tower to need a stronger section. **Winner (the reification contract).**

**Paper triage.** For infinite `X`, `#(Finset X) = #X`, so a bijection `Finset X ≃ X` exists; `attends := e.symm`, `reify := e` gives `FinReify` immediately. Decidable and immediate. **Winner.**

### C2, total `IsReify` on the full `PkObj κ` (the over-strong framing, rejected)

```lean
theorem ws1_reification_total (attends) : ∃ reify, IsReify (outDest hinf attends) reify   -- REJECT
```

Demand a section of the full `PkObj κ`-coalgebra `outDest`. This is UNSATISFIABLE for the finite functor: `outDest _ (reify s) = finsetToPk _ (attends (reify s))` has a FINITE underlying set, while `s : PkObj κ X` ranges over INFINITE sets; equality fails for any infinite `s`. **Reject as the contract** (it is false, not merely hard). The honest object is the finite section C1; the mismatch is DISCLOSED in the ledger (this is P1.Reader's disclosed situation: "total `IsReify` is unsatisfiable here").

### C3, the reification tower on the finite functor (the retained companion)

```lean
def finReifyStep (attends) (reify) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : Finset X, ↑s ⊆ Ωα ∧ s.Nonempty ∧ x = reify s }
def finTowerN (attends) (reify) (Ω₀ : Set X) : ℕ → Set X
  | 0 => Ω₀ | n+1 => finReifyStep attends reify (finTowerN attends reify Ω₀ n)
theorem ws1_tower_monotone (attends) (reify) (Ω₀) {m n} (h : m ≤ n) :
    finTowerN attends reify Ω₀ m ⊆ finTowerN attends reify Ω₀ n
```

Adapt P1's `reifyStep`/`towerN` to `Finset`, so the tower ("to relate is to create", iterated) has a home on the finite functor. Monotone, immediate. **Retain as WS1's companion** (the tower the tick S1 will need), not the headline.

### C4, the bound is finite attention, no cardinal ceiling (the audit-(a) certificate)

```lean
theorem ws1_bound_is_finite_attention (hinf : ℵ₀ ≤ κ) (attends : X → Finset X) :
    ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < Cardinal.aleph0
```

The out-neighborhoods are strictly FINITE (`< ℵ₀`), uniformly in `κ`: the ontological bound is ℵ₀ (finiteness), below ANY infinite `κ`, never `κ` itself. This is discipline 1's certificate: strip "attention" and it reads "the coalgebra's neighborhoods are finite," a `κ`-free finiteness fact. **Winner (the audit-(a) certificate).**

### C5, order the world by a bounding cardinal (the pullback sin, rejected)

```lean
def worldBound (κ) : Prop := Cardinal.mk X < κ   -- as the ONTOLOGICAL bound   -- REJECT as ontological
```

Take `mk X < κ` as the world's bound. This is the Series 11 §4.4 back door: it makes `κ` the ontological ceiling. **Reject as the ontological bound, SERIOUS.** `mk X < κ` appears ONLY as the ambient hypothesis `hcar` for `symDest`'s in-attention neighborhoods (README §2.2), refutably distinct from a chosen ceiling: it bounds the SYMMETRIC REDUCT's neighborhoods by carrier size, never the out-attention, which is finite for every `κ` (C4).

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | finite section `FinReify`, exists | `mk_finset_of_infinite`, equiv | yes, the bijective section | **win (the contract)** |
| C2 | total `IsReify` on `PkObj κ` | `outDest` | yes, provably FALSE (finite ≠ infinite) | reject (unsatisfiable; disclosed) |
| C3 | finite tower, monotone | `finReifyStep` | yes, refl/trans of `⊆` | **win (companion)** |
| C4 | bound finite, `< ℵ₀`, `κ`-free | `finsetToPk`, `finite_toSet` | yes, `mk < ℵ₀` | **win (audit a)** |
| C5 | `mk X < κ` as ontological bound | — | yes, the wall | **reject (ceiling, SERIOUS)** |

## Winning candidates: C1 (finite section) + C3 (tower) + C4 (finite bound)

### Definitions and obligations (cite README §2.1–§2.2)

```lean
-- finsetToPk, outDest, knows, sym, attendedBy, symDest        (README §2.2)
-- FinReify, ws1_finreify_injective, ws1_reification_exists    (C1)
-- finReifyStep, finTowerN, ws1_tower_monotone                 (C3)
-- ws1_bound_is_finite_attention                               (C4)
```

**Proof architecture.** C1's existence: `X := ULift ℕ` (infinite); `mk_finset_of_infinite` gives `#(Finset X) = #X`, `Cardinal.eq` gives `Nonempty (Finset X ≃ X)`, `Classical.choice` extracts `e`; `attends := e.symm`, `reify := e`; `FinReify` is `e.symm (e s) = s` (`Equiv.symm_apply_apply`); injectivity is `ws1_finreify_injective` (a section is injective: `reify s₁ = reify s₂ ⇒ attends (reify s₁) = attends (reify s₂) ⇒ s₁ = s₂`). C4: `(outDest hinf attends x).1 = ↑(attends x)`, and `(↑(attends x) : Set X).Finite = (attends x).finite_toSet`, giving `mk ↥↑(attends x) < ℵ₀` by `Cardinal.lt_aleph0_of_finite` under `Set.Finite.to_subtype`. C3: `⊆`-monotone by induction, mirroring `ws3_tower_monotone`. **Dependencies:** imported `PkObj`/`IsReify`/`ws1_reify_injective` (as the shape template, `FinReify` is the finite analog). **The carrier and the finite section are WS1's whole content; WS2–WS4 build on the carrier.**

## Outcome classes (per charter §5)

- **GROUND (the WS1 payoff):** `ws1_reification_exists` (a genuine section, `Ω ≅ F(Ω)` for the finite functor), `ws1_bound_is_finite_attention` (finite bound, no ceiling), the tower (`ws1_tower_monotone`).
- **OBSTRUCTED (pre-registered, first-class, the honest obstruction):** the finite-attention functor admits NO reification section. Foreclosed here by the cardinal equivalence; but if the tower demanded a section with extra structure the finite functor could not carry, the obstruction is the result and WS2–WS5 are not built. **The design says so explicitly.**
- **PARTIAL (pre-registered):** reification lands only pointwise (a section at specific patterns, not total over `Finset X`), the situation `P1.Reader` disclosed for its witness; reported PARTIAL.
- **Strip test.** Delete "attention / relating / create" from `ws1_reification_exists` and it is *"a type `X` with `attends : X → Finset X` and `reify : Finset X → X` such that `attends ∘ reify = id`, `reify` injective"*, a bare `Finset`-section fact; from `ws1_bound_is_finite_attention`, *"the coalgebra's neighborhoods are finite, uniformly in `κ`"*, a finiteness fact. No name is a term.

## Deliverable

`program-2/series-0/formal/P2S0/ws1.lean`: `import P1`; the carrier (README §2.2); `FinReify`, `ws1_finreify_injective`, `ws1_reification_exists`; `finReifyStep`, `finTowerN`, `ws1_tower_monotone`; `ws1_bound_is_finite_attention`. **WS1 is blocking; the carrier is ambient for WS2–WS4; OBSTRUCTED is pre-registered.** Axiom check: `#print axioms ws1_reification_exists` reduces through the cardinal equivalence and `Classical.choice` to the standard three. **The finite section is the reification home, the finite bound the guard against the cardinal ceiling, and the carrier the ground WS2–WS4 stand on.**
