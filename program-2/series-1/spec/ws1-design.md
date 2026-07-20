# WS1, The cycle and its reification (the primitive, the construction knot)

**Design doc. Series 2.1, the blocking workstream. Owns: the ATTENTION CYCLE and its COMPOSITE (the tick). A
finite pattern of relata each attending the next, closing on the first, reified by S0's finite-functor section
into a composite relatum of the same field whose `attends` is exactly the cycle pattern. Blocking: if the cycle
imports structure beyond the stream, the series reports DISCONNECTED and WS2-WS5 are not built.**

*Series 2.1 imports `P2S0`; the section machinery (`FinReify`, `reifyStep`, `ws1_finreify_injective`,
`ws1_bound_is_finite_attention`) and the base case (`ws1_first_other`, the self-loop reified) are S0's own API
(README §1). WS1 fixes the shared witness `TCar` (README §3) and proves the composite well-formed. The one
signature risk (protocol §0.8, watch-point WS1): a composite that NAMES a cycle-object while importing its
structure via a fresh opaque constructor, the section `attendsT (reifyT cycleA) = cycleA` never discharged.*

## The object at stake

The charter's WS1 (§2): define an attention cycle, reify it into a composite relatum of the SAME field, and
prove the composite well-formed - a relatum of the field (`ws1_cycle_reifies`), its attention a genuine finite
`attends` set composed from its components (`ws1_composite_attention_finite`). The pre-registered sin: the
composite's well-formedness posited, not discharged from the section pointwise the way `ws1_first_other`
discharges the base case.

## Candidates

### C1, the composite as a pointwise section on a concrete witness (the lead)

Reify cycle A `{p0,p1}` into `kA` on `TCar` (README §3), sectioning `attendsT` pointwise, exactly as
`ws1_first_other` reifies `{s0}` into `s1`.

```lean
-- the genuine 2-cycle closes into kA, a relatum of the same field, sectioning attendsT
theorem ws1_cycle_reifies :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1)            -- cycle A is a genuine 2-cycle
  ∧ reifyT cycleA = kA                                 -- the cycle reifies into kA
  ∧ attendsT (reifyT cycleA) = cycleA                  -- the section: kA attends exactly the cycle
  ∧ (reifyT cycleA ≠ reifyT cycleB                     -- distinct cycles give distinct composites
      ∧ reifyT cycleA ≠ reifyT ({kA, kB} : Finset TCar)
      ∧ reifyT cycleB ≠ reifyT ({kA, kB} : Finset TCar))
```
where `cycleA : Finset TCar := {p0, p1}`, `cycleB := {q0, q1}`. The last conjunct is the explicit distinctness
triple (C1-S6 repair: replacing an under-specified `Function.Injective reifyTOn`): distinct cycles reify to
distinct composites on the three sectioned patterns, by `decide`. Total `FinReify` is unsatisfiable on the
finite carrier (disclosed as in S0), so injectivity is stated as pointwise distinctness, not as injectivity of
the fallback-carrying total `reifyT`.

- **Ambient:** `attendsT`, `reifyT`, `cycleA` (README §3); the pattern of `ws1_first_other`.
- **Success condition:** all four conjuncts by `decide`/`rfl`; `kA : TCar` (same field), no new type.
- **Failure mode:** *the composite imports structure (watch-point WS1).* Foreclosed: `kA = reifyT cycleA` and
  `attendsT kA = cycleA` are `decide`-facts about the concrete witness, not an opaque constructor. **Winner.**

### C2, the composite's attention is a genuine finite `attends`, composed from its components

```lean
theorem ws1_composite_attention_finite {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∀ x : TCar, Cardinal.mk (↥((outDest hinf attendsT x).1)) < Cardinal.aleph0)  -- finite bound (audit a)
  ∧ attendsT kA = cycleA                                    -- composed from the components (the cycle set)
  ∧ (∀ z ∈ attendsT kA, z = p0 ∨ z = p1)                    -- bounded BY the components, attends no more
```
The finite bound is `ws1_bound_is_finite_attention hinf attendsT` (S0). The second and third conjuncts are the
"composed from, and bounded by, its components' attention" clause of the charter, by `decide`.

- **Success condition:** the bound is S0's theorem; the composition facts by `decide`.
- **Failure mode:** *a cardinal ceiling smuggled in.* Foreclosed: the bound is ℵ₀ (finiteness), uniform in κ,
  inherited from S0's `ws1_bound_is_finite_attention`. **Winner.**

### C3, the tick as the general case of `ws1_first_other` (the framing, non-payoff)

State that the base case is the self-loop: `ws1_first_other` reifies the 1-cycle `{s0}` into `s1`; WS1 reifies
the 2-cycle `cycleA` into `kA`. Recorded as prose in the deliverable (a framing, not a separate theorem, to
avoid a bare conjunction). **Retain as commentary; not a signature.**

### C4, a total `FinReify` section on the witness (the over-strong framing)

```lean
theorem ws1_total_section {κ} (hinf) : FinReify attendsT reifyT   -- ∀ s, attendsT (reifyT s) = s
```
- **Failure mode:** *unsatisfiable on the finite carrier* (finite images vs all finite patterns; S0 discloses
  the same for its witness). **Reject; the pointwise section (C1) is the honest strength.**

### C5, the composite via an opaque `Quotient`/`Sigma` constructor (the smuggle)

Define `kA` as an abstract "cycle object" `⟨cycleA, proof⟩` in a fresh type, then assert it attends `cycleA`.

- **Failure mode:** *the well-formedness posited, not discharged (watch-point WS1, SERIOUS).* The composite
  would be a new layer of substance, not a relatum of `TCar`, and the section would be an axiom of the
  constructor. **Reject.** C1 keeps `kA : TCar`, the section a `decide`-fact.

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | pointwise section, `kA : TCar` | `attendsT`, `reifyT` | yes, `decide`/`rfl` | **win (well-formedness)** |
| C2 | finite attention, composed from components | `ws1_bound_is_finite_attention` | yes | **win (finiteness)** |
| C3 | base-case framing | `ws1_first_other` | prose only | retain as commentary |
| C4 | total `FinReify` | — | unsatisfiable | reject (over-strong) |
| C5 | opaque cycle-object | — | posited section | **reject (smuggle, SERIOUS)** |

## Winning candidates: C1 + C2

**Proof architecture.** The witness `TCar`/`attendsT`/`reifyT`/`rankT`/`cycleA` is defined in `formal/P2S1/ws1.lean`
(README §3). `ws1_cycle_reifies` and `ws1_composite_attention_finite` discharge by `decide`/`rfl` plus S0's
`ws1_bound_is_finite_attention`. `kA : TCar` is a relatum of the same field: no new type, no atom. The
distinctness of the three composites (distinct cycles reify to distinct relata) is `decide`. The base case
(`ws1_first_other`) is cited in prose (C3).

## Outcome classes (per charter §5)

- **Well-formed (the WS1 payoff, feeds `wf = true`):** both theorems typecheck on `TCar`; `kA` a relatum of
  the field with a genuine finite composed `attends`.
- **DISCONNECTED (pre-registered, first-class):** if the cycle cannot reify without importing structure beyond
  the stream (no section dischargeable; C1 fails), WS1 lands DISCONNECTED, `wf = false`, the series reports
  Disconnected, WS2-WS5 not built. The obstruction (which pattern fails to section) is recorded in
  `charter-status.md`.
- **Strip test.** Delete "cycle", "tick", "composite", "moment" from `ws1_cycle_reifies` and it reads: *"a
  finite pattern `cycleA` has a section `reifyT` with `attendsT (reifyT cycleA) = cycleA`, and distinct
  patterns reify to distinct values"* - a bare `FinReify`/section fact. From `ws1_composite_attention_finite`: *"the
  out-neighborhoods are finite (`< ℵ₀`), and `attendsT kA = cycleA`"* - a bound-and-set fact. No name is a term.

## Deliverable

`formal/P2S1/ws1.lean`: the witness `TCar` and its `attendsT`/`reifyT`/`rankT`/`cycleA`/`cycleB`, the carrier
lemmas (`attendsT_ne_empty`, `ws1_tcar_SHNE`, the pointwise sections, `plainOf_rankLiftT`, `rankLiftT_val`),
and `ws1_cycle_reifies`, `ws1_composite_attention_finite`. **WS1 is blocking; the witness is ambient for
WS2-WS4; DISCONNECTED is pre-registered.** Axiom check: `#print axioms ws1_cycle_reifies` reduces through
`decide` and the finite witness to the standard three.
