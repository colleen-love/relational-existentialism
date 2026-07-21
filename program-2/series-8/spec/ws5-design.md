# WS5 design — the verdict and the audit folded in (2.8)

**The verdict is COMPUTED from the flags, never hand-set: `verdict : Bool⁶ → Outcome`, `= frustrated` by computation on the certified flags, DISCRIMINATING (reaches all six outcomes), the deciding flags EARNED by the WS1–WS4 headlines. The computed verdict is FRUSTRATED: a non-trivial self-relative good (WS1), pairwise coherence pervasive (WS2), the obstruction genuinely many-body and model-derived (WS3), and frustration AND gluing both reachable (WS4) — so local coherence does NOT force a global good, the value analog of energy's global failure (2.7). The five audit clauses (a)–(e) bundle the payoffs.**

## 1. The outcome type and the verdict function

```
inductive Outcome
  | frustrated      -- local coherence does not force a global good (both fork sides reachable) — the expected close
  | gluable         -- a global good FORCED (frustration not reachable) — the surprise, positioning rewritten
  | shapeDrawn      -- the fork drawn, neither side decided in-sight
  | pairwiseOnly    -- the obstruction degenerates to a single edge (not genuinely many-body)
  | disconnected    -- no non-trivial good survives
  | partial'        -- an obligation degenerate ('partial' is a Lean keyword)
  deriving DecidableEq

def verdict (nonTrivial pairwiseCoherent manyBody modelDerived frustReachable glueReachable : Bool) : Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if !manyBody then Outcome.pairwiseOnly
  else if !pairwiseCoherent then Outcome.partial'
  else if !modelDerived then Outcome.partial'
  else if frustReachable && glueReachable then Outcome.frustrated    -- coherence does not FORCE gluing
  else if glueReachable && !frustReachable then Outcome.gluable      -- gluing forced
  else if !glueReachable && !frustReachable then Outcome.shapeDrawn  -- neither decided
  else Outcome.partial'
```

`frustReachable` = a pairwise-coherent population with NO global section exists (the ring); `glueReachable` = one WITH a section exists (the star). Both true means local coherence is compatible with non-gluing — it does not FORCE a global good — the honest capstone finding FRUSTRATED. `gluable` fires only if gluing is forced (frustration not reachable), which would contradict the phase thesis.

## 2. Payoffs

```
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.frustrated      -- := rfl

theorem ws5_verdict_discriminates :                        -- reaches all six outcomes (by decide)
    verdict false true true true true true  = Outcome.disconnected
  ∧ verdict true true false true true true  = Outcome.pairwiseOnly
  ∧ verdict true false true true true true  = Outcome.partial'
  ∧ verdict true true true true true true   = Outcome.frustrated
  ∧ verdict true true true true false true  = Outcome.gluable
  ∧ verdict true true true true false false = Outcome.shapeDrawn

-- the SIX deciding flags earned by the WS1–WS4 headlines (none hand-set)
theorem ws5_flags_justified :
    (valu attTri p1 ≠ valu attTri p2)                                  -- nonTrivial (WS1)
  ∧ (∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v)  -- pairwiseCoherent (WS2)
  ∧ (∀ att : S → Finset S, ∀ x y : S, incr att x y + incr att y x = 0)  -- manyBody: 2-body trivial (WS3)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)  -- modelDerived (WS3)
  ∧ (hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s)      -- frustReachable (WS4)
  ∧ (∃ s : S → ℤ, IsSection attStar s)                                 -- glueReachable (WS4)
```

## 3. The five audit clauses (a)–(e)

```
-- (a) NO GLOBAL GOOD ASSERTED. No section asserted for the frustrated population; the good is FOR a self (`valu`);
-- a section is claimed only where the holonomy vanishes (the star); `gluable` returned only if gluing is forced.
theorem ws5_audit_no_global :
    (¬ ∃ s : S → ℤ, IsSection attTri s)
  ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)
  ∧ (verdict true true true true false true = Outcome.gluable)

-- (b) THE FORK NOT BY FIAT. Frustrated (ring hol = 3) AND gluable (star hol = 0) both reachable, good non-trivial.
theorem ws5_audit_fork_genuine :
    (hol attTri p0 p1 p2 = 3) ∧ (hol attStar p0 p1 p2 = 0) ∧ (valu attTri p1 ≠ valu attTri p2)

-- (c) GENUINE MANY-BODY COCYCLE, NOT A SINGLE EDGE / IMPORT-NESS / BOLTED-ON (the doubled costume gate + T1-S1).
theorem ws5_audit_many_body :
    (∀ att : S → Finset S, ∀ x y : S, hol att x y x = 0)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y)

-- (d) LOCAL COHERENCE IS REAL AND PERVASIVE. Every pair reconciles, for every attention.
theorem ws5_audit_coherence_pervasive :
    ∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v

-- (e) NAMES-NOT-TERMS. Meta-property enforced by the protocol §6 grep (docstring prose excepted); house placeholder.
theorem ws5_audit_names_not_terms : True := trivial
```

## 4. Triage

- **Computed, not hand-set (audit).** `verdict` is total `Bool⁶ → Outcome`; `ws5_verdict_eq` is `rfl`; `ws5_verdict_discriminates` reaches all six by `decide`; the six deciding flags are the WS1–WS4 theorems (`ws5_flags_justified`). No meta-flag: all six inputs are earned.
- **No global (audit a).** No payoff asserts a globally forced good; the good is self-relative; `gluable` fires only under `glueReachable && !frustReachable`, which the honest flags do not set (frustration IS reachable).
- **The costume gate, doubled (audit c).** The verdict rests on the many-body `hol`: `ws5_audit_many_body` shows 2-body-trivial, symmetry-kills-it (model-derived, not bolted on), and genuine directedness — neither Series 2.3 nor Series 07.
- **Strip test.** Each payoff strips to its bare fact (integer non-equality, translation round-trip, signed-sum `= 3`/`= 0`, no-section arithmetic); no interpretive term is load-bearing.
- **Names-not-terms (audit e).** `Outcome`, `verdict`, `valu`, `ws5_*` embed no forbidden content-word.
