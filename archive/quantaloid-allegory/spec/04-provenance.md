# 04 — Provenance

> *The honest accounting, in brief.* Paper one stands on **one definition, no axioms**
> ([`02-foundation.md`](02-foundation.md)). What is mechanized is mechanized; what is interface-relative or
> paper-level says so. Full graded ledger: [`03-theorem-debt.md`](03-theorem-debt.md); assumed/constructed
> boundary + disclosure table: [`07-interface.md`](07-interface.md); open questions:
> [`10-open-questions.md`](10-open-questions.md).

## Tier 1 — mechanized, τ-free (from `{arena, D1, completeness}`; no A1, no A2, no self, no interface)

| Result | Lean | Footprint |
|---|---|---|
| Existence of a fixed self-relation (relational Knaster–Tarski) | `Paper1.self_exists`, `self_greatest` | `[propext, Quot.sound]` |
| Feedback trace `Tr = D1` (+ its trace axioms) | `Paper1.TraceSeam.ptrace`, `ptrace_unit`, `ptrace_prod` | `[propext, Quot.sound]` |
| The seam / reflexive opacity (Lawvere; arena-independent) | `Paper1.Seam.reflexive_opacity`, `lawvere` | **0 axioms** |
| **The arrow's irreversibility** (`reenter` non-injective; semigroup not group) | `Paper1.Arrow.reenter_not_injective` | `[propext, Classical.choice, Quot.sound]` |
| The re-entry **dynamics** exists; the self is idempotent | `Paper1.reentry_self_exists`, `reentry_self_idempotent` | `[propext, Quot.sound]` |

## Tier 2 — mechanized *relative to the modular interface* (assumed substrate, cited, non-relational)

| Result | Lean |
|---|---|
| `A3 = σ ⊕ arrow` (reversible core = `σ`; remainder = trace-scaling) | `Paper1.a3_core_is_modular`, `a3_arrow_scales`, `a3_is_modular_plus_arrow` |
| Bridge reduced (1b): passive core ⇒ `CoDirection` (KMS *derived*, via Pusz–Woronowicz) | `Paper1.coDirectionOfPassive`, `a3_core_is_modular_of_passive` |

The interface dependency is surfaced by `#print axioms` (see [`07-interface.md`](07-interface.md)); the τ-free
Tier 1 carries none of it.

## Paper-level (argued, not mechanized — the type III gap)

The **A1 dissolution** (type III ⇒ no symmetric self), the modular identification's operator steps, the
Takesaki II∞-core measure, and the arrow's **orientation** are paper-level — the substrate (Tomita–Takesaki,
KMS, crossed products) is not in mathlib ([`06-type-III-modular.md`](06-type-III-modular.md) Part D). Flagged,
never faked; no `sorry` as truth.

## Collapses & the minimal foundation

Selectivity ≡ differentiation; orthogonality ⇔ selfhood-selection; the stability dichotomy holds **by absence**
(no tracial state in type III), repeller form open. **A2 (co-direction) was never load-bearing** — parked as
open pending recovery, not deleted ([`10-open-questions.md`](10-open-questions.md)).

## Not paper one's

**Presence / consciousness** (paper four's) and **agency** are **not** in paper one's debt and were not reached
for.

## Prior representation

The traced-SMC edifice is archived as structural reference:
[`../../archive/traceable-smt/INDEX.md`](../../archive/traceable-smt/INDEX.md). Shapes were mined (the seam); no
old-arena proof was imported as new-arena truth.
