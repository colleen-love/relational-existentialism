# 04 — Provenance

> *The honest accounting.* Paper one is an **exploration in progress** on the new relational arena. What is
> proved is proved; what is obstructed is reported as such. The full per-theorem status is
> [`03-theorem-debt.md`](03-theorem-debt.md); this page is the short ledger.

## What is mechanized (Lean 4, `sorry`-free)

| Result | Lean | Footprint | Tier |
|---|---|---|---|
| **Existence** of a fixed self-relation (relational Knaster–Tarski) | `Paper1.self_exists`, `Paper1.self_greatest` | `[propext, Quot.sound]` | **R** — Knaster–Tarski on the lattice of relations; the *application* (the greatest fixed relation = the self) is the synthesis |
| **Reflexive opacity** (the seam, Lawvere) | `Paper1.Seam.reflexive_opacity`, `Paper1.Seam.lawvere` | **0 axioms** | **R / S** — Lawvere's diagonal, arena-independent; ported from the archive verbatim |
| **Raising ascends to the self** (A3 order-proxy) | `Paper1.Frontier.raising_ascends_to_self`, `bounded_by_top` | `[propext, Quot.sound]` | **R** — the order-half of A3; the quantitative half is obstructed |

**Axioms actually invoked** (the minimal-set finding): existence and the raising-proxy use **only the arena's
completeness** (no A1, no A2); the seam uses **no axioms at all**. See [`03-theorem-debt.md`](03-theorem-debt.md).

## What is obstructed (reported, not forced)

The **quantitative** A3 dynamics (capacity bound, asymmetric rates, mutual/non-freezable), **sparsity**,
**self-differentiation**, the **stability dichotomy** (the falsifiable headline), and **recovery** are all
**obstructed pending a trace / measure on `Q`** — the open arena seam. None is faked; the Lean carries no
`sorry`, and the obstructed targets are stated in prose with their precise blockers in
[`03-theorem-debt.md`](03-theorem-debt.md).

## Not paper one's

**Presence / consciousness** (paper four's, where conservation defines a remainder) and **agency** (a gloss on
operational closure, not a theorem) are **not** in paper one's debt and were not reached for.

## Prior representation

The traced-SMC edifice that proved the downstream results in the old arena is archived as structural
reference: [`../../archive/archived/INDEX.md`](../../archive/archived/INDEX.md). Shapes were mined (the seam);
no old-arena proof was imported as new-arena truth.
