# paper-1 — a self arises from one definition, no axioms

**The finding.** On a **seam-chosen arena** — a quantaloid/allegory in which relations are primitive, with
`Q` the hyperfinite **type III₁ factor** (chosen because the **seam/opacity** forces tracelessness, never
because of asymmetry) — a **single definition** generates the core results, **with no axioms**:

> **D1 — self-relation is the trace** (the diagonal, `reenter S = S ⨾ S`). That is the whole foundation.

From `{arena, D1, completeness}` alone — **τ-free, no A1, no A2, no self, no interface** — the headline
cluster follows, all mechanized:

| Result | Lean | Footprint |
|---|---|---|
| **Existence** of a fixed self-relation | `self_exists` | `[propext, Quot.sound]` |
| **Feedback trace `Tr = D1`** | `TraceSeam.ptrace` (+ axioms) | `[propext, Quot.sound]` |
| **The seam / opacity** (a self can't fully trace what includes it; Lawvere) | `Seam.reflexive_opacity` | **0 axioms** |
| **The arrow's irreversibility** (self-composition non-invertible; a semigroup, not a group) | `Arrow.reenter_not_injective` | upstream of the self |

**The headline, stated at the strength it earns:** *self-reference creates the arrow's **irreversibility***
— intrinsically, below the self. Its **orientation** (which way is the future) is *not* derived from
self-reference; that needs the modular/KMS structure of `σ` and may **not** be imported
([`spec/09-arrow.md`](spec/09-arrow.md)). We do not overclaim "the arrow of time."

## The foundation (read these first)

- [`spec/00-domain.md`](spec/00-domain.md) — the **type III₁ relational arena**, justified by the **seam**
  (opacity ⇒ tracelessness ⇒ type III), never by asymmetry.
- [`spec/01-signature.md`](spec/01-signature.md) — the vocabulary, **no self named**.
- [`spec/02-foundation.md`](spec/02-foundation.md) — **D1, the one definition; no axioms.** A1 (asymmetry)
  **dissolves into the arena** (type III has no tracial = symmetric self; grounding flagged paper-level); A2
  (co-direction) is **parked as open**, not deleted.

## Results by strength

- **Tier 1 — τ-free, from `{arena, D1, completeness}`** (the table above): existence, feedback trace,
  seam/opacity, the arrow's irreversibility. No interface, no self.
- **Tier 2 — relative to the assumed modular interface** ([`spec/07-interface.md`](spec/07-interface.md)):
  time = the reversible modular flow `σ` a state generates; the arrow's **orientation**; `A3 = σ ⊕ arrow`
  given the passivity/`CoDirection` bridge (flagged as the paper-level residual). The assumed/constructed
  boundary is surfaced via `#print axioms` and a disclosure table; the τ-free core needs none of it.
- **Collapses (established):** the re-entry **dynamics** is derived interface-free (selves are idempotents),
  so A3 is **not** an axiom ([`spec/08-raising.md`](spec/08-raising.md)); **selectivity ≡ differentiation**;
  **orthogonality ⇔ selfhood-selection**; the **stability dichotomy** holds **by absence** (type III has no
  symmetric self), with the dynamical-repeller form left open and falsifiable.

The full graded ledger is [`spec/03-theorem-debt.md`](spec/03-theorem-debt.md); the exploration that got here
runs [`05-trace-seam`](spec/05-trace-seam.md) → [`06-type-III-modular`](spec/06-type-III-modular.md) →
[`07-interface`](spec/07-interface.md) → [`08-raising`](spec/08-raising.md) → [`09-arrow`](spec/09-arrow.md).
Open questions are consolidated in [`spec/10-open-questions.md`](spec/10-open-questions.md).
[`spec/04-provenance.md`](spec/04-provenance.md) is the short provenance.

## The arc

The foundational paper the others build on: **paper-1** (*a self arises*) → paper-2 (the self **in time**:
arrow, energy, seam) → paper-3 (the self's **modular / thermal** structure) → paper-4
(**conservation / presence**). Papers 2–4 currently exist only in the archived (traced-SMC) representation
([`../archive/archived/`](../archive/archived)); they will be re-grounded on the relational arena after paper
one lands. See [`../STRUCTURE.md`](../STRUCTURE.md) and
[`../archive/archived/INDEX.md`](../archive/archived/INDEX.md) (the shapes mined here).
