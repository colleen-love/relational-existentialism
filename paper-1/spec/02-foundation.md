# 02 — The foundation: one definition, no axioms

> *What paper one actually stands on.* A **single definition** on a **seam-chosen arena**
> ([`00-domain.md`](00-domain.md)) — **there are no axioms.** From `{arena, D1, completeness}` alone, with no
> A1, no A2, no self, and no interface, the headline cluster follows: existence of a fixed self-relation, the
> feedback trace, the **seam** (opacity), and the **arrow's irreversibility**. The former axioms A1 and A2 are
> *not* part of the foundation — A1 **dissolves into the arena**, and A2 is **parked as open** (below).

## D1 — self-relation is the trace (the one definition)

A **self-relation** is a relation `A ⇸ A`. **Self-relation as feedback is the trace** — the relation routed
back into itself; the **diagonal**; concretely `reenter S = S ⨾ S`. This is **minimal**: just the feedback of a
relation on itself, with **no modular content** (the modular / thermal reading of the trace is the assumed
interface's, [`07-interface.md`](07-interface.md), not part of this foundation).

**This single definition, on the arena, generates the τ-free cluster** ([`03-theorem-debt.md`](03-theorem-debt.md),
Tier 1):

- **Existence** of a fixed self-relation (relational Knaster–Tarski) — `Paper1.self_exists`.
- **The feedback trace `Tr = D1`** — `Paper1.TraceSeam.ptrace` (and its trace axioms), `τ`-free.
- **The seam / opacity** — a self cannot fully trace the relation that includes it (Lawvere) —
  `Paper1.Seam.reflexive_opacity`, **0 axioms**.
- **The arrow's irreversibility** — self-composition is non-invertible (`S` is unrecoverable from `S ⨾ S`; a
  semigroup, not a group) — `Paper1.Arrow.reenter_not_injective`, **upstream of the self**.

All four use **only `{arena, D1, completeness}`** — neither A1 nor A2, no self, no interface. *That is the
finding: one definition on a seam-chosen arena, no axioms.*

## On the former axioms

Earlier drafts carried two axioms, **A1 (asymmetry)** and **A2 (co-direction)**. Neither survives as an axiom.

### A1 — asymmetry: **dissolved into the arena**

A1 is now a **derived consequence**, not a premise. The arena's value-object is the hyperfinite **type III₁
factor**, chosen by the **seam** (a self whose accounting never closes ⇒ no trace ⇒ type III — see
[`00-domain.md`](00-domain.md); the justification is the *opacity*, never asymmetry, which would make this
circular). A type III factor has **no tracial state**, and a **symmetric self is a tracial state**; therefore
**no self is symmetric** — asymmetry falls out.

**Grounding identification — flagged honestly.** The chain rests on **symmetric self ↔ tracial state** (via
the converse ↔ the modular conjugation `J`, and `φ` tracial ⇔ `σ_t = id`). This is **standard operator algebra,
argued at paper level here — it is _not_ mechanized** (type III modular theory is not in mathlib; see
[`06-type-III-modular.md`](06-type-III-modular.md) Part D). What *is* mechanized is the τ-free cluster above;
the A1-dissolution is a **paper-level consequence of the arena choice**, recorded as such, not asserted as a
formal theorem.

### A2 — co-direction: **parked, open — not deleted**

A2 (that a relation co-directs attention at its two ends, the converse-weight structure) has **not been
load-bearing in any mechanized proof** across the whole exploration. **This is not a refutation.** Its status
is **open**, pending the **recovery theorem** (does the derived self genuinely *satisfy* "a collection of
relations asymmetrically **co-directing** attention"?), where co-direction is a property *of the object being
recovered*. Until recovery is settled, A2 is neither an axiom we use nor a claim we discard — it is an **open
question** ([`10-open-questions.md`](10-open-questions.md)). We do **not** present it as resolved, redundant,
or false; pre-deciding recovery would be the one overclaim this paper refuses.

## The self is derived (not posited)

The self is **never named in the foundation**. It is a **fixed relation of the dynamics** that *arises* and
sustains itself under self-relation (D1). Its existence is a theorem (above); its further structure — the
dynamics (the re-entry raising), selectivity, differentiation, the stability dichotomy, recovery — is explored
and graded by strength in [`03-theorem-debt.md`](03-theorem-debt.md), with the assumed/constructed boundary in
[`07-interface.md`](07-interface.md). What each result *actually invokes* is recorded — that is how the **true
minimal foundation** was found: **one definition, no axioms.**
