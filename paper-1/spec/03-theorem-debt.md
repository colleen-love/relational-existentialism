# 03 — The theorem debt: an exploration

> *The deliverable is the **truth** — theorem or obstruction — not a green checkmark.* Each theorem of the
> debt ([`02-axioms.md`](02-axioms.md)) was attempted relationally, to find out **whether it is true** on the
> new arena. This page records, per theorem: **holds / obstructed / collapsed**, the **axioms it actually
> invoked** (how we find the minimal set), and — for obstructions — the **precise blocker**. Nothing was
> forced; the Lean carries no `sorry`.

## Summary

| # | Theorem | Status | Axioms invoked | Lean |
|---|---|---|---|---|
| 1 | **Existence** of a fixed self-relation | **HOLDS** | *completeness only* — neither A1 nor A2 | `Existence.self_exists`, `self_greatest` |
| 2 | **A3 / raising dynamics** | **SPLIT:** order-proxy holds; quantitative **obstructed** | completeness + monotonicity (proxy) | `Frontier.raising_ascends_to_self`, `bounded_by_top` |
| 3 | **Selectivity / sparsity** | **OBSTRUCTED** (statement-level) | — (needs the trace) | — |
| 4 | **Self-differentiation** | **OBSTRUCTED** (downstream of 2) | — | — |
| 5 | **Stability dichotomy** (headline) | **NOT SETTLED** — falsifiable, not built | — | — |
| 6 | **The seam** (reflexive opacity) | **6a HOLDS**; 6b/6c open | **0 axioms** (6a) | `Seam.reflexive_opacity`, `Seam.lawvere` |
| 7 | **Recovery** (the real headline) | **OBSTRUCTED** (downstream of 2) | — | structural skeleton only |

**The one bottleneck.** Every obstructed theorem (2-quantitative, 3, 4, 5, 7) is blocked on the **same**
missing structure: a **trace / measure on `Q`**. The abstract arena gives the *order* (joins, fixed points,
`≤`) for free — enough for existence and the seam — but not the *quantity* (how much weight, how fast it
raises, how many relations clear a threshold). So the real shape of the debt is: **the trace seam is the
gate**; pass it (honestly, via `Q` = the II₁ factor or otherwise) and 2 unlocks 3, 4, 5, 7 in turn.

> **Update (handoff I.IV) — the trace seam settled to _B (connect), conditionally_.** The categorical
> feedback trace `Tr` D1 needs is **not** the factor trace `τ` (different types: `Tr` is relation-valued and
> contracts by **join**, `τ`-free; `τ` is number-valued and contracts by **sum**). They **connect** through
> the II₁ **dimension function** `dim = τ|_proj`, which turns *orthogonal* joins into sums — an **equality
> only under an orthogonality side condition** (submodular otherwise). A **residual tension** is flagged (the
> measure is natural on the projection lattice, the composition wants a quantale — possibly *not the same
> object*), which could still force **C** downstream. Mechanized: [`../formal/Paper1/TraceSeam.lean`](../formal/Paper1/TraceSeam.lean);
> full verdict: [`05-trace-seam.md`](05-trace-seam.md). **The gate is _ajar_:** quantitative theorems are now
> approachable through `dim` (carrying the orthogonality condition) — **attempt Theorem 3 (sparsity) first**.

> **Update (handoff I.V) — the arena moved to type III₁.** `Q` is now the hyperfinite **type III₁ factor**
> (trace-lessness = the limits-of-knowing; [`06-type-III-modular.md`](06-type-III-modular.md)). The I.IV
> residual tension **dissolves** (no global trace to conflict with `Tr`). The `τ`-free results (existence,
> feedback trace, seam) **port unchanged** ([`../formal/Paper1/TypeIII.lean`](../formal/Paper1/TypeIII.lean)).
> **Central finding:** A3's co-direction = the **modular flow `σ_t`** in its reversible core (forced by **KMS
> uniqueness** at the equilibrium self), ⊕ the **dissipative arrow** (Takesaki trace-scaling) — unifying with
> papers 2–4. Operator-level steps are **paper-level** (type III modular theory is not in mathlib). Quantity
> now routes through the **II∞ core**; next: re-ground **Theorem 2's rate** as the core's trace-scaling.

> **Update (handoff I.VII) — the raising dynamics, gated.** Full analysis: [`08-raising.md`](08-raising.md);
> Lean: [`../formal/Paper1/RaisingDynamics.lean`](../formal/Paper1/RaisingDynamics.lean).
> - **Theorem 2 (raising / dynamics) — DYNAMICS DERIVED (interface-free); group-form REDUCED, conditional.**
>   The re-entry process `S ↦ S ⨾ S` (D1) is a non-trivial monotone dynamics with an **idempotent** fixed self
>   (`reentry_self_exists`, `[propext, Quot.sound]`) — using **D1 + completeness only, no A1/A2.** So A3 does
>   **not** return to the axiom list. *But* the greatest fixed point is **degenerate** (`gfp = ⊤`), so the
>   genuine self is **selected by the measure**, not by maximality (→ Theorem 3). The modular-group form is
>   **reduced** from assumed-KMS to assumed-**complete-passivity** (`coDirectionOfPassive`, via the new cited
>   interface field `passive_kms` = Pusz–Woronowicz), leaving one flagged paper-level gap (the fixed point is
>   *completely* passive).
> - **Theorems 3 ≡ 4 — collapsed, conditional.** Selectivity and differentiation are **one fact** (bounded
>   capacity ⇒ few, differentiated strong relations); obstructed pending the core measure + arena↔core bridge.
>   **Collapse test result:** *orthogonality (I.IV) ⇔ selfhood-selection* — the side condition is plausibly the
>   selectivity criterion, not an input.
> - **Theorem 5 — collapses into the type III choice (absence form); repeller form open.** Type III has **no
>   tracial (symmetric) state**, so symmetric selves **don't exist** — "stable selves are asymmetric" holds by
>   **absence**, not as a dynamical repeller (the stronger, still-open, falsifiable form). Not engineered.
> - **Theorem 7 (recovery) — conditional; asymmetry half now strongly grounded** by type III.
> - **Minimal set:** A2 (co-direction) has **still not been load-bearing** in any mechanized proof — open
>   question whether it is definitional. A1 enters via type III (no symmetric self).

> **Update (handoff I.VIII) — self-reference and the arrow (upstream of the self).** Full verdict:
> [`09-arrow.md`](09-arrow.md); Lean: [`../formal/Paper1/Arrow.lean`](../formal/Paper1/Arrow.lean).
> **Verdict: MONOTONE-BUT-NOT-TEMPORAL (sharpened).** Self-reference `reenter S = S ⨾ S` is **irreversible** —
> mechanized **τ-free, no self**: the identity and the swap self-compose to the same relation, so `reenter` is
> **non-injective** (`reenter_not_injective`) — `S` is unrecoverable from `S ⨾ S` (a semigroup, not a group).
> So self-reference creates **a direction** intrinsically and **upstream of the self** (D1 + completeness
> only; no A1, no A2). **But its _orientation_ (which way is the future) is _not_ derivable from
> self-reference alone** — that needs `σ`'s modular/KMS sign (interface), and may **not** be imported
> thermodynamically (no-import discipline honored). Honest headline: *self-reference creates the arrow's
> **irreversibility**, not (by itself) the arrow of time.* **Seam collapse flagged:** the diagonal's
> non-invertibility (arrow) and its untraceability (seam) are plausibly **one fact, two faces** — recorded,
> not engineered.

---

## 1. Existence — **HOLDS**

A monotone co-direction process `Φ` on the complete lattice of self-relations `A ⇸ A` has a **greatest fixed
point** (relational Knaster–Tarski); it is a fixed self-relation, and the *greatest* one — the maximal
sustained structure, the candidate self. `Existence.self_exists` / `self_greatest`.

**Axioms invoked — the finding.** *Only the arena's completeness.* The proof uses **neither A1 (asymmetry)
nor A2 (co-direction)**; footprint `[propext, Quot.sound]`. **Existence is free.** Consequence for the minimal
axiom set: A1 and A2 cannot be justified by existence — they must earn their keep *downstream*, in *which*
fixed relation arises and with what structure. The floor behaves; the arena is sound enough to host a self.

## 2. A3 / the raising dynamics — **SPLIT (order holds; quantity obstructed)**

A3 was demoted to a theorem: a self-relation evolves by **bounded, mutual, asymmetric raising**. Split by what
the arena can express:

- **Order-half — HOLDS.** "Raising" as *being pulled upward by the dynamics* is the relation `R ≤ Φ R`
  (`Frontier.Raising`), and a raising seed **ascends to the self** (`raising_ascends_to_self`, from
  completeness + monotonicity). Lattice-**boundedness is free** (`bounded_by_top`: everything is `≤ ⊤`).
- **Quantitative-half — OBSTRUCTED.** A3's real content is quantitative and **none of it** is expressible on
  the abstract arena:
  - **(2a) capacity bound, derived not dialed** — A3 wants a *finite* ceiling (a bounded trace), so growth is
    a finite achievement, not a climb to `⊤`. Lattice `⊤` is not a capacity bound. **Blocker: `Q`'s trace.**
  - **(2b) asymmetric rates** — "each end raises at its own rate" compares the weights of `R` and `R°`
    numerically. **Blocker: numerical comparison of `Q`-weights (trace).**
  - **(2c) mutual / non-freezable** — "moves only when both ends are live" is a product of the two ends'
    weights vanishing if either is `0`. **Blocker: a multiplicative/positivity structure on `Q`-weights.**

**Verdict on whether A3 is an axiom.** *Deferred, honestly.* A3's derivation is **blocked on the trace
seam**, not **refuted** — we have not shown it irreducible, only that it cannot be *derived or refuted* until
`Q` carries a trace. So A3 stays demoted (a theorem-to-derive) with the derivation **pending the arena seam**,
not returned to the axiom list. *Reporting the blocker is the result.*

## 3. Selectivity / sparsity — **OBSTRUCTED (statement-level)**

"Strong self-relations are few" is a **counting / density** claim — it needs a *measure* of how many relations
clear a capacity threshold. No measure without the trace, so the statement **cannot even be written** on the
abstract arena without smuggling in the open seam. Downstream of Theorem 2's capacity bound. (The archived
`Sparsity`/`SparsityReal` family proved this in the *old budget* framing — `INDEX.md` — which is exactly what
must be re-grounded on *constitutive* capacity once the trace is honest.) **Obstructed, not attempted with a
fake statement.**

## 4. Self-differentiation — **OBSTRUCTED (downstream of 2)**

"The stable self has internal leading/lagging structure" is the relational re-grounding of the archived
`capacity_orders_couplings`; it needs the **per-end rates** of Theorem 2 (2b). Cannot precede 2. **Obstructed.**

## 5. The stability dichotomy — **NOT SETTLED (the falsifiable headline)**

"The symmetric configuration is **unstable**; the stable selves are **asymmetric**." This is the high-risk,
high-reward claim — and it is **explicitly falsifiable**, so it is **reported open, not engineered**. It is a
**dynamical** statement (symmetry a *repeller*), which needs a metric/topology on the space of selves — again
the trace. We did **not** build a construction to force it true; per the discipline, it is to be built *true
or false* once the dynamics (2) exist.

**Honest fallback, recorded in advance.** Should symmetry turn out only **marginal** (not a repeller), the
defensible weaker result is *"stable differentiation requires asymmetry"* (≈ Theorem 4) — weaker, but real.
**Status: obstructed (downstream of 2); verdict deferred to the dynamics; fallback named.**

## 6. The seam — **6a HOLDS; 6b/6c open**

- **(6a) reflexive opacity — HOLDS, 0 axioms, arena-independent.** A self admits no *complete self-model*: if
  any endomap of the value-space is fixed-point-free, there is no point-surjective `A → (A → B)`
  (`Seam.reflexive_opacity`, via `Seam.lawvere`). **Lawvere is Lawvere** — it ported from the archive verbatim
  and depends on **no axioms** and on nothing about `Q`. The seam is the most portable result.
- **(6b) the relational route** — "knowing another is partial self-knowledge, because the other carries an
  irreducible aspect of you" — the epistemic reading of `coupling_not_factor` (non-factoring of the converse).
  **Open:** needs the quantitative converse structure (a relation that provably does not factor through one
  end), which waits on `Q`-weights.
- **(6c) the relational bound** — "you cannot wholly know another's knowing of you" (the surplus is itself
  sealed). **Open:** same blocker.

**Collapse conjecture.** The intent is that 6a/6b/6c are **one irreducibility read three ways**. **Confirmed
for 6a** (proved); the **collapse of 6b and 6c into 6a is not yet shown** — establishing it is itself a target
once the converse weight is quantitative. So the seam is, *so far*, **one proved theorem (6a)** with two
conjectured faces.

## 7. Recovery — **OBSTRUCTED (the real headline, downstream of 2)**

"The derived fixed self-relation **is** a collection of relations asymmetrically co-directing attention" — the
proof that derive-don't-define worked. The **structural skeleton exists**: the derived self is a genuine fixed
self-relation (`Existence.derivedSelf_fixed`), and its converse may differ from it (the seed of asymmetry). But
the **full lived-description match** — "asymmetrically co-directing attention" *quantitatively* — needs
Theorem 2's co-direction. **Obstructed**, and rightly last: everything else serves being able to state this.

---

## What the exploration taught us

**About the minimal axiom set.**

- **Existence needs no axioms beyond the arena** (completeness). A1, A2 did *not* appear. They are not yet
  *shown necessary* — they can only earn their keep in the quantitative downstream, which is gated on the
  trace. So the minimal-set question is **open and honest**: as of now we have *used* zero of {A1, A2} and
  cannot confirm either is load-bearing.
- **A3 is correctly demoted** — its order-proxy is a theorem; its quantitative content is blocked on the
  arena, not on a genuine irreducibility. It does **not** return to the axiom list on this evidence.
- **The debt is smaller than it looks.** Theorems 3, 4, 5, 7 do not have independent obstructions — they
  **all reduce to Theorem 2's trace bottleneck**. Effectively the live debt is: **(1) existence [done],
  (6a) seam [done], (2) the trace-borne dynamics [the gate], and then 3/4/5/7 in its wake.**

**About the arena seams** ([`00-domain.md`](00-domain.md)).

- **Seam 1 (the trace in the quantaloid) is the bottleneck** — confirmed by exploration to be exactly what
  gates the entire quantitative tower. *Highest priority.* The next spec should settle whether the arena
  carries the trace natively (II₁ factor) or must be reshaped.
- **Seam 2 (order vs. operator)** — untested directly, but it is the *same* question wearing another hat: the
  order structure gave existence/seam; whether the *operator/trace* structure matches is what Theorems 2–7
  need. Tied to Seam 1.
- **Seam 3 (`Q` self-similarity)** — untouched; load-bearing for the philosophy, not for any theorem here, as
  predicted. Left to fall out or not.

**Bottom line.** On the new arena, the **floor (existence) and the seam (reflexive opacity) hold cleanly and
cheaply** — existence from completeness alone, the seam from nothing at all. Everything *quantitative* — the
raising dynamics, sparsity, differentiation, the stability dichotomy, recovery — waits on **one** honest piece
of structure, a **trace on `Q`**. That is the real result of the exploration: not a wall, a **gate**, and we
now know exactly where it is.
