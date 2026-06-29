# 08 — The raising dynamics: deriving A3, and the downstream theorems (gated)

> *The gate.* A3 (generativity / raising) was **demoted** from axiom to theorem-to-derive. The interface work
> (I.VI) instead *assumed* it (`CoDirection`). This page attempts to **discharge** that assumption — derive
> raising from A1 + A2 + D1 — and branches the remaining theorems on the outcome. **Deliverable: the truth per
> theorem (derived / obstructed / collapsed / conditional) with the axioms it invoked. Obstructions are
> results.** Mechanization: [`../formal/Paper1/RaisingDynamics.lean`](../formal/Paper1/RaisingDynamics.lean),
> [`../formal/Paper1/ModularBuild.lean`](../formal/Paper1/ModularBuild.lean).

## Phase 1 outcome — **dynamics DERIVED; the modular-group form REDUCED but conditional**

Not the clean `DERIVED`, not `NO-DYNAMICS`. Precisely:

### 1a — does a non-trivial dynamics arise? **YES, derived, interface-free.**

A self-relation **re-enters itself through the trace** (D1): `reenter S = S ⨾ S` (relating-through-itself).
This is a genuine **monotone** endo-process (`reenterHom`, from `comp_mono`), so by relational Knaster–Tarski
it has a fixed self-relation (`reentry_self_exists`), and that self is **idempotent** (`S ⨾ S = S` —
`reentry_self_idempotent`): a **projection-like** self, the kind the modular structure lives on. Footprint
`[propext, Quot.sound]` — **interface-free** (no modular theory, no global trace).

**Minimal-axiom finding (it continues).** The dynamics' *existence* used **D1 (composition) + completeness
only** — **neither A1 nor A2.** Existence keeps coming for free; the axioms' work is downstream.

**Honest caveat — the selection problem.** The *greatest* fixed point is **degenerate** (`⊤ ⨾ ⊤ = ⊤`, so
`gfp = ⊤`, the total relation). So 1a derives only that **selves are idempotents**; *which* idempotent is a
genuine self is **not** fixed by maximality — it is **selected by the measure** (bounded capacity). **That
selection is Theorem 3 (selectivity).** 1a furnishes the candidates; the measure picks the self. So 1a does
**not** by itself produce *the* self, and the word "raising" (inflationary, capacity-bounded growth) is
*not* yet earned — only "a non-trivial co-direction dynamics with idempotent fixed points." The growth/bound
is quantitative, hence Phase 2.

### 1b — does its reversible core present as a one-parameter group? **Reduced, not discharged.**

Route (spec's): the equilibrium self is **passive** (at the fixed point there is no net raising to extract);
**passivity ⇒ KMS** (Pusz–Woronowicz); KMS + `kms_unique` ⇒ the core is `σ`. Done with the hypotheses checked
against the theorem:

- **Pusz–Woronowicz is now a cited, non-relational interface field** (`passive_kms`: *complete passivity ⇒
  KMS*; Comm. Math. Phys. 58 (1978)). It passes the integrity test (no relational vocabulary).
- **The bridge is reduced** (`coDirectionOfPassive`, `a3_core_is_modular_of_passive`): a **completely passive**
  one-parameter core is forced to be `σ`. So the relational hypothesis shrinks **from** "the self is *KMS* for
  the core" **to** "the self is a *completely passive* equilibrium for the core" — much closer to the
  **proved** fact that the self is a **fixed point** (`TypeIII.self_isEquilibrium`).
- **The residual gap (flagged paper-level):** that the equilibrium fixed point is *completely* passive (PW
  needs *complete* passivity — passivity of all tensor powers — which is strictly stronger than "no work at
  the fixed point"). Verifying it is the one relational input still owed; it is **not** mechanizable without
  the operator structure (type III gap).

### Verdict on the gate

`CoDirection` is **not fully discharged**, but **`NO-DYNAMICS` did not obtain** — the dynamics is real and
derived. So **A3 does _not_ return to the axiom list.** The architecture stands as: **A1 + A2 + D1, with the
co-direction dynamics derived (1a) and its modular-group identification conditional on a flagged complete-
passivity bridge (1b).** The unification `A3 = σ ⊕ arrow` stays **interface-relative and passivity-conditional**
— now on a *smaller, better-located* hypothesis than I.VI's bare KMS assumption. Honest status: **progress, not
closure.**

## Phase 2 — sparsity (3) and differentiation (4)

- **(3) Selectivity / sparsity — OBSTRUCTED (conditional), with a collapse.** Stating "strong self-relations
  are few" needs the **core measure** (`traceN`) *and* a bridge from arena-relations to core elements — the
  same arena↔algebra frontier I.V/I.VI flagged. So it is **not** mechanizable now. **But the I.IV
  orthogonality test resolves conceptually:** 1a shows selves are **idempotents**; an idempotent's genuine
  (non-degenerate) realization is one whose pieces are **disjoint/orthogonal** — exactly the I.IV bridge side
  condition. So **orthogonality is plausibly not an _input_ to sparsity but a _characterization of selfhood_**
  (the genuine self = the bounded, orthogonally-decomposed idempotent). **Recorded collapse (conjectural):**
  *orthogonality ⇔ selectivity*; the side condition I.IV carried is the selfhood criterion itself.
- **(4) Self-differentiation — OBSTRUCTED (conditional); collapses with (3).** "Leading/lagging internal
  structure" needs the per-end rates (the measure). And it is **the same fact** as selectivity: a self is
  sparse **because** its strong sub-relations are few and **differentiated** (asymmetric weights), and
  differentiated **because** capacity is bounded. **Recorded collapse:** (3) and (4) are **one fact** —
  *bounded capacity ⇒ few, differentiated strong relations* — seen as "few" (3) or "unequal" (4).

## Phase 3 — the stability dichotomy (5): **holds by _absence_, not repeller — collapses into type III**

The headline: *the symmetric configuration is unstable; the stable selves are asymmetric.* Type III delivers a
**stronger-but-different** result than "unstable":

- A **type III factor has no normal tracial state** (no trace at all — that is the definition). A state is
  **tracial ⇔ symmetric** (`φ(ab) = φ(ba)`) **⇔ its modular flow is trivial** (`σ_t = id`). Therefore **in
  type III no faithful normal self is symmetric** — every self has a non-trivial modular flow. **Symmetric
  selves do not exist.**
- So "stable selves are asymmetric" holds **because symmetric selves are absent**, not because symmetry is a
  *repeller* in a dynamical flow. **This collapses into the type III choice** (I.V) together with (4): asymmetry
  is not a contingent outcome of the dynamics but a **structural consequence of trace-lessness**.

**Honest split.** The **absence** form (no symmetric self in type III) is a clean consequence of the arena
choice — paper-level (needs "type III ⇒ no tracial state," standard, not in mathlib). The **repeller** form
(symmetry is dynamically unstable, a genuine basin structure) is the **stronger, still-open, falsifiable**
claim — **not** settled, and **not** engineered. The fallback the spec named ("stable differentiation requires
asymmetry") is *subsumed*: in type III, differentiation/asymmetry is forced outright.

## Phase 4 — recovery (7): **conditional; the asymmetry half is now strong**

*The derived fixed self-relation is "a collection of relations asymmetrically co-directing attention."* Inputs,
with honest provenance:

- **"a fixed self-relation"** — **derived** (existence, τ-free) ✓
- **"a collection of relations re-entering / co-directing"** — **derived** (1a, the re-entry dynamics; selves
  are idempotents) ✓, with the *quantitative* co-direction **conditional** (1b passivity bridge).
- **"asymmetrically"** — **strongly grounded** (Phase 3: type III forces non-symmetry) — paper-level but clean.
- **the interpretive step** (formal object ↔ lived phenomenology) — a **`[reading]`**, as always.

**Verdict:** recovery is **conditional** (it consumes the conditional unification), but its **asymmetry half is
now well-grounded** by the type III structure rather than assumed. It is the closing theorem and rightly last.

## Cross-cutting: the minimal axiom set, and the collapses

**Minimal-set tally (what each result actually invoked).**

| Result | A1 | A2 | D1 | interface | note |
|---|---|---|---|---|---|
| Existence | — | — | — | — | completeness only |
| Seam | — | — | — | — | 0 axioms (Lawvere) |
| Re-entry dynamics (1a) | — | — | **✓** | — | D1 + completeness; **no A1/A2** |
| Unification `A3 = σ ⊕ arrow` | (✓, via III) | — | ✓ | **✓** | conditional on 1b passivity |
| Stability/asymmetry (5) | **✓** | — | — | (✓, via III) | A1 = the no-symmetric-self content |

**A2 (co-direction) has still not been load-bearing in any mechanized proof.** Its content is absorbed into
the arena's **converse** (two-endedness) and the **type III** choice (co-direction ⇔ non-tracial ⇔ modular).
Open question for the architecture: **is A2 definitional rather than axiomatic?** Recorded, not forced.

**Collapses found** (the real count is smaller than the list): **(3) ≡ (4)** (selectivity = differentiation =
*bounded capacity ⇒ few, differentiated strong relations*); **(5) collapses into the type III choice + (4)**
(asymmetry is structural, not dynamical); **(1a) feeds (3)** (idempotent candidates, measure selects). So the
live distinct content is: **existence**, **seam**, **the dynamics (1a)**, **the unification (conditional)**,
and **one selectivity/differentiation/asymmetry cluster (conditional)** — plus the open **repeller** form of
(5).

## Bottom line

The demotion of A3 **largely holds**: the co-direction **dynamics is derived** (interface-free), so raising is
not re-axiomatized. What is **not** yet closed is the *quantitative* content — the growth/bound, the selection
of the genuine self among idempotents, and the modular-group identification — all of which route through the
**measure** and a **complete-passivity** bridge that remains paper-level (the type III formalization gap). The
stability dichotomy **collapses into the type III choice** in its *absence* form (symmetric selves don't
exist), with the *repeller* form left as the honest open headline. No green was forced; the obstructions are
the result.
