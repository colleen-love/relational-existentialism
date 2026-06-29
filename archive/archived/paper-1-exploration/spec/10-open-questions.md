# 10 — Open questions

> *The honest frontier.* What paper one has **not** settled — stated as open, neither claimed nor dismissed.
> These are live; some are falsifiable, some await the formalization frontier (type III modular theory is not
> in mathlib — [`06-type-III-modular.md`](06-type-III-modular.md) Part D).

## 1. A2 / co-direction — does it bite at recovery, or is it redundant?

**A2 (co-direction)** — that a relation directs attention at its *two ends* (the converse-weight structure) —
has **not been load-bearing in any mechanized proof** across the whole exploration (existence, the seam, the
dynamics, the arrow all went through without it; even A1 dissolved without it). **This is not a refutation.**
Its proper test is the **recovery theorem**: does the derived fixed self-relation genuinely *satisfy* "a
collection of relations asymmetrically **co-directing** attention"? Co-direction is a property *of the object
being recovered*, so it can only be load-bearing — or shown redundant — *there*.

- **Open:** is A2 a genuine commitment that bites at recovery, or is it definitionally absorbed into the
  arena's converse (so that "co-direction" adds nothing beyond two-endedness)?
- **Discipline:** we **park** it. Pre-deciding recovery — declaring A2 resolved, redundant, or false — is the
  one overclaim paper one refuses. Until recovery is settled, A2 is an open question, not an axiom we use and
  not a claim we discard.

## 2. The seam–arrow collapse — one diagonal, two faces?

Self-reference (the diagonal `Δ`) is loss-of-information read two ways:

- **irreversibility (the arrow):** `S` is unrecoverable from `S ⨾ S` — the diagonal is **non-invertible**
  (`Arrow.reenter_not_injective`).
- **opacity (the seam):** `S` cannot fully trace the relation that includes it — the diagonal is
  **untraceable** (`Seam.reflexive_opacity`, Lawvere).

**Open:** is the *same* lost information that forbids reversing (the arrow) the *same* that forbids
self-knowledge (the seam)? Both are mechanized as non-invertibility/opacity of the diagonal, but a theorem
exhibiting **one map** witnessing both is not yet written. Plausible collapse — recorded as a **reading**, not
engineered ([`09-arrow.md`](09-arrow.md) Part 4).

## 3. Is the arrow's orientation intrinsic after all?

The earned result is that self-reference gives the arrow's **irreversibility** but not its **orientation**
(which way is the future); orientation currently comes from `σ`'s modular/KMS sign (interface). **Open:**
could the orientation come from the **modular structure itself** — e.g. **Borchers' theorem** / **half-sided
modular inclusions**, where positivity of the generator already distinguishes a direction — rather than being
imported or assumed? If so, the orientation would be intrinsic to the modular flow (still interface-level, but
*derived* there, not posited), tightening the headline. Not attempted here; flagged as the natural next probe.
The **no-import discipline** stands either way: a thermodynamic/low-entropy boundary is **not** an acceptable
source of orientation.

## 4. The stability dichotomy — the dynamical-repeller form

Type III delivers the **absence** form: no tracial (symmetric) state exists, so symmetric selves don't exist,
and stable selves are asymmetric **by absence** ([`08-raising.md`](08-raising.md) Phase 3). **Open and
falsifiable:** the stronger **dynamical** form — that the symmetric configuration is an actual **repeller**
(an unstable fixed point with a genuine basin structure), not merely absent. **Build it true or false; do not
engineer it.** A precise obstruction here is a success.

## 5. The formalization frontier (paper-level → mechanizable)

Several results are **paper-level** only because the substrate is not in mathlib: the **A1 dissolution**
(type III ⇒ no symmetric self), the modular identification `A3 = σ ⊕ arrow`, the Takesaki II∞-core measure,
and the orientation. **Open (engineering):** mechanize the modular-theory interface's fields (Tomita–Takesaki,
KMS, crossed products, Takesaki duality) — a specialist / new-mathlib-development task — to convert the
interface-relative results into outright ones. The boundary is disclosed in
[`07-interface.md`](07-interface.md); this is where it would move.

## 6. The arena bets (load-bearing for the philosophy, not the theorems)

- **`Q` self-similarity** `Q ≅ Q ⊗ M₂` ("relations all the way down") — the deepest bet, left to fall out or
  not ([`00-domain.md`](00-domain.md)).
- **Order vs. operator** — whether the relational/order structure fully matches `Q`'s operator structure;
  partly resolved by the type III choice, the rest paper-level.

---

*Nothing here is hidden in prose elsewhere: the foundation ([`02-foundation.md`](02-foundation.md)) and the
ledger ([`03-theorem-debt.md`](03-theorem-debt.md)) point here for everything open, so the assumed/derived/open
boundary is legible in one place.*
