# 03 — Theorems: what follows from the basis

> *Given the axioms **A1–A3** and the definition **D1** ([02](02-axioms.md)), what actually
> follows?* This file holds the three named theorems **T1–T3** and the derived notions; the
> larger bodies of structural results have their own pages, indexed below — so the
> [axioms file](02-axioms.md) holds only what is **assumed** and these hold what is **derived**.

**Status tags**, used on every claim, because the difference matters:

| Tag | Meaning |
| --- | --- |
| `[proved]` | mechanized in Lean (name given); footprint by `#print axioms` |
| `[follows]` | forced by the structure, but not (yet) mechanized |
| `[reading]` | an interpretation the structure invites but does not compel |
| `[open]` | a genuine theorem the prose has claimed but the formalization has **not** established |

The dependency is one-way: **A1, A2, A3, D1 ⟹ T1, T2, T3 ⟹ everything below.**

## The rest of this chapter

The structural results split into four pages:

- [`03.1-sparsity.md`](03.1-sparsity.md) — **the sparsity conjecture**: under a finite attention
  budget, selves are rare. The one place the spec reaches for a quantitative headline theorem;
  the resource-counting core and the topological form are mechanized, the full lift is the
  standing conjecture.
- [`03.2-limits-of-knowing.md`](03.2-limits-of-knowing.md) — **the limits of knowing**: the
  relational typology (self, part, other, collection), the Lawvere obstruction, and the corrected
  map — *to relate is to make the other unknowable; to know fully you must not relate.*
- [`03.3-decoherence.md`](03.3-decoherence.md) — **knowing, attention, and the trace**: what
  knowing does to a relation (decoherence), directed attention as selective decoherence, the
  irreducible floor, and decoherence-is-the-partial-trace — *coherence is conserved, only
  relocated into the relationship you cannot forget.*
- [`03.4-the-self-quantified.md`](03.4-the-self-quantified.md) — **the self quantified**: how much
  of a self ends up in others (the Banach-algebra bound), the quantitative eigenform and its
  uniqueness, and the unification of the order-theoretic and quantitative selves under the
  ν-modality.

---

## T1 — To relate is to create

**Claim.** Iterated self-relation `σ(P) = Tr(P)` (D1) *has* a fixed point; relating produces
a third thing — the eigenform — that need not have pre-existed.

**What is proved.** `[proved]` In the complete-lattice setting,
[`Trace.selfTrace`](../../formal/Scratch/Trace.lean)` := νP` with `selfTrace_fixed`
(`P(νP) = νP`), `le_Tr` (coinduction), `Tr_fixed`, `Tr_mono`. Footprint `propext, Quot.sound`.

**Honest scope.** This is **Knaster–Tarski** — a greatest fixed point of a monotone map on a
complete lattice. It is *not* the Hasegawa–Hyland trace↔Conway-operator bijection (the Conway
identities are not verified), and a gfp existing is generic to *every* monotone operator. So
"to relate is to create" rests, formally, on "monotone maps have greatest fixed points." The
discriminating content — that the created selves are *rare* — is not here; it is sparsity
([03.1](03.1-sparsity.md)).

---

## T2 — Observational identity and the "we"

**Claim.** `≈ := νΘ` is the greatest bisimulation; the shared world is `𝔼 := D/≈`; and `𝔼`
has an **irreducible seam** (no master perspective).

**What is proved.** `[proved]` [`We.bisim`](../../formal/Scratch/We.lean)` := νΘ` with
`bisim_unfold` (`Θ≈ = ≈`), `bisim_coind` (coinduction), `bisim_{refl,symm,trans}` (an
equivalence), and `World := D/≈` (the quotient). Footprint `propext, Quot.sound`.

**The seam, now partly earned.** `[proved]` The "irreducible seam" — that there is no master
perspective on a whole one belongs to — is the Lawvere obstruction under self-inclusion:
[`Relating.self_inclusive_unmodelable`](../../formal/RelExist/Relating.lean) (0 axioms). No
member of a collection holds a complete model of the collection that contains it. (See
[03.2 — the corrected map](03.2-limits-of-knowing.md) — this is where T2's seam and T3's
remainder turn out to be one fact, and where it reaches the *other* too, through the shared
between.)

**Still open.** `[open]` That `≈` **coincides with the contextual congruence `≡`** of A2
("behavioral equivalence = greatest bisimilarity") — a context-lemma / full-abstraction
result — is asserted by the doctrine but **not mechanized**: there is no `≡` in the Lean and
no theorem connecting the two. Likewise the *full naturality* of the no-master-section claim
(Property "T2.1") beyond the point-surjective case. These are real targets, not done deals.

---

## T3 — Knowing vs feeling

**Claim.** Knowing (the σ-move, an endomap `D → D`, cartesian) is Lawvere-obstructed and
leaves a remainder; feeling (the `≈`-relation, one type-level up) is not of the kind that
obstruction touches.

**What is proved.** `[proved, 0 axioms]` The σ-side is genuine and fully constructive:
[`Mirror.lawvere`](../../formal/RelExist/Mirror.lean), `no_complete_selfModel`,
`selfModel_remainder`, and [`KnowingFeeling.knowing_can_fail_to_close`](../../formal/Scratch/KnowingFeeling.lean),
`no_complete_boolModel`. Knowing is structurally partial — the contrapositive of a one-line
diagonal.

**Honest scope of the asymmetry.** The feeling side is `feeling_is_reflexive` `[proved]` —
`≈` is reflexive (an equivalence). The real asymmetry is **type-level**: knowing has type
`D → D`, against which the diagonal `g a a` runs; feeling has type `D → D → Prop`, against
which there is no diagonal to run — the obstruction does not typecheck. We do **not** claim
"feeling is whole / global / has no remainder": no absence-of-obstruction is proved, and a
universal negative cannot follow from one positive property. *Knowing is obstructed; feeling
is simply not the kind of arrow that obstruction applies to.* That is the earned claim.

The full unfolding of T3 — what knowing *does* to a relation, and why the self can never
completely know itself — is [03.3](03.3-decoherence.md).

---

## Derived notions

- **Self / eigenform** — a member of `Stab_R` (A3); a fixed point of funded, deep self-relation.
- **Distributed self** `[reading]` — for `e ∈ Stab_R`, its `≈`-image in `𝔼`; it persists in
  `≈`-neighbours on the timescale of their returning, even after `e`'s own loop opens. Quantified
  in [03.4](03.4-the-self-quantified.md).
- **Birth / death** `[follows]` — a fresh fixed point forced into being already coupled (T1 +
  A3) / the loop `loop_R(e) = e` ceasing to hold as funding withdraws (A3 negated).

---

→ Back to [02 — The Axioms](02-axioms.md) · onward to [03.1 — Sparsity](03.1-sparsity.md),
[03.2 — The Limits of Knowing](03.2-limits-of-knowing.md),
[03.3 — Decoherence and the Trace](03.3-decoherence.md),
[03.4 — The Self Quantified](03.4-the-self-quantified.md) · the functorial semantics are
[04](04-functorial-semantics.md).
