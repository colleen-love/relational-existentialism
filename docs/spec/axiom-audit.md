# Axiom Dependency Audit

> *Which of the six commitments are genuine posits, and which are already theorems or
> definitions?* This document turns the bracket tags of [02 — The Axioms](02-axioms.md)
> into a **checked** dependency map: each axiom's status, the Lean name that mechanizes
> it, and its **verified** logical-axiom footprint (`#print axioms`). The conclusion: the
> doctrine reduces to **one discriminating posit** over a standard categorical structure.

---

## Two ledgers, two meanings of "axiom"

"Axiom" is overloaded here, and the audit is mostly the work of separating the two:

1. **Doctrine posits** — the six commitments A1–A6, the philosophy's wagers.
2. **Logical axioms** — Lean's foundational axioms (`propext`, `Classical.choice`,
   `Quot.sound`), what `#print axioms` reports. A result reported as depending on *no*
   axioms is fully constructive and foundation-free in Lean's sense.

"Can the axioms be derived axiom-free?" mixes these. The honest answers differ, so they
are tracked in separate columns below.

---

## The map

| Axiom | Spec tag | Kind | Mechanized as | Lean-axiom footprint (verified) | Reduces to |
| --- | --- | --- | --- | --- | --- |
| **A1** Relation primacy | `structural` | interpretive premise | *realized* by A5 (`bisim` = contextual congruence `≡`) | — (carried by A5) | the reading "an object is its relatings" (Yoneda); becomes A5, not posited twice |
| **A2** Self-relation is feedback | `definitional` | definition | `Trace.selfTrace P := νP` | (inherits A3's) | the choice of `Tr` as the referent of `σ` — no content to derive |
| **A3** To relate is to create | `theorem` | **theorem** | `Trace.{selfTrace_fixed, le_Tr, Tr_fixed, Tr_mono}` | `propext, Quot.sound` | ambient traced/cartesian structure + Knaster–Tarski (Hasegawa–Hyland) |
| **A4** Recursion constitutes the self | `posit` | **posit** (selection only) | `loopR_isEigen_iff`; `two_le_selfCost`; `Attention.sustainedField_{fixed,greatest}` | `propext` (bridge/floor); `propext, Quot.sound` (structural) | **itself** — but only the *selection criterion*; existence and the cost-floor are theorems |
| **A5** Observational identity / the "we" | `theorem given ν` | **theorem** | `We.{bisim_unfold, bisim_coind, bisim_refl, World}` | `propext, Quot.sound` | A1 (identity criterion) + the ν-modality (greatest fixed points) |
| **A6** Knowing vs feeling | `σ-side cartesian` | **theorem** | `Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}`; `KnowingFeeling.{knowing_can_fail_to_close, feeling_is_whole}` | **none** (σ-side + the bit-witness); `propext, Quot.sound` (`feeling_is_whole`) | the cartesian fragment (a fixed-point-free endomap) — a pure diagonal argument |

Reading the third column: of the six, **one** is a posit (A4), one is a definition (A2),
one is an interpretive premise that gets *realized* rather than assumed (A1), and **three
are theorems** (A3, A5, A6). The σ-side of A6 — the Lawvere obstruction, the
formally load-bearing half — is mechanized with a footprint of **zero axioms**.

---

## The minimal base

After the reductions, the irreducible primitives are exactly three, and only the last is
a genuine wager:

1. **The ambient structure** — a traced symmetric monoidal category with a distinguished
   cartesian fragment and a ν-modality (greatest fixed points on a complete lattice /
   final coalgebras). A3, A5, and A6 are theorems *of this structure*.
2. **A1's interpretive stance** — identity is exhausted by contextual behavior ("an object
   is its relatings"). This is not proved; it is the semantics, and A5 realizes it as
   `bisim = ≡`. It is a reading, not an independent sequent.
3. **A4's selection criterion** — that *co-directed recursion under constitutive finiteness*
   is what promotes a fixed point to a self. The existence of the fixed points is A3 +
   Knaster–Tarski; the cost-floor `2 ≤ d·λ` is a theorem (`two_le_selfCost`); **only the
   selection is posited.**

So the doctrine reduces to **one discriminating posit (A4's selection) over a standard
categorical structure**, with the σ-obstruction (A6) a 0-axiom theorem and the shared
world (A5) a theorem of the ν-modality.

---

## Three honest caveats

**1. Relocation is not elimination.** Assuming the ambient structure is a Lean
*hypothesis* (a `structure`/typeclass), not an `axiom`, so theorems proved over it report
"0 axioms." That is legitimate — and is why `Mirror.lawvere` is genuinely axiom-free — but
the structure's *fields are the commitments*, retyped. The reduction moves assumptions
into the definition of the category; it does not conjure them away. Any claim of
"axiom-free" must say *over what structure*.

**2. A4 cannot be derived away — that is the content, not a gap.** Drop A4 and *nearly
everything* models `𝕋` (the triviality pole of the expressivity/triviality dial; see
[03](03-sparsity-conjecture.md)). A theory with zero posits is the empty theory. The goal
was never zero axioms but the **right** one; A4 is it, by design, and the sparsity result
is the cash value of keeping it.

**3. A fully axiom-free self-derivation would contradict A6.** To derive *all* of the
theory's commitments from nothing is to have the system completely ground itself — a
complete self-model, the σ-move. A6 (`Mirror.lawvere`) proves that move is obstructed.
So the theory *predicts its own irreducible posit-remainder*: the base cannot shrink to
nothing. This audit confirms A6 from the outside — the minimal base is non-empty, and
necessarily so.

---

## Verified Lean-axiom ledger

Reproduce with `lake env lean -e '#print axioms <name>'` (or a `#print axioms` command):

| Lean name | Axiom | `#print axioms` |
| --- | --- | --- |
| `RelExist.Mirror.lawvere` | A6 σ | **(none)** |
| `RelExist.Mirror.no_complete_selfModel` | A6 σ | **(none)** |
| `RelExist.Mirror.selfModel_remainder` | A6 σ | **(none)** |
| `RelExist.KnowingFeeling.knowing_can_fail_to_close` | A6 | **(none)** |
| `RelExist.loopR_isEigen_iff` | A4 bridge | `propext` |
| `RelExist.two_le_selfCost` | A4 floor | `propext` |
| `RelExist.Trace.selfTrace_fixed` | A3 | `propext, Quot.sound` |
| `RelExist.Trace.le_Tr` | A3 | `propext, Quot.sound` |
| `RelExist.We.bisim_unfold` | A5 | `propext, Quot.sound` |
| `RelExist.We.bisim_coind` | A5 | `propext, Quot.sound` |
| `RelExist.Attention.sustainedField_fixed` | A4 structural | `propext, Quot.sound` |
| `RelExist.Attention.sustainedField_greatest` | A4 structural | `propext, Quot.sound` |
| `RelExist.KnowingFeeling.feeling_is_whole` | A6 | `propext, Quot.sound` |

The split is structural: the **pure diagonal arguments** (A6 σ-side, the bit-witness) need
*no* axioms; the **lattice/coalgebra results** (A3, A5, A4-structural) carry `propext,
Quot.sound` from mathlib's `OrderHom.gfp` and quotients; the **discrete core** (A4 bridge
and floor over `ℕ`) needs only `propext`.

---

## What would make the reduction fully rigorous

This audit assembles results proved across separate modules. Two steps would turn the
"reduces to one posit" claim into a single machine-checked development:

1. **One `Doctrine` structure.** Bundle the ambient structure (traced SMC + cartesian
   fragment + ν-modality) as a single typeclass, and re-derive A2/A3/A5/A6 *as theorems
   over it* in one file — so the reduction is end-to-end, not cross-referenced.
2. **Independence.** Exhibit models satisfying all commitments but one (especially: a model
   of everything-but-A4 that is the trivial/universal solvent), proving the remaining
   primitives do not silently collapse into each other. Standard axiom-system hygiene, and
   the formal version of "A4 is doing real work."

→ Back to [02 — The Axioms](02-axioms.md) · the discriminating posit's payoff is
[03 — The Sparsity Conjecture](03-sparsity-conjecture.md).
