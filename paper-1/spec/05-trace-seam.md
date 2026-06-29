# 05 — The trace seam: does `Tr` coincide with `τ`?

> **The single gate.** The I.III exploration ([`03-theorem-debt.md`](03-theorem-debt.md)) found theorems
> 3, 4, 5, 7 all wait on one thing — a measure on `Q`. This page settles whether the **categorical feedback
> trace `Tr`** that D1 requires *is* the **factor trace `τ`** on `Q`. **Verdict: B (connect), conditionally**
> — they are **not** the same structure (A is false on types), they connect through a **dimension measure**
> with an **orthogonality side condition**, and a **residual structural tension** is flagged that could still
> force C downstream. The Lean half is [`../formal/Paper1/TraceSeam.lean`](../formal/Paper1/TraceSeam.lean).

## The two traces (kept distinct — the conflation is the bug)

- **`Tr` — the categorical / feedback trace** D1 requires. It eats a relation with a fed-back wire,
  `A⊗U ⇸ B⊗U`, and returns the looped relation `A ⇸ B`. **Relation-valued.** Self-relation as a loop.
- **`τ` — the factor trace** on the II₁ factor. It eats one element `x ∈ Q` and returns a **number**
  `τ(x) ∈ ℂ`. A measure; unique, faithful, normal — the reason II₁ was chosen.

## Step 1 — types on paper (the cheap discriminator)

**The quantaloid, concretely.** A morphism `R : A ⇸ B` is a `Q`-valued matrix/kernel `R_{a,b} ∈ Q`.
Composition is `(R;S)_{a,c} = ⨆_b R_{a,b} · S_{b,c}` — **join** over the intermediary of the quantale product.
The contraction operation of this arena is **`⨆` (join)**; that is how matrix categories over a quantale add.

**The candidate `Tr`.** For `R : A⊗U ⇸ B⊗U`, looping the `U`-wire, the natural categorical trace contracts
the `U`-diagonal by the arena's contraction — **join**:

```
    Tr^U(R)_{a,b}  =  ⨆_u  R_{(a,u),(b,u)}          ∈ Q        (relation-valued)
```

**What `τ` does, by contrast.** `τ` eats an element of `Q` and returns a number; the trace-mediated
contraction of a diagonal would be

```
    Σ_u τ( R_{(u),(u)} )                              ∈ ℂ        (number-valued)
```

**The discriminator — the types do not line up.** Two independent mismatches, fatal to literal coincidence:

| | categorical `Tr` | `τ`-mediated contraction |
|---|---|---|
| **output type** | a relation (`Q`-valued, `A ⇸ B`) | a number (`ℂ`) |
| **contraction op** | **join** `⨆` (idempotent semilattice) | **addition** `+` (abelian group) |

A loop is a **relation**; a measure is a **number**. The contraction of a loop is by **join** (idempotent:
`x ⊔ x = x`); the contraction of a measure is by **sum** (`x + x = 2x`). These are different operations on
different-typed things. **`Tr` is not `τ`. Verdict A (literal coincidence) fails at type-checking** — exactly
the "half of these questions die at the types" the spec predicted. We did not need Lean for this; the type
table is the whole argument.

**Where this leaves us.** `Tr` exists as a *relation-valued, join-contracted* operation that **never mentions
`τ`**. `τ` is a *separate measure*. The live question becomes **B vs C**: do they *connect* (a bridge relates
the join-contraction to the measure), or *conflict* (no compatible measure exists)?

## Step 2 — the trace axioms (Lean): `Tr` is a real, `τ`-free trace

If `Tr` is a genuine categorical trace **without** `τ`, then D1's feedback is well-defined on the arena and
`τ` is a *separate* layer — the B picture. We verified the trace axioms the join-contraction settles on its
own, in [`TraceSeam.lean`](../formal/Paper1/TraceSeam.lean), each using **only** `[CompleteLattice Q]` (no
`τ`, no product):

- **Vanishing I** — tracing the trivial wire is the identity: `Tr^I(R) = R` (`ptrace_unit`). ✓
- **Vanishing II** — a compound loop is two loops: `Tr^{U⊗V} = Tr^U ∘ Tr^V`, because the join factorises
  `⨆_{(u,v)} = ⨆_u ⨆_v` (`ptrace_prod`). ✓
- **Order-indifference of the loop** (the Fubini/superposing content): the looped indices commute,
  `⨆_u ⨆_v = ⨆_v ⨆_u` (`ptrace_comm`). ✓

**The diagnosis these deliver.** The axioms hold, and **none invokes `τ`** — the feedback trace is built from
**join alone**. This is the decisive Step-2 finding: **`Tr` is a `τ`-free categorical trace.** Therefore D1's
self-relation-as-feedback is real on the arena, and it is **not** the factor measure — confirming A is false
and locating the truth at **B**: `τ` must *connect to* `Tr`, not *be* it.

**What Step 2 did _not_ certify (named, not patched).** The remaining trace axioms — **naturality / sliding**
and **superposing through composition** — involve the quantale **product** `·` (composition on the `A,B`
wires), and so require the value-object to carry a product distributing over `⨆`. On the projection lattice
that product is problematic (see the residual tension below); we did **not** assert these axioms, and did
**not** paper a gap with a `sorry`. They are the part of the seam that is still load-bearing.

## Step 3 — the minimal instance: the loop is a join, not a sum

`ptrace_bool_diagonal` computes `Tr` on the smallest non-trivial self-loop (a 2-element wire `U = Bool`,
diagonal `g`):

```
    Tr(loop) = g(true) ⊔ g(false)            -- a JOIN of the diagonal, on the nose
```

The feedback trace returns the **join** of the diagonal, **not** the sum `g(true) + g(false)`. One worked
instance makes the type analysis concrete: looping produces a relation (a join in `Q`), full stop. A *number*
appears only when a measure is applied.

**The bridge, worked.** `bridge_on_instance` shows exactly how `τ` re-enters: given a **dimension measure**
`dim : Q → ℝ` (the structure `DimensionBridge`) and **orthogonality** of the two diagonal values,

```
    dim( Tr(loop) )  =  dim(g true)  +  dim(g false)        -- join ↦ sum, under Disjoint (g true) (g false)
```

The join becomes a sum **exactly under the orthogonality side condition** `Disjoint (g true) (g false)`. That
equality is the **bridge lemma B requires**, proved on the instance. Drop orthogonality and it is only the
submodular inequality `dim(a ⊔ b) ≤ dim a + dim b` — the bridge holds *conditionally*.

## The verdict: **B (connect), conditionally — with a flagged residual tension**

**B, not A.** `Tr` and `τ` are **different structures**: `Tr` is the relation-valued, join-contracted,
`τ`-free feedback trace (Step 1 types; Step 2 axioms); `τ` is a number-valued measure. They **connect**
through the **dimension function** `dim = τ|_{proj} : Q → [0,1]` — the II₁ trace restricted to projections,
faithful/normal/additive — which turns **orthogonal** joins into numerical **sums** (Step 3). This is the
canonical II₁ structure: continuous dimensions are *why* `Q` was chosen, and they are precisely the bridge.

**The side condition is real.** The bridge is an **equality only on orthogonal diagonals**; in general it is a
submodular inequality. So D1's feedback measured by `τ` is additive exactly when the looped relation's
diagonal pieces are disjoint — a hypothesis the quantitative theorems will have to carry (or discharge).

**The residual tension (why this is B-with-a-C-warning, not clean B).** The value-object must do **two** jobs,
and it is **not yet shown one object does both**:

1. carry the **measure** — natural on the **projection lattice** `Proj(Q)` (where `dim` lives, additive on
   orthogonal joins); and
2. carry the **quantale product** for **composition** `(R;S) = ⨆_b R_{ab}·S_{bc}` — which `Proj(Q)` does
   **not** support (meet of projections is not sup-distributive in a non-distributive orthomodular lattice),
   and which wants a genuine quantale (e.g. Mulvey's `Max(Q)` of closed right ideals).

This is the **"order vs. operator" arena seam (#2)** resurfacing, sharpened: the *measure* and the
*composition* are natural on **different** derived structures of the II₁ factor. If a single value-object
carrying **both** can be exhibited (the projection/ideal structure reconciled with a sup-distributing
product), the verdict is cleanly **B and the gate is open**. If no such object exists, this is where the arena
**reshapes** — the honest path to **C**, localized exactly. The naturality/superposing axioms left unproved in
Step 2 are the same tension wearing its categorical hat.

## Consequence — the gate is **ajar**, and what to attempt first

- **The gate is open enough to proceed.** D1's feedback trace is real and `τ`-free; the measure connects via
  `dim` under orthogonality. The quantitative theorems become **approachable** through `dim`, carrying the
  orthogonality side condition explicitly.
- **Attempt Theorem 3 (sparsity) first.** It is the most direct consumer of `dim`: "strong self-relations are
  few" becomes a statement about the dimension measure of the relations clearing a capacity threshold — a
  counting/density claim in `dim`, now *stateable*. It is also the cheapest test of whether the bridge's
  orthogonality condition is workable in practice.
- **Before leaning on the gate for the headline (Theorem 5), settle the residual tension** — exhibit the one
  value-object carrying both the measure and the composition, or report that none does (C, localized). That is
  the next spec's first task.

**Bottom line.** The shared word "trace" hid two structures; they are **not** one (A false). They **connect**
through the II₁ dimension function under an orthogonality side condition (**B**), proved on a minimal
instance. What remains open — and what could still force the arena to reshape — is whether **one** value-object
carries both the measure and the composition. The gate is **ajar**: enough to attempt sparsity, not yet enough
to bank the headline.

> **Resolution (handoff I.V).** The residual tension above **dissolves** when `Q` is moved to a **type III₁
> factor** ([`06-type-III-modular.md`](06-type-III-modular.md)): a type III factor has **no global trace** at
> all, so the *measure horn* of the conflict is removed — `Tr` stands alone on the lattice, with no `τ` to
> reconcile it with. The I.IV obstruction was the **symptom of forcing a global trace where the arena does
> not admit one**. Quantity is recovered not from a global `τ` but from the **II∞ core** of the Takesaki
> decomposition; see `06`.
