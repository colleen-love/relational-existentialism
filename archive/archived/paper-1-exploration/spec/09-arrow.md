# 09 — Self-reference and the arrow of time (isolated, upstream of the self)

> *The claim under test.* Time is the **reversible** modular flow a state generates (`σ`, a one-parameter
> *group*; thermal-time hypothesis, interface-level, explicitly **direction-free** — Connes–Rovelli). The
> **arrow** (its direction) is tested as the intrinsic irreversibility of **self-reference** — the diagonal
> `reenter S = S ⨾ S` (D1 + completeness, **no self**). **Verdict: MONOTONE-BUT-NOT-TEMPORAL, sharpened —
> self-reference creates the arrow's _irreversibility_ intrinsically and upstream of the self, but not, by
> itself, its _orientation_ (which way is the future); pinning that to time needs `σ`'s modular/KMS structure,
> and may _not_ be imported.** Lean: [`../formal/Paper1/Arrow.lean`](../formal/Paper1/Arrow.lean).

## The two pieces, kept distinct

- **Time = `σ` (reversible).** A state generates the modular flow, a one-parameter **group** `σ : ℝ → Aut`,
  fully reversible. Connes–Rovelli are explicit: this gives the *flow*, **not the direction**. Supported
  background (TTH, interface), **not** the thing proved.
- **Arrow = `reenter` (the candidate, irreversible).** `reenter S = S ⨾ S` (D1): self-reference, the diagonal.
  A monotone semigroup with idempotent fixed points, on **D1 + completeness only** — no A1, no A2, no self.

## Part 1 — `reenter` is irreversible `[proved, τ-free, upstream of the self]`

On the canonical relational model (`Q = Prop`, the allegory `Rel`; value product = `∧`), self-composition is
**non-invertible**:

- the **identity** `idR` and the **swap** `swapR` are **distinct** relations (`idR_ne_swapR`), yet **both
  self-compose to the identity** (`reenter_idR`, `reenter_swapR`): going-and-coming-back is standing still, and
  the swap's *direction* is destroyed by squaring;
- hence `reenter` is **not injective** (`reenter_not_injective`): `S` **cannot be recovered** from `S ⨾ S`.
  Self-composition is **information-losing**; there is **no way back**.

This is the **precise, intrinsic sense in which self-reference is directional** — established with **no `σ`, no
self, no global trace** (footprint `[propext, Classical.choice, Quot.sound]`; the upstream-of-self audit
confirms no selfhood/interface lemmas are used). `σ` is a *group* (invertible, `t ∈ ℝ`); `reenter` is a
*semigroup* (forward only, no inverse). **The non-invertibility is real and intrinsic.**

## Part 2 — the load-bearing identification: does `reenter`'s direction = time's direction?

Two halves, and they come apart:

**(i) Irreversibility — YES, and it matches `σ`'s complement.** `reenter` is forward-only exactly where `σ` is
bidirectional; structurally it is the **non-invertible complement** of the reversible group — the same role as
the dissipative `⊕ arrow` of `A3 = σ ⊕ arrow` (I.VI) and the Takesaki trace-scaling (I.V). The *type* matches:
group + semigroup, reversible + irreversible. So self-reference supplies the **fact that there is an arrow** (a
genuine forward-only structure), intrinsically.

**(ii) Orientation — NOT from self-reference alone.** `reenter`'s direction is an **information/order**
direction: `S ⨾ S` loses information, and the orbit flows **toward the idempotent** (equilibrium). To call
*that* direction the **future** is to assert *information-loss = forward-in-time* (equivalently,
*toward-equilibrium = future*) — which is precisely the **thermodynamic / equilibration arrow**. Self-reference
gives the *gradient*; it does **not**, by itself, say the gradient points at the future. That identification
needs either:

- the **modular/KMS orientation** (the KMS analytic strip is one-sided — the sign of `β` distinguishes a
  preferred direction; interface-level, supported by TTH), **or**
- an **imported** thermodynamic arrow (a low-entropy boundary, an entropy-increase postulate) — **forbidden**
  by the no-import discipline (Part 3).

So the honest split: **irreversibility is intrinsic to self-reference (Part 1, mechanized); orientation is
not (it needs `σ`/KMS, the interface).** Hence **MONOTONE-BUT-NOT-TEMPORAL** — self-reference creates *a*
direction (a forward-only, information-losing gradient toward equilibrium), and that direction is *available*
to be the arrow of time, but **identifying it with time's future is supplied by `σ`'s modular structure, not
derived from the diagonal alone.** Not the clean HOLDS; not NEEDS-SELF (no self/selectivity was invoked — the
idempotent here is a structural attractor, not the self-qua-self).

## Part 3 — the no-import discipline (honored)

Nothing thermodynamic was imported: **no low-entropy boundary, no entropy-increase postulate, no chosen KMS
orientation, no external arrow** (audited — grep clean in `Arrow.lean`). The irreversibility of Part 1 is
derived purely from the diagonal's information loss. **And the finding of Part 2(ii) is exactly the
discipline's payoff:** the orientation *cannot* be obtained from self-reference without an external tiebreaker
(or `σ`'s KMS sign), and **we say so** rather than smuggling one in. The arrow's *existence* is
self-referential and intrinsic; its *orientation* is not — reported, not forced.

## Part 4 — the seam connection: one diagonal, two faces `[flagged; not engineered]`

Self-reference is also where the **seam** lives (Lawvere: the diagonal that cannot be traced — opacity). The
two read as **one structure, twice**:

- **irreversibility (the arrow):** `S` cannot be recovered from `S ⨾ S` — the diagonal (self-*composition*)
  is **non-invertible** (`reenter_not_injective`).
- **opacity (the seam):** `S` cannot fully trace the relation that includes it — the diagonal
  (self-*reference*) is **untraceable** (`Seam.reflexive_opacity`, Lawvere).

Both are the **diagonal `Δ` losing information**: the lost information that forbids **reversing** (no way back
= the arrow) is the same lost information that forbids **knowing yourself** (no way to trace yourself = the
seam). **Plausible collapse: the arrow and the seam are one fact — self-reference's information loss — read as
*irreversibility* and as *opacity*.** Recorded as present; **not engineered** (a full proof that the *same*
map witnesses both is left open — both are mechanized as non-invertibility/non-surjectivity of the diagonal,
but their identification is a structural reading here, not a theorem).

## Verdict, status, and what is mechanized

**MONOTONE-BUT-NOT-TEMPORAL (sharpened):**

- **Mechanized, τ-free, upstream of the self:** self-reference is **irreversible** (`reenter` non-invertible;
  information-losing; semigroup not group). *Self-reference creates a direction.* ✓
- **Paper-level, interface-relative:** that this direction is **the arrow of time** — its *orientation* toward
  the future — is **not** derivable from self-reference alone; it is supplied by `σ`'s modular/KMS orientation
  (TTH, interface), **not** importable thermodynamically.
- **The honest headline:** **"self-reference creates the arrow's irreversibility"** — *not* the stronger
  "self-reference creates the arrow of time," which would require the orientation to come from the diagonal
  too (it does not). Stated at the strength it earns, no more.

| Claim | Status | Axioms / interface |
|---|---|---|
| `reenter` non-invertible (irreversibility) | **mechanized**, τ-free, no self | `[propext, Classical.choice, Quot.sound]` |
| irreversibility = `σ`'s non-invertible complement (type match) | paper-level | interface (`σ` a group) |
| orientation = time's future | **NOT derived** (needs `σ`/KMS; not importable) | the precise gap |
| arrow ≡ seam (one diagonal, two faces) | flagged collapse, **not engineered** | both mechanized as diagonal non-invertibility; identification is a reading |

**Cross-cutting (minimal set):** Part 1 used **D1 + completeness only** — **no A1, no A2, no self, no
interface.** The arrow's irreversibility sits *below* everything: it is the bare diagonal. (A2 *still* not
load-bearing.) The orientation is where the interface enters — and that boundary is the result.
