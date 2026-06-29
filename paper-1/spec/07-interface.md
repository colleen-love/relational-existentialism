# 07 — The modular interface: the assumed / constructed boundary

> *Every formalization stands on assumptions somewhere — mathlib itself rests on `propext`,
> `Classical.choice`, `Quot.sound`. The only honest questions are **where** the line is and **whether it is
> visible.* This page draws paper one's line **high but legible**: a clean, cited **interface** captures the
> established Tomita–Takesaki / modular substrate as assumed axioms, and paper one's **novel relational**
> results are **proved on top of it** — fully mechanized relative to that named floor. Interface:
> [`../formal/Paper1/ModularInterface.lean`](../formal/Paper1/ModularInterface.lean); results:
> [`../formal/Paper1/ModularBuild.lean`](../formal/Paper1/ModularBuild.lean).

## The integrity gate (the whole point)

The interface may assume **only the operator-algebra substrate** — facts a Tomita–Takesaki textbook states
*without ever mentioning relations or selves*. It must **never** assume anything **relational** (not that a
self exists, not that A3 is the modular flow, not the unification). If a relational claim were built into the
interface, we would have **assumed our conclusion** — the one fatal error.

**The test each interface field passes:** *would a Tomita–Takesaki textbook state this without using the words
"relation," "self," "attention," or "co-direction"?* **Audit result: every field passes.** The field
signatures are purely operator-algebraic:

```
sigma, sigma_oneParam, KMSfor, sigma_kms, kms_unique,
cyclicSeparating, cyclicSeparating_holds, Core, traceN, theta, theta_oneParam, trace_scaling
```

— no field name or type contains "self," "relation," "attention," or "co-direction" (grep-audited). The
relational content (`CoDirection`, the unification) lives in `ModularBuild.lean`, **consuming** the interface
as a hypothesis and **proving** the relational conclusion.

## The boundary, made visible in the artifact

`#print axioms` on the headline results (recorded from the build):

| Theorem | `#print axioms` | Reading |
|---|---|---|
| `a3_core_is_modular` | `[propext, Classical.choice, Quot.sound]` | the relational derivation adds **no hidden axioms**; the interface is a **typed hypothesis** `[ModularInterface M]`, visible in the signature |
| `a3_is_modular_plus_arrow` | `[propext, Classical.choice, Quot.sound]` | same — `A3 = σ ⊕ arrow` is proved, the dependency is the visible binder |
| `disclosure_demo` | `[propext, Classical.choice, Quot.sound, Paper1.DiscM, Paper1.discMI, Paper1.discCD]` | discharging the interface (`discMI`) and the relational bridge (`discCD`) as named axioms **surfaces them in the artifact** — exactly what is assumed, nothing hidden |
| `self_exists` (τ-free) | `[propext, Quot.sound]` | a τ-free result **does not acquire** the interface — most of paper one stands on *less* |

The honest Lean idiom for "proved relative to an assumed substrate" is the **typed hypothesis**
`[ModularInterface M]`: it appears in every headline signature, and `#print axioms` confirms no *additional*
axiom is smuggled in. The `disclosure_demo` makes the same boundary vivid by surfacing the discharged
interface and bridge as axiom names.

## The disclosure table — fact / assumed-or-constructed / citation

**Constructed, τ-free (need _nothing_ from the interface)** — stand on `[CompleteLattice Q]` alone:

| Fact | Status | Lean |
|---|---|---|
| Existence of a fixed self-relation | **constructed** (`[propext, Quot.sound]`) | `self_exists` |
| Feedback trace `Tr = D1` | **constructed** (τ-free) | `TraceSeam.ptrace` (+ axioms) |
| The seam (reflexive opacity) | **constructed** (0 axioms) | `Seam.reflexive_opacity` |
| The self is an equilibrium | **constructed** (τ-free) | `TypeIII.self_isEquilibrium` |

**Assumed — the modular substrate (operator algebra; standard; cited; unmechanized here):**

| Fact | Status | Citation |
|---|---|---|
| Modular automorphism group `σ_t` (one-parameter group of `*`-autos) | **assumed** | Takesaki I, Thm VI.1.19 |
| The KMS condition; `σ` is KMS for the state | **assumed** | Haag–Hugenholtz–Winnink; Bratteli–Robinson II, Prop 5.3.7 |
| **Modular uniqueness:** a KMS one-parameter group **= σ** | **assumed** | Takesaki II, Thm VIII.1.2; Bratteli–Robinson II, Thm 5.3.10 |
| Cyclic–separating precondition (faithful normal state) | **assumed** | Takesaki II, Ch. VI (GNS standard form) |
| Takesaki II∞ core, semifinite trace, dual flow, **trace-scaling** `τ_N∘θ_s = e^{−s}τ_N` | **assumed** | Takesaki II, Thm XII.1.1; Connes' classification |

**Constructed _on top of_ the interface (proved, relative to it):**

| Fact | Status | Lean |
|---|---|---|
| The self meets the cyclic–separating precondition | **constructed** (consumes the interface field, not a new axiom) | `self_meets_precondition` |
| **Unification, reversible half:** A3's co-direction core **is** `σ` | **constructed** (via KMS-uniqueness) | `a3_core_is_modular` |
| **Unification, arrow half:** the remainder **is** the trace-scaling | **constructed** | `a3_arrow_scales` |
| **`A3 = σ ⊕ arrow`** | **constructed** | `a3_is_modular_plus_arrow` |

**Assumed — the one _relational_ bridge (paper-level; the open frontier, flagged):**

| Fact | Status | Where |
|---|---|---|
| A3's co-direction **presents** on `M` as a one-parameter group for which the self is a **KMS** (equilibrium) state | **assumed as a hypothesis** (`CoDirection`), **not** an interface field; it is the relational input *to be checked* (I.V's KMS test), **not** the conclusion `= σ` | `ModularBuild.CoDirection` |

> **Why the bridge is not smuggling.** `core_kms` asserts the self is **KMS** (an equilibrium condition) for
> the co-direction core — a property *of many dynamics*. It is **strictly weaker** than the conclusion
> `core = σ`; the *content* of the theorem is that modular **uniqueness** turns that equilibrium property into
> the identity. The bridge is carried as a **theorem hypothesis** in the relational file, never as an
> operator-algebra axiom. Its full discharge — constructing the arena↔algebra presentation — is the
> paper-level frontier I.V flagged (type III modular theory is not in mathlib).

## What "fully mechanized" means here

Paper one's relational results are **fully mechanized _relative to the modular-theory interface_** — the
qualifier is load-bearing and is stated wherever the interface is used. The τ-free core (existence, `Tr`, the
seam) is mechanized **absolutely** (no interface). The modular substrate is **assumed**, standard, and cited;
it is *not* mechanized here (we do not mechanize Tomita–Takesaki, and we do not PR to mathlib). The boundary
is visible in the type signatures, in `#print axioms`, and in this table — rigor through an honest boundary,
not an impossible completeness claim.
