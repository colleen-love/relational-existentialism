/-
# Paper one's results, relative to the modular interface (handoff I.VI)

Paper one's **novel relational** content, proved **on top of** `ModularInterface` (the cited operator-algebra
substrate). The interface supplies only modular facts; **the identifications are the theorems here**.

**Boundary discipline:**
- The `τ`-free results (existence, feedback trace `Tr = D1`, the seam) need **none** of this — they stay on
  `[CompleteLattice Q]` (`Existence`, `Seam`, `TraceSeam`, `TypeIII`). Most of paper one stands on *less* than
  the interface.
- The relational bridge — *that A3's co-direction presents on `M` as a one-parameter group for which the self
  is a KMS (equilibrium) state* — is a **named hypothesis** (`CoDirection`), **not** an interface field. It is
  the relational input to be *checked*; the conclusion (`= σ`) is *derived* from it, never assumed.
-/
import Paper1.ModularInterface
import Paper1.TypeIII

namespace Paper1

variable {M : Type*}

/-- **The relational bridge — NOT an interface field.** The reversible **core** of A3's co-direction, as it
presents on the algebra `M`, together with the relational equilibrium claim `core_kms`: *the self is a KMS
(thermal-equilibrium) state for that core*. This is the property paper one **checks** (per I.V's KMS test) —
it is an **equilibrium** condition, **not** the conclusion `core = σ` (KMS holds of many dynamics; uniqueness
is what then pins σ). Carrying relational vocabulary, it lives **here**, consumed as a hypothesis — never in
the interface. -/
structure CoDirection (M : Type*) [inst : ModularInterface M] where
  /-- A3's reversible co-direction core, presented on `M`. -/
  core : ℝ → (M → M)
  /-- it is a one-parameter group. -/
  core_oneParam : IsOneParam core
  /-- **the relational equilibrium claim:** the self is KMS for the core (to be checked, not assumed true of σ). -/
  core_kms : inst.KMSfor core

/-- **Unification — reversible half `[proved, relative to the interface]`.** A3's co-direction core **is** the
modular flow `σ`. The interface gives only the *uniqueness* of the KMS dynamics; the **identification** is
this theorem — KMS-uniqueness *forces* the co-direction core to be modular. -/
theorem a3_core_is_modular [inst : ModularInterface M] (cd : CoDirection M) :
    cd.core = inst.sigma :=
  inst.kms_unique cd.core cd.core_oneParam cd.core_kms

/-- **Phase 1b — the bridge reduces from KMS to _passivity_ `[proved, relative to the interface]`.** A
one-parameter core for which the self is **completely passive** yields a `CoDirection` — the KMS claim is
*derived* (Pusz–Woronowicz, `passive_kms`), not assumed. This **shrinks the relational hypothesis** from
"the self is KMS for the core" to "the self is a **passive equilibrium** for the core" — which is far closer to
the *proved* fact that the self is a **fixed point** (`TypeIII.self_isEquilibrium`). The residual gap (that
the equilibrium fixed point is *completely* passive) is the only relational input left, and it is flagged
paper-level in `spec/08-raising.md`. -/
def coDirectionOfPassive [inst : ModularInterface M]
    (core : ℝ → (M → M)) (hgrp : IsOneParam core) (hpass : inst.CompletelyPassive core) :
    CoDirection M :=
  ⟨core, hgrp, inst.passive_kms core hgrp hpass⟩

/-- **The reversible core is `σ`, from passivity alone `[proved, relative to the interface]`.** Chaining the
1b reduction with KMS-uniqueness: a passive one-parameter co-direction core **is** the modular flow. -/
theorem a3_core_is_modular_of_passive [inst : ModularInterface M]
    (core : ℝ → (M → M)) (hgrp : IsOneParam core) (hpass : inst.CompletelyPassive core) :
    core = inst.sigma :=
  a3_core_is_modular (coDirectionOfPassive core hgrp hpass)

/-- **Unification — arrow half `[proved, relative to the interface]`.** The irreversible remainder is the
**trace-scaling** of the core: `τ_N(θ_s n) = e^{−s} τ_N(n)`. A3's raising is the dissipative arrow, read off
the dual flow's non-conservation of the trace. -/
theorem a3_arrow_scales [inst : ModularInterface M] (s : ℝ) (n : inst.Core) :
    inst.traceN (inst.theta s n) = Real.exp (-s) * inst.traceN n :=
  inst.trace_scaling s n

/-- **The self meets the Tomita–Takesaki precondition `[proved, relative to the interface]`.** The
cyclic–separating precondition holds (it is a property of `M` having a faithful normal state — the interface's
`cyclicSeparating` field), so the equilibrium self qualifies for the modular construction. **Derived by
consuming the interface field — not added as a relational axiom.** -/
theorem self_meets_precondition [inst : ModularInterface M] : inst.cyclicSeparating :=
  inst.cyclicSeparating_holds

/-- **The unification, packaged `[proved, relative to the interface]`: `A3 = σ ⊕ arrow`.** The reversible core
is the modular flow, *and* the arrow is the core trace-scaling. -/
theorem a3_is_modular_plus_arrow [inst : ModularInterface M] (cd : CoDirection M) :
    cd.core = inst.sigma ∧
      ∀ (s : ℝ) (n : inst.Core), inst.traceN (inst.theta s n) = Real.exp (-s) * inst.traceN n :=
  ⟨a3_core_is_modular cd, a3_arrow_scales⟩

/-! ## Disclosure demonstration — surfacing the boundary in `#print axioms`

To make the assumed boundary **visible in the verification artifact** (not just the type signatures), we
discharge the interface and the relational bridge as named `axiom`s and apply the headline theorem. Then
`#print axioms disclosure_demo` lists exactly what the result stands on: the assumed interface `discMI` and the
relational bridge `discCD` — nothing hidden. (The real theorems above keep these as *hypotheses*; this section
is purely a disclosure device.) -/
section Disclosure

axiom DiscM : Type
axiom discMI : ModularInterface DiscM
attribute [instance] discMI
axiom discCD : CoDirection DiscM

/-- Disclosure witness. `#print axioms disclosure_demo` ⇒ depends on `DiscM`, `discMI`, `discCD` — the
assumed modular interface and the relational bridge, surfaced. -/
theorem disclosure_demo : discCD.core = ModularInterface.sigma := by
  exact a3_core_is_modular discCD

end Disclosure

end Paper1
