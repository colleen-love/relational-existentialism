/-
# Closing bridge A of the seam: the Lawvere agent is a *supplied* forgetting, not a posited one

[`Seam.self_cannot_trace_relation`](Seam.lean) proves the obstruction — *a faithful trace over a
self-inclusive factor would be a complete self-model, which Lawvere refutes* — but it takes the trace
agent `traceAgent` and the inclusion `restrict` as **abstract hypotheses** (bridge A), and was read as
biting the quantum partial trace specifically (bridge B). This module closes **A only**: it
instantiates the seam theorem at a **concrete set-level forgetting**, so the abstract maps are
supplied, not posited. It does **not** close B (the obstruction on the actual `ptrace`/`dephase`) —
see "Honest scope" below; that is open research, not a residue.

The construction. By A2 the relationship that constitutes the self carries the self's own view-space:
the between is `S → V`. The actual forgetting — the marginal that keeps the self and drops the
relationship — is `forget := Prod.fst : S × (S → V) → S`. Then:

* `forget_lossy` — the forgetting is **genuinely lossy**: distinct relationships over the same
  self collapse to the same marginal. The relationship is dropped. (This part is trivial — projection
  non-injectivity.)
* `no_faithful_self_trace` — and **no reconstruction can restore it**: a faithful trace agent
  (recovering every relationship from the self) is `self_cannot_trace_relation` at the self-inclusive
  factor `Env = Self`, `restrict = id` — a point-surjective complete self-model, Lawvere-forbidden. The
  abstract `traceAgent`/`restrict` are now the *concrete* forgetting and its inversion, supplied, not
  assumed.
* `seam_on_forgetting` — the two together: the actual marginal is lossy, and its lossiness over a
  self-inclusive factor is **forced by the diagonal**, not a feature of a model. You cannot decohere
  yourself relative to what you are made of, and you cannot undo the decoherence either.

**Honest scope — this closes one of two bridges, and is not new mathematics.** The `[open]` held two
claims, and only the first is settled here.

* **Bridge A (closed).** The seam theorem posited its trace agent and inclusion abstractly; A is that
  these are the *actual* forgetting. Closed: `forget := Prod.fst`, `restrict = id`, `Env = Self`. But
  note what A *is* — `forget_lossy` is projection non-injectivity (trivial), and
  `no_faithful_self_trace` is `self_cannot_trace_relation` **specialized** to `Env = Self`, i.e.
  Lawvere on the function space `S → V`. So A is "the seam on a **set-level** forgetting": the existing
  obstruction at a concrete instance, **not new mathematics**. It removes a real referee objection (the
  load-bearing map was assumed), nothing more.
* **Bridge B (open — the candidate-novel result).** That the obstruction bites the **quantum** partial
  trace `ptrace`/`dephase` of [`Conservation`](../Scratch/Conservation.lean) /
  [`MatrixModel`](../Scratch/MatrixModel.lean) — the one producing `isClassical_ptrace_entangle` — is
  **not** closed here, and is **not** an "inherent residue." It is remaining research. It is *not*
  closeable in `matTracedSMC` directly: finite-dimensional, so by Cantor there is no reflexive object
  (no point-surjective `A → [A,B]`), and Lawvere's diagonal cannot be set up there non-vacuously.
  Closing B needs one of: **(1)** a traced/compact category that *has* reflexive objects —
  domain-theoretic / GoI models where `D ≅ [D→D]` — where Lawvere genuinely runs non-cartesianly; or
  **(2)** grounding the quantum-side obstruction in **no-broadcasting** (`Compact.no_cloning`,
  `Decoherence.defectSq_plus_pos`), the compact-closed *face of the same firewall* (`Compact.collapse`)
  whose cartesian face is Lawvere — which does bite the real `ptrace`/`dephase`, but is a distinct
  obstruction unified with the seam via the firewall, not Lawvere inside the quantum fragment. Either
  is a genuine theorem; neither is done.
-/
import RelExist.Seam

namespace RelExist.SeamBridge

open RelExist.Seam RelExist.Mirror

universe u v
variable {S : Type u} {V : Type v}

/-- The **relationship** that constitutes the self (A2: a part of you is the relation, which carries
how you are viewed): the between is `S → V`, the self's own view-space. The actual forgetting — the
marginal / partial trace — keeps the self and drops this relationship. -/
def forget : S × (S → V) → S := Prod.fst

/-- A **faithful trace agent**: a reconstruction of the forgotten relationship from the self alone,
realizing *every* relationship (point-surjective). This is precisely the abstract `traceAgent` of
`self_cannot_trace_relation` at the self-inclusive factor (`Env = Self`, `restrict = id`) — the
environment you would trace out is, by A2, a copy of you. -/
def FaithfulTrace (account : S → S → V) : Prop := PointSurjective account

/-- **The forgetting is genuinely lossy.** Distinct relationships over the same self collapse to the
same marginal — two joints `forget`-equal yet unequal: the residue dropped is the whole relationship. -/
theorem forget_lossy (s : S) {r₁ r₂ : S → V} (h : r₁ ≠ r₂) :
    ∃ p q : S × (S → V), forget p = forget q ∧ p ≠ q :=
  ⟨(s, r₁), (s, r₂), rfl, fun he => h (congrArg Prod.snd he)⟩

/-- **The bridge, closed.** Instantiating the seam theorem at the self-inclusive factor (`Env = Self`,
`restrict = id`): no faithful trace agent over the self-constituting relationship exists. The abstract
Lawvere `traceAgent`/`restrict` are now the *concrete* forgetting and its inversion — supplied, not
posited. -/
theorem no_faithful_self_trace (neg : V → V) (hneg : ∀ v, neg v ≠ v) :
    ¬ ∃ account : S → S → V, FaithfulTrace account :=
  self_cannot_trace_relation (Self := S) (Env := S) (View := V) neg hneg
    (fun h => h) (fun h => ⟨h, rfl⟩)

/-- **The seam, on the actual forgetting.** The marginal `forget` is necessarily lossy
(`forget_not_injective`), and no faithful reconstruction can restore it — that would be a complete
self-model, which Lawvere forbids (`no_faithful_self_trace`). So the partial trace's lossiness over a
self-inclusive factor is a theorem of the diagonal on the *concrete* forgetting, not a reading. -/
theorem seam_on_forgetting (neg : V → V) (hneg : ∀ v, neg v ≠ v)
    (s : S) {r₁ r₂ : S → V} (h : r₁ ≠ r₂) :
    (∃ p q : S × (S → V), forget p = forget q ∧ p ≠ q) ∧
      ¬ ∃ account : S → S → V, FaithfulTrace account :=
  ⟨forget_lossy s h, no_faithful_self_trace neg hneg⟩

end RelExist.SeamBridge
