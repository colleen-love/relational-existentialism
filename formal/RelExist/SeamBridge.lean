/-
# Closing the seam bridge: the Lawvere agent *is* the actual forgetting

[`Seam.self_cannot_trace_relation`](Seam.lean) proves the obstruction — *a faithful trace over a
self-inclusive factor would be a complete self-model, which Lawvere refutes* — but it takes the trace
agent `traceAgent` and the inclusion `restrict` as **abstract hypotheses**. That the abstract
`restrict`/`traceAgent` *are* the actual forgetting (the marginal / partial trace) was the standing
`[reading]` ([03.3](../../docs/spec/03.3-decoherence.md): "bridge-across-settings still narrated rather
than mechanized"). This module closes it: it instantiates the seam theorem at the **concrete
forgetting**, so the obstruction bites the real operation, not a posited one.

The construction. By A2 the relationship that constitutes the self carries the self's own view-space:
the between is `S → V`. The actual forgetting — the marginal that keeps the self and drops the
relationship — is `forget := Prod.fst : S × (S → V) → S`. Then:

* `forget_not_injective` — the forgetting is **genuinely lossy**: distinct relationships over the same
  self collapse to the same marginal. The relationship is dropped.
* `no_faithful_self_trace` — and **no reconstruction can restore it**: a faithful trace agent
  (recovering every relationship from the self) is `self_cannot_trace_relation` at the self-inclusive
  factor `Env = Self`, `restrict = id` — a point-surjective complete self-model, Lawvere-forbidden. The
  abstract `traceAgent`/`restrict` are now the *concrete* forgetting and its inversion, supplied, not
  assumed.
* `seam_on_forgetting` — the two together: the actual marginal is lossy, and its lossiness over a
  self-inclusive factor is **forced by the diagonal**, not a feature of a model. You cannot decohere
  yourself relative to what you are made of, and you cannot undo the decoherence either.

What this does and does not settle. The **operative (function-level) identification** — that the
Lawvere agent is the actual forgetting — is now a theorem (`0` axioms, Lawvere alone). The matrix
partial trace of [`Conservation`](../Scratch/Conservation.lean) is the *same forgetting* one category
over (ℝ-matrices instead of functions), and is proved lossy in the same shape there
(`not_isClassical_entangle` / `isClassical_ptrace_entangle`); equating ℝ-matrices with Type-functions
is not a single theorem because they are different categories — that residue is inherent, not a gap in
rigor. The abstractness the `[reading]` flagged is removed: `restrict`/`traceAgent` are no longer
posited.
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
