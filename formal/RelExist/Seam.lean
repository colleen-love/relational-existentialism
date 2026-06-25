/-
# The seam: the trace a self cannot take

Two modules have been narrating one fact between them, and this ties them into a single theorem.

* [`Scratch/Conservation.lean`](../Scratch/Conservation.lean) shows **decoherence *is* the partial
  trace**: forgetting the environment makes a coherent global state look classical. The collapse
  lives entirely in the act of *forgetting a subsystem*.
* [`RelExist/Relating.lean`](Relating.lean) shows a self **cannot completely view a whole it is part
  of** (Lawvere's diagonal): `self_inclusive_unmodelable`, `related_other_unmodelable`,
  `no_complete_view`.

The seam between them: **who takes the trace?** To forget the environment *faithfully* — to sum it
out, to hold the classical reduction as a complete account — the tracing agent must possess a
complete account of the environment (it ranges over every configuration). So the question of
whether a self can decohere itself is the question of whether it can completely view the factor it
is tracing out. And by **A2** the relationship *is* part of the self — the sustained self
`νΦ_c` is supported on the between (`Attention.closed_loop_registers`), a part of you is a part of
the other. The factor the self would trace out *contains the self*.

Hence the split, exactly mirroring Relating's one-knowable / three-unknowable map:

* **`disjoint_trace_exists`** — over a factor the self is *not* part of, the complete tracing
  account exists (trivially). You can decohere yourself relative to what you are not.
* **`self_cannot_trace_relation`** — over the relationship (self-inclusive), the account would be a
  complete self-model: *the partial-trace agent over a self-inclusive factor IS a complete
  self-model*, which Lawvere forbids. You cannot decohere yourself relative to what you are made of.
* **`self_cannot_view_relation`** — the same seam in the doctrinal A2-closure form (via
  `no_complete_view`): the complete relationship-view the trace requires does not exist, because
  viewing the relationship is relating to it, registering the viewer inside the viewed.

So from inside, the coherent global (`Conservation.not_isClassical_entangle`) is **real but
unviewable**, and the classical reduction (`Conservation.isClassical_ptrace_entangle`) is the
artifact of a forgetting **the self cannot perform on itself**. *Locally* a relation decoheres;
*globally* it never does — and now the reason a self is stuck with the local view is a theorem: the
global view is the one trace it cannot take. 0 axioms, on Lawvere's diagonal alone.
-/
import RelExist.Relating

namespace RelExist.Seam

open RelExist.Relating RelExist.Mirror

universe u v w

/-- **The trace a self *can* take — over a relationless factor.** If the environment shares
nothing with the self (a factor the self stands entirely outside of), a complete tracing account
exists: the cheapest possible — let the vantage points *be* the accounts. Decohering yourself
relative to what you are not part of is unobstructed. The mirror of `Relating.disjoint_modelable`:
knowability — and here, self-tracing — is reserved for the *relationally empty* limit. -/
theorem disjoint_trace_exists {Env : Type u} {View : Type v} :
    ∃ (Vantage : Type (max u v)) (account : Vantage → Env → View),
      ∀ h : Env → View, ∃ p, account p = h :=
  ⟨Env → View, id, fun h => ⟨h, rfl⟩⟩

/-- **The trace a self *cannot* take — over the relationship it is part of.** Read Conservation's
partial trace as the agent that forgets the environment. To take it faithfully the self must hold a
complete account `traceAgent : Self → Env → View` realizing *every* environment-view — that is what
"sum out the relationship" requires. But the relationship is self-inclusive: by **A2** the self is a
part of it, so a complete account of the relationship restricts to a complete account of the self
(`restrict` surjective — the restriction along the inclusion `Self ↪ Env` of the self's
constitution in the between). Then `restrict ∘ traceAgent : Self → (Self → View)` is a
**point-surjective complete self-model**, and Lawvere's diagonal (`neg`, a fixed-point-free "always
a discrepancy") refutes it. *The partial-trace agent over a self-inclusive factor is a complete
self-model.* You cannot forget the part of the world that is you. -/
theorem self_cannot_trace_relation {Self : Type u} {Env : Type v} {View : Type w}
    (neg : View → View) (hneg : ∀ x, neg x ≠ x)
    (restrict : (Env → View) → (Self → View))
    (hrestrict : ∀ h : Self → View, ∃ k, restrict k = h) :
    ¬ ∃ traceAgent : Self → Env → View, ∀ h : Env → View, ∃ s, traceAgent s = h := by
  rintro ⟨traceAgent, htrace⟩
  -- the self-located trace, restricted to the self, completely models the self
  have hself : PointSurjective (fun s => restrict (traceAgent s)) := by
    intro h
    obtain ⟨k, hk⟩ := hrestrict h
    obtain ⟨s, hs⟩ := htrace k
    exact ⟨s, by show restrict (traceAgent s) = h; rw [hs]; exact hk⟩
  -- a complete self-model gives `neg` a fixed point — impossible
  obtain ⟨v, hv⟩ := lawvere _ hself neg
  exact hneg v hv

/-- **The same seam in the doctrinal A2-closure form.** To decohere itself the self would hold a
complete *view* `v : Env → View` of the relationship, consistent with every account at that
account's own registration (`∀ w, v (reg w) = w (reg w)`). But the relationship is self-inclusive:
every view of it is registered among its relata — `reg` — because *viewing the relationship is
relating to it*, hence (A2) part of it. So by `Relating.no_complete_view` no such complete view
exists: the trace that would decohere the self requires a view the self, registered inside the
relationship, cannot hold. -/
theorem self_cannot_view_relation {Env : Type u} {View : Type v}
    (reg : (Env → View) → Env) (neg : View → View) (hneg : ∀ x, neg x ≠ x) :
    ¬ ∃ v : Env → View, ∀ w : Env → View, v (reg w) = w (reg w) :=
  no_complete_view reg neg hneg

end RelExist.Seam
