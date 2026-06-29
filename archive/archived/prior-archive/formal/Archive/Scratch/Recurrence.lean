/-
# AI — recurrence, feedback, and the Geometry of Interaction (Layer 4, fourth domain)

The plan's AI verdict is a **design-principle functor**: *Geometry of Interaction is
traced categories*, and the semantics of recurrence **is** feedback through a hidden wire.
This module makes that literal, reusing the doctrine's own structure rather than re-deriving
it:

* **Feedback = the trace.** A recurrent system `step : (input × state) → (output × state)`
  loops its hidden `state` back into itself. Its observable input/output behaviour is
  `rtrace step` — *exactly* the trace of `Rel` ([`Scratch/Rel.lean`](Rel.lean)). The GoI
  "execution formula" — feedback realised by a **self-consistent hidden state** — falls out
  by definition (`feedback_iff`), and `feedback_eq_trace` shows it *is* `Tr` in the doctrine.
* **Sustained recurrence = the eigenform `ν`.** Pure state dynamics `next : state → state`
  give a monotone "can-keep-going" operator whose **greatest fixed point** (`sustained`) is
  the set of states lying on an unbounded orbit — the recurrent net's persistent activity,
  the AI eigenform, the same `OrderHom.gfp` ν-modality as `≈` and attention.
* **The bridge.** A self-consistent hidden state of a traced feedback system is a *sustained*
  state of the induced dynamics (`selfConsistent_sustained`): the looped self in the theory
  maps to persistent recurrence in the AI domain. Trace and `ν` together — the functor.

So the AI domain *receives* the trace and the eigenform structure with nothing bolted on:
the recurrence operator is the doctrine's `Tr`, and sustained computation is its `ν`.
-/
import Mathlib.Order.FixedPoints
import Scratch.Rel

namespace RelExist.Recurrence

open RelExist.RelModel RelExist.Traced

universe u
variable {I O S : Type u}

/-! ### Feedback as the trace (the Geometry-of-Interaction execution formula) -/

/-- A **recurrent system**: given an input and the current hidden state, it relates to an
output and the next hidden state. The hidden `state` is the looped wire. -/
abbrev Recurrent (I O S : Type u) : Type u := Rel (I × S) (O × S)

/-- **The feedback behaviour** of a recurrent system — its observable input/output relation,
obtained by tracing out (feeding back) the hidden state. This is the doctrine's trace. -/
def feedback (step : Recurrent I O S) : Rel I O := rtrace step

/-- **The GoI execution formula.** Feedback relates `i` to `o` exactly when some hidden state
is **self-consistent** under the step — fed back into itself unchanged. The "between" of the
loop is a fixed hidden wire. -/
theorem feedback_iff (step : Recurrent I O S) (i : I) (o : O) :
    feedback step i o ↔ ∃ s, step (i, s) (o, s) := Iff.rfl

/-- **Feedback *is* the trace.** The AI domain's recurrence operator is, definitionally, the
doctrine's `Tr` in `Rel` — the functor on this generator is the identity-on-structure. -/
theorem feedback_eq_trace (step : Recurrent I O S) :
    feedback step = relTracedSMC.trace step := rfl

/-! ### Sustained recurrence as the eigenform `ν` -/

/-- The **"can keep going" operator** of a transition relation `next`: a state is retained
when it has a successor that is itself retained. Monotone, so it has a greatest fixed point. -/
def recurOp (next : S → S → Prop) : Set S →o Set S where
  toFun X := {s | ∃ s', next s s' ∧ s' ∈ X}
  monotone' := by
    intro X Y hXY s hs
    obtain ⟨s', hns, hs'⟩ := hs
    exact ⟨s', hns, hXY hs'⟩

@[simp] theorem mem_recurOp {next : S → S → Prop} {X : Set S} {s : S} :
    s ∈ recurOp next X ↔ ∃ s', next s s' ∧ s' ∈ X := Iff.rfl

/-- **Sustained recurrence `ν`**: the greatest set of states from which the dynamics can
continue indefinitely — the recurrent system's persistent activity, an eigenform of
"can-keep-going". -/
def sustained (next : S → S → Prop) : Set S := (recurOp next).gfp

/-- `sustained` is a **fixed point**: every sustained state steps to a sustained state, and
conversely. -/
theorem sustained_fixed (next : S → S → Prop) :
    recurOp next (sustained next) = sustained next :=
  (recurOp next).map_gfp

/-- **Coinduction.** Any set that is self-upholding (every member has a successor inside the
set) consists of sustained states. To show a state recurs forever, exhibit such a set. -/
theorem sustained_greatest {next : S → S → Prop} {X : Set S}
    (h : X ≤ recurOp next X) : X ≤ sustained next :=
  (recurOp next).le_gfp h

/-- A genuine self-loop `next s s` is **sustained** — the simplest persistent recurrence (a
fixed point of the dynamics lies on an infinite constant orbit). -/
theorem selfLoop_sustained {next : S → S → Prop} {s : S} (h : next s s) :
    s ∈ sustained next := by
  have hsub : ({s} : Set S) ≤ sustained next := by
    apply sustained_greatest
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact ⟨s, h, rfl⟩
  exact hsub rfl

/-! ### The bridge — a feedback fixed point is sustained recurrence -/

/-- The **hidden-state dynamics** a recurrent system induces at a fixed input/output: the
state may step `s → s'` when `step` relates `(i,s)` to `(o,s')`. -/
def induced (step : Recurrent I O S) (i : I) (o : O) : S → S → Prop :=
  fun s s' => step (i, s) (o, s')

/-- **The functor's content.** A self-consistent hidden state realising the feedback `i ↦ o`
is a *sustained* state of the induced dynamics: the looped self of the theory (a self-trace
fixed point) maps to persistent recurrence in the AI domain. Trace ⟶ feedback, `ν` ⟶
sustained activity — both received with nothing added. -/
theorem selfConsistent_sustained {step : Recurrent I O S} {i : I} {o : O} {s : S}
    (h : step (i, s) (o, s)) : s ∈ sustained (induced step i o) :=
  selfLoop_sustained (next := induced step i o) h

/-- Hence **observable feedback is witnessed by a sustained eigenform**: if the system
exhibits the behaviour `i ↦ o` via a self-consistent state, that witness recurs forever. -/
theorem feedback_witnessed_by_sustained {step : Recurrent I O S} {i : I} {o : O}
    (h : feedback step i o) :
    ∃ s, step (i, s) (o, s) ∧ s ∈ sustained (induced step i o) := by
  obtain ⟨s, hs⟩ := (feedback_iff step i o).1 h
  exact ⟨s, hs, selfConsistent_sustained hs⟩

end RelExist.Recurrence
