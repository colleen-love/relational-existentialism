/-
# Trace as feedback, and the Conway operator — definition D1 & theorem T1

Mechanizes the *operational content* of the doctrine's trace (`Tr`) in the cartesian
(complete-lattice) setting, where feedback genuinely produces fixed points:

* **D1 — self-relation is feedback.** `selfTrace P := νP` (the same `ν`-modality as `≈`):
  the trace of a self-relating `P` is the fixed point it feeds back to.
* **T1 — to relate is to create.** The *parameterized* fixed-point (Conway) operator
  `Tr f a := ν(f a)`: looping the wire `β` with a parameter `a` manufactures a fixed
  point `f a (Tr f a) = Tr f a` that need not have pre-existed. We prove the Conway
  fixed-point identity, the greatest-fixed-point (coinduction) property, and naturality
  in the parameter.

This is `[cartesian; theorem]`: the complete lattice is exactly the order-theoretic
shadow of the cartesian fragment, where `Tr` is a Conway operator (Hasegawa–Hyland).
The abstract *traced symmetric monoidal category* itself is left as categorical
infrastructure; what the axioms invoke — feedback creating a fixed point — is here.
-/
import Mathlib.Order.FixedPoints

namespace RelExist.Trace

variable {α : Type*} {β : Type*}

/-- **D1 — self-relation is feedback.** The trace of a self-relating `P : α →o α` is the
(greatest) fixed point it feeds back to: `σ(P) := Tr(P) = νP`. -/
def selfTrace [CompleteLattice α] (P : α →o α) : α := P.gfp

/-- The self-trace is a genuine fixed point — feedback closes: `P (Tr P) = Tr P`. -/
theorem selfTrace_fixed [CompleteLattice α] (P : α →o α) : P (selfTrace P) = selfTrace P :=
  P.map_gfp

variable [CompleteLattice β]

/-- **T1 — the parameterized fixed-point (Conway) operator.** Tracing the looped wire
`β` against a parameter `a : α` yields `Tr f a := ν(f a)`. -/
def Tr (f : α → β →o β) (a : α) : β := (f a).gfp

/-- **To relate is to create** (the Conway fixed-point identity): the traced map is a
fixed point, `f a (Tr f a) = Tr f a`. Looping manufactures structure. -/
theorem Tr_fixed (f : α → β →o β) (a : α) : (f a) (Tr f a) = Tr f a :=
  (f a).map_gfp

/-- The traced value is the **greatest** consistent feedback: any post-fixed point of
the loop lies below it (coinduction). -/
theorem le_Tr (f : α → β →o β) (a : α) {b : β} (h : b ≤ (f a) b) : b ≤ Tr f a :=
  (f a).le_gfp h

/-- **Naturality in the parameter** (a Conway law): a stronger coupling traces to a
greater fixed point. -/
theorem Tr_mono (f : α → β →o β) {a a' : α} (h : f a ≤ f a') : Tr f a ≤ Tr f a' := by
  apply le_Tr
  calc Tr f a = (f a) (Tr f a) := (Tr_fixed f a).symm
    _ ≤ (f a') (Tr f a) := h (Tr f a)

end RelExist.Trace
