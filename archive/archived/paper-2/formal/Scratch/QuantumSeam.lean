/-
# The quantum seam (bridge B, route 2): decoherence is irreversible, and its loss is non-broadcastable

[`SeamBridge`](../RelExist/SeamBridge.lean) closed **bridge A** of the seam (the posited maps are now a
supplied *set-level* forgetting) but explicitly **not bridge B** — that the obstruction bites the
*quantum* partial trace / decoherence. This module takes B by **route 2**: not Lawvere's diagonal in
the quantum fragment (that needs a reflexive object `matTracedSMC` lacks — Cantor; route 1, still
open), but the **no-broadcasting** face of the *same firewall* (`Compact.collapse`,
`Compact.no_cloning`) whose cartesian face is Lawvere. Crucially, this one bites the **actual matrix
operation** `dephase` (the local face of the partial trace,
`Conservation.decoherence_is_partial_trace`), not a set projection.

* `dephase_not_injective` — the **real** decoherence is lossy: a coherent state `|+⟩⟨+|` and its own
  decohered shadow are distinct yet `dephase` identically. (Contrast `SeamBridge.forget_lossy`, which
  was projection non-injectivity on functions; this is on the genuine `dephase`.)
* `no_dephase_recovery` — and **irreversible**: no map left-inverts `dephase`. The self cannot undo its
  own decoherence, on the actual operation.
* `irreversible_loss_is_noncopyable` / `dephase_fixes_iff_copyable` — and the loss is *exactly the
  non-broadcastable part*: `dephase` fixes a state iff it is classical (copyable); the states it
  irreversibly alters are the non-classical ones, which are non-broadcastable
  (`plus_not_classical`; the no-cloning fault line `classical_comm`). What the partial trace forgets,
  and cannot restore, is exactly what cannot be cloned.

**The two seams, unified by the firewall.** The cartesian seam (`SeamBridge` / Lawvere) needs copying —
`g a a` — to run its diagonal; the quantum seam here forbids copying — no-broadcasting. `Compact.collapse`
(cartesian + compact ⇒ thin) is why they cannot both hold in one non-trivial domain, and why *either*
way a self cannot hold a complete account of itself: where it can copy, the diagonal escapes; where it
cannot copy, the coherence is unrecoverable. One firewall, two faces.

**Honest scope.** This is **route 2**, and it is **not new mathematics** — `dephase_not_injective` is
idempotency plus a coherent witness; `no_dephase_recovery` is non-injectivity ⇒ no left inverse. Its
worth is that it bites the **real** `dephase`/`ptrace` (which `SeamBridge` did not) via no-broadcasting,
and it names the unification. What remains **`[open]`** is **route 1**: the *Lawvere* diagonal itself
biting `ptrace` via an internal point-surjection — which needs a traced/GoI setting with a reflexive
object (`D ≅ [D→D]`), not the finite matrix model. B-as-no-broadcasting: done here. B-as-Lawvere: open.
-/
import Scratch.Decoherence

namespace RelExist.QuantumSeam

open RelExist.Decoherence

/-- The actual decoherence `dephase` is **lossy** — on the genuine matrix operation, not a projection:
a coherent state `|+⟩⟨+|` and its own decohered shadow are distinct yet `dephase` identically. -/
theorem dephase_not_injective :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ, M ≠ N ∧ dephase M = dephase N :=
  ⟨plus, dephase plus, fun h => dephase_plus_ne h.symm, (dephase_idem plus).symm⟩

/-- **The self cannot undo its own decoherence — on the actual matrix operation.** No recovery map
left-inverts `dephase`: were there one, the coherent state and its shadow would be forced equal. The
quantum seam biting the real `dephase` (the local face of the partial trace). -/
theorem no_dephase_recovery :
    ¬ ∃ recover : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ M, recover (dephase M) = M := by
  rintro ⟨recover, hrec⟩
  obtain ⟨M, N, hne, heq⟩ := dephase_not_injective
  apply hne
  calc M = recover (dephase M) := (hrec M).symm
    _ = recover (dephase N) := by rw [heq]
    _ = N := hrec N

/-- **The loss is exactly the non-broadcastable part.** The witness whose decoherence cannot be undone
is a **non-classical** (hence non-broadcastable) state: `¬ IsClassical plus` and `dephase plus ≠ plus`.
What the partial trace forgets is precisely the coherence that cannot be cloned. -/
theorem irreversible_loss_is_noncopyable :
    ¬ IsClassical plus ∧ dephase plus ≠ plus :=
  ⟨plus_not_classical, dephase_plus_ne⟩

/-- **Decoherence fixes exactly the copyable fragment.** A state survives decoherence untouched iff it
is classical (copyable); everything coherent is strictly, irreversibly lost — the no-broadcasting
fault line, on the real operation. -/
theorem dephase_fixes_iff_copyable (M : Matrix (Fin 2) (Fin 2) ℝ) :
    dephase M = M ↔ IsClassical M :=
  dephase_eq_self_iff

end RelExist.QuantumSeam
