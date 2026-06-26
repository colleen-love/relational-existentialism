/-
# Bridge B, closed on the compact face — the seam bites the *genuine* partial trace

[`QuantumSeam`](QuantumSeam.lean) took bridge B by route 2, but on `dephase` (the *local* dephasing
map) and via "no left inverse." This module moves route 2 onto the **actual partial trace `ptrace`** —
the very operation `Conservation.decoherence_is_partial_trace` produces — and sharpens the obstruction
from "lossy" to the physically exact statement: **`ptrace` collapses an entangled joint and its
decohered shadow to the *same marginal*, so a self holding only its marginal cannot tell whether it is
entangled, and the information it cannot recover is exactly the non-broadcastable coherence.**

The witnesses are the genuine ones from [`Conservation`](Conservation.lean): the Schmidt-correlated
`entangle a` (globally coherent, `not_isClassical_entangle`) and its product-basis decoherence
`dephase (entangle a)` (classical). The key computation `ptrace_dephase` shows global dephasing is
invisible to the partial trace on a state whose marginal is already diagonal — so the two joints,
*one entangled and one not*, have **identical** partial traces.

* `ptrace_dephase` — global product-basis dephasing commutes past the partial trace into a diagonal:
  `ptrace (dephase M) i j = if i = j then ptrace M i j else 0`.
* `ptrace_collapses_entanglement` — the real `ptrace` is **non-injective on the entanglement degree of
  freedom**: `entangle a ≠ dephase (entangle a)` (one coherent, one classical) yet
  `ptrace (entangle a) = ptrace (dephase (entangle a))`. The partial trace forgets the relation.
* `no_ptrace_recovery` — **the seam on the genuine `ptrace`**: no map reconstructs the joint from its
  marginal. A self with only `ρ_S = ptrace ρ_SE` cannot recover `ρ_SE` — cannot hold a complete account
  of the relation it is in. (Strengthens `QuantumSeam.no_dephase_recovery` from `dephase` to `ptrace`.)
* `unresolved_fiber_is_coherence` — **the unrecoverable fiber is exactly the non-broadcastable part**:
  the two joints with the same marginal are a *non-classical* (non-broadcastable) state and a classical
  one. What `ptrace` destroys, and the self cannot restore, is precisely the coherence that cannot be
  cloned — the no-broadcasting face of the firewall, on the real operation.

**Why this is the *whole* bridge — route 1 is firewall-obstructed, not merely unbuilt.** The
complementary cartesian face (route 1: Lawvere's diagonal *inside* the quantum fragment) is not a
remaining to-do; it is **ruled out by the firewall**. Lawvere's argument is intrinsically cartesian —
it copies its point (`Mirror.lawvere` applies `g a a`) — and [`Compact`](Compact.lean) proves that any
**non-trivial compact-closed structure has no cartesian copy** (`Compact.no_cloning`: two distinct
parallel maps ⇒ `¬ UnitSubterminal`), because copying + compact closure forces thinness
(`Compact.collapse`). So the diagonal route 1 would run cannot exist in the genuine (entangled, non-thin)
quantum category. The partial-trace seam is therefore **necessarily** the compact / no-broadcasting face
— exactly the one mechanized here — and that necessity *is* the resolution of the open dichotomy.

**Honest scope.** This is **not new mathematics**: `ptrace_dephase` is a one-line sum manipulation,
non-injectivity ⇒ no recovery is the same two-line argument as before, and the firewall is the existing
`Compact.collapse`. What it delivers is that the seam now bites the **genuine `ptrace`** (which neither
`SeamBridge` nor `QuantumSeam` did — they had a set projection and `dephase`), that the lost fiber is
identified with non-broadcastable coherence, and that route 1 is shown to be the *wrong face* by a
theorem rather than left open. The standing `[reading]` — that `entangle`'s environment factor *is* the
relationship the self is made of (A2) — is unchanged; that identification is the lens, not a derivation.
-/
import Scratch.Conservation
import Scratch.Compact

namespace RelExist.QuantumSeamTrace

open Matrix BigOperators
open RelExist.Conservation RelExist.Decoherence RelExist.PartialTrace

variable {m : Type} [DecidableEq m] [Fintype m]

/-- **Global dephasing commutes past the partial trace into a diagonal.** Decohering the *joint* state
in the product basis, then tracing out the environment, gives the partial trace forced to its diagonal:
`ptrace (dephase M) i j = if i = j then ptrace M i j else 0`. (The off-diagonal `i ≠ j` of the partial
trace is killed, because product-basis dephasing zeroes any joint entry with `i ≠ j`.) -/
theorem ptrace_dephase (M : Matrix (m × m) (m × m) ℝ) (i j : m) :
    ptrace (dephase M) i j = if i = j then ptrace M i j else 0 := by
  simp only [ptrace_apply, dephase_apply, Prod.mk.injEq]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The partial trace of the entangled joint **equals** that of its decohered shadow. Since
`ptrace (entangle a)` is already diagonal, global dephasing leaves it untouched — the entangling
coherence lives entirely in the part the partial trace forgets. -/
theorem ptrace_entangle_eq_ptrace_dephase (a : m → ℝ) :
    ptrace (entangle a) = ptrace (dephase (entangle a)) := by
  funext i j
  rw [ptrace_dephase]
  by_cases h : i = j
  · rw [if_pos h]
  · rw [if_neg h, ptrace_entangle_apply, if_neg h]

/-- **The genuine partial trace collapses the entanglement degree of freedom.** Two *distinct* joint
states — the entangled `entangle a` (globally coherent) and its product-basis decoherence
`dephase (entangle a)` (classical) — have the **same** partial trace. So the marginal a self holds does
not record whether it is entangled with its environment: the partial trace forgets the relation. -/
theorem ptrace_collapses_entanglement (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    entangle a ≠ dephase (entangle a) ∧
      ptrace (entangle a) = ptrace (dephase (entangle a)) := by
  refine ⟨?_, ptrace_entangle_eq_ptrace_dephase a⟩
  intro heq
  apply not_isClassical_entangle a hij hi hj
  rw [heq]
  exact isClassical_dephase (entangle a)

/-- **The seam on the genuine `ptrace`.** No map reconstructs the joint state from its partial trace:
a self holding only its marginal `ρ_S = ptrace ρ_SE` cannot recover the joint `ρ_SE` — cannot hold a
complete account of the relation it is part of. Were there such a `recover`, the entangled joint and its
classical shadow (equal marginals) would be forced equal, contradicting
`ptrace_collapses_entanglement`. This is `QuantumSeam.no_dephase_recovery` lifted from `dephase` to the
**actual partial trace**. -/
theorem no_ptrace_recovery (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    ¬ ∃ recover : Matrix m m ℝ → Matrix (m × m) (m × m) ℝ,
        ∀ M : Matrix (m × m) (m × m) ℝ, recover (ptrace M) = M := by
  rintro ⟨recover, hrec⟩
  obtain ⟨hne, heq⟩ := ptrace_collapses_entanglement a hij hi hj
  apply hne
  calc entangle a = recover (ptrace (entangle a)) := (hrec _).symm
    _ = recover (ptrace (dephase (entangle a))) := by rw [heq]
    _ = dephase (entangle a) := hrec _

/-- **The unrecoverable fiber is exactly the non-broadcastable coherence.** The two joints the partial
trace cannot tell apart are a **non-classical** (non-broadcastable) state and a **classical** one, with
the same marginal. So what `ptrace` destroys — and the self cannot restore (`no_ptrace_recovery`) — is
precisely the coherence that cannot be cloned: the seam's quantum face *is* the no-broadcasting face of
the firewall, realized on the real operation. -/
theorem unresolved_fiber_is_coherence (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    ¬ IsClassical (entangle a) ∧ IsClassical (dephase (entangle a)) ∧
      ptrace (entangle a) = ptrace (dephase (entangle a)) :=
  ⟨not_isClassical_entangle a hij hi hj, isClassical_dephase (entangle a),
    ptrace_entangle_eq_ptrace_dephase a⟩

/-- **Route 1 is the wrong face — the firewall, restated for the seam.** Lawvere's diagonal is a
*cartesian* argument (it copies its point); a non-trivial compact-closed structure — the quantum
fragment that carries the partial trace — has **no** such cartesian copy (`Compact.no_cloning`: any two
distinct parallel maps force `¬ UnitSubterminal`, since copying + compact closure ⇒ thin,
`Compact.collapse`). Hence the partial-trace seam cannot live on the cartesian/Lawvere face; it is
**necessarily** the compact/no-broadcasting face above. (This is `Compact.no_cloning` read for the seam,
not new math — but it converts "route 1 open" into "route 1 obstructed.") -/
theorem route1_needs_copy_blocked (C : RelExist.Compact.CompactClosed)
    {A B : C.Obj} {f g : C.Hom A B} (hfg : f ≠ g) :
    ¬ RelExist.Compact.UnitSubterminal C :=
  RelExist.Compact.no_cloning C hfg

end RelExist.QuantumSeamTrace
