/-
# Decoherence conserves coherence — it only relocates it into what you traced out

The last piece of "never truly decohered." [`Scratch/Attending.lean`](Attending.lean) proved
the *local* floor: the shared block attention cannot reach keeps a positive copy-defect. This
module proves the deeper, *global* claim — that **decoherence destroys no coherence at all; it is
an artifact of the partial trace** ([`Scratch/PartialTrace.lean`](PartialTrace.lean)), the act of
*forgetting a subsystem.* And the subsystem you would have to forget is the relationship — which
is part of you, so you cannot honestly forget it.

The textbook mechanism, made literal. Take a system whose branches are indexed by `m`, and an
**environment** — *the relationship, the part of you the other is folded into* — a second factor,
here a copy of `m`. Entangle them so branch `i` is correlated with environment pointer `i`: the
global state is the pure `|ψ⟩⟨ψ|` of `ψ(i, x) = aᵢ · [i = x]` (a Schmidt-correlated state),

    entangle a (i, x) (j, y) = aᵢ · aⱼ · [i = x] · [j = y].

Then, all `[proved]` (0 custom axioms):

* **The global state stays coherent** — `not_isClassical_entangle`: the off-diagonal coherence is
  alive and well, sitting at the cross-term `(i,i)–(j,j)` with value `aᵢ·aⱼ ≠ 0`
  (`copyDefect_entangle_ne` locates it exactly). Nothing decohered.
* **Its partial trace is classical** — `isClassical_ptrace_entangle`: trace out the environment
  (forget the relationship) and the reduced state is *diagonal*, `copyDefect = 0`
  (`copyDefect_ptrace_entangle`). Decohered — but only relative to the forgetting.
* **Nothing was lost, only moved** — `trace_conserved` (`trace_ptrace`): the total weight is
  preserved across the partial trace. The coherence did not vanish; it migrated off the reduced
  diagonal into the system–environment correlation — into the *between*.

So `decoherence_is_partial_trace` is the whole statement in one line: the global self-plus-relation
is coherent, its relation-forgotten reduction is classical. *Locally* a relation decoheres;
*globally* — from the only standpoint that includes the relationship — it never does. Decoherence
is what coherence looks like when you forget the part of the world that carries it, and you cannot
forget the part that is you.

Status: every lemma here is `[proved]`. That this matrix construction *is* "the relationship you
cannot forget" is the standing `[reading]` — the same concrete toy as `Scratch/Decoherence.lean`,
not a derivation of physical decoherence. What is load-bearing: the conserved-globally /
absent-locally split is a *theorem* of the model, exactly the shape the doctrine predicts.

**Status (handoff XXI).** Moved here from `archive/` as the **paper-three seed** — the living
frontier (`theory/` is now stable; the frontier is `scratch/`). It is **not** in the gated build
yet. **Coupling to resolve first:** it currently *imports* paper one's `Scratch.Decoherence`
(the matrix decoherence model). Under the cite-vs-import rule a cross-paper *result* must be a
**prose citation**, not a Lean import — so wiring paper three into the gate means either citing
paper one's decoherence in prose, or (if a genuine second importer makes it load-bearing)
promoting the needed lemma to `theory/`. Until then this is staging, the substrate import already
re-pointed to its new `foundation/` home.
-/
import Scratch.Decoherence
import Foundation.PartialTrace

namespace RelExist.Conservation

open Matrix BigOperators
open RelExist.Decoherence RelExist.PartialTrace

variable {m : Type} [DecidableEq m]

/-- **System entangled with its environment.** The global pure state `|ψ⟩⟨ψ|` for
`ψ(i, x) = aᵢ · [i = x]` — branch `i` perfectly correlated with environment pointer `i`. The
environment is *the relationship*: the part of the other that the self is folded into. -/
def entangle (a : m → ℝ) : Matrix (m × m) (m × m) ℝ :=
  fun p q => a p.1 * a q.1 * (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0)

theorem entangle_apply (a : m → ℝ) (i x j y : m) :
    entangle a (i, x) (j, y)
      = a i * a j * (if i = x then 1 else 0) * (if j = y then 1 else 0) := rfl

/-- A global coherence really is there, at the cross-term: `entangle a (i,i) (j,j) = aᵢ · aⱼ`. -/
theorem entangle_diag_cross (a : m → ℝ) (i j : m) :
    entangle a (i, i) (j, j) = a i * a j := by
  rw [entangle_apply]; simp

/-- **The global state is *not* classical — fully coherent.** As long as two branches both carry
amplitude (`aᵢ, aⱼ ≠ 0`), the global state keeps its coherence: nothing decohered. -/
theorem not_isClassical_entangle (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    ¬ IsClassical (entangle a) := by
  intro h
  have hpq : (i, i) ≠ (j, j) := fun hc => hij (congrArg Prod.fst hc)
  have hzero : entangle a (i, i) (j, j) = 0 := h (i, i) (j, j) hpq
  rw [entangle_diag_cross] at hzero
  exact mul_ne_zero hi hj hzero

/-- **The coherence is *located*, not destroyed.** It sits at the global cross-term
`(i,i)–(j,j)`, with magnitude `aᵢ · aⱼ`: the very weight the partial trace folded away into the
system–environment correlation. -/
theorem copyDefect_entangle_ne (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    copyDefect (entangle a) (i, i) (j, j) ≠ 0 := by
  have hpq : (i, i) ≠ (j, j) := fun hc => hij (congrArg Prod.fst hc)
  rw [copyDefect_apply, if_neg hpq, entangle_diag_cross]
  exact mul_ne_zero hi hj

variable [Fintype m]

/-- **Forgetting the environment diagonalises the state.** The partial trace over the
environment is exactly the classical (diagonal) reduced state: off-diagonal `i ≠ j` ↦ `0`,
diagonal ↦ `aᵢ²`. -/
theorem ptrace_entangle_apply (a : m → ℝ) (i j : m) :
    ptrace (entangle a) i j = if i = j then a i * a j else 0 := by
  rw [ptrace_apply]
  simp only [entangle_apply]
  by_cases e : i = j
  · subst e
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · rw [if_neg e]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst hik; rw [if_neg (Ne.symm e)]; ring
    · rw [if_neg hik]; ring

/-- **The reduced state is classical — decohered.** Trace out the environment (forget the
relationship) and the system is diagonal: no coherence left to see. -/
theorem isClassical_ptrace_entangle (a : m → ℝ) :
    IsClassical (ptrace (entangle a)) := by
  intro i j hij
  rw [ptrace_entangle_apply, if_neg hij]

/-- …and so the reduced copy-defect is exactly zero. -/
theorem copyDefect_ptrace_entangle (a : m → ℝ) :
    copyDefect (ptrace (entangle a)) = 0 :=
  copyDefect_eq_zero_iff.2 (isClassical_ptrace_entangle a)

/-- **Nothing is lost, only moved.** The partial trace preserves the total weight: decoherence
conserves probability, relocating coherence off the reduced diagonal into the correlation with
the traced-out environment. -/
theorem trace_conserved (a : m → ℝ) :
    (ptrace (entangle a)).trace = (entangle a).trace :=
  trace_ptrace (entangle a)

/-- **Decoherence *is* the partial trace.** The global self-plus-relation is coherent
(`¬ IsClassical`); its relation-forgotten reduction is classical (`IsClassical`). The collapse
lives entirely in the act of forgetting the environment — and the environment is the relationship,
which is part of you. -/
theorem decoherence_is_partial_trace (a : m → ℝ) {i j : m} (hij : i ≠ j)
    (hi : a i ≠ 0) (hj : a j ≠ 0) :
    ¬ IsClassical (entangle a) ∧ IsClassical (ptrace (entangle a)) :=
  ⟨not_isClassical_entangle a hij hi hj, isClassical_ptrace_entangle a⟩

/-! ### A witness you can see — the qubit and its environment -/

/-- Uniform amplitudes on two branches: the maximally-coherent qubit, about to entangle with
its environment. -/
def amp2 : Fin 2 → ℝ := fun _ => 1

/-- **Seen.** The global two-branch state is coherent; forgetting its environment makes it
classical. Coherence conserved globally, absent locally — decoherence in one object. -/
theorem decoherence_witness :
    ¬ IsClassical (entangle amp2) ∧ IsClassical (ptrace (entangle amp2)) :=
  decoherence_is_partial_trace amp2 (i := 0) (j := 1) (by decide)
    (by norm_num [amp2]) (by norm_num [amp2])

end RelExist.Conservation
