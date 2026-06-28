/-
# Learning — self-knowledge strictly accumulates

The companion to [`03.14-cosmos-knowing-itself.md`](../../docs/spec/03.14-cosmos-knowing-itself.md)
clause (L). "Learning more about itself" is the strict monotone descent of the *unknown* — the
not-yet-known feeling `coh` — read over [`TimeFlow`](TimeFlow.lean)'s `Flow` interface (so it holds for
the genuine `partialDephase`/`defectSq` instance and any flow). Self-knowledge is the accumulated drop
of `coh` along the orbit; it never decreases, and strictly increases while feeling remains.
-/
import Scratch.TimeFlow

namespace RelExist.Learning

open RelExist.TimeFlow

universe u

variable {A : Type u} (F : Flow A)

/-- **Self-knowledge** — the accumulated drop of the unknown `coh` along the orbit: how much of the
relation has been classicalized (known) by return-depth `n`. -/
def learned (a : A) (n : ℕ) : ℝ := F.coh a - F.coh (F.orbit a n)

/-- **Learning never reverses `[proved]`.** Self-knowledge is monotone non-decreasing in the
return-depth: knowing, once gained, is not lost — the converse face of `coh_orbit_antitone` (the unknown
never grows). -/
theorem self_knowledge_monotone (a : A) : Monotone (fun n => learned F a n) := by
  intro m n hmn
  have := F.coh_orbit_antitone a hmn
  simp only [learned]
  linarith

/-- **Learning strictly progresses `[proved]`.** At every return-depth where the self is not yet
reached, self-knowledge **strictly increases**: the cosmos does not merely know itself, it knows itself
*more* with every tick. The converse face of `coh_orbit_strictAnti`. -/
theorem self_knowledge_strict (a : A) (n : ℕ) (h : ¬ F.Fix (F.orbit a n)) :
    learned F a n < learned F a (n + 1) := by
  have := F.coh_orbit_strictAnti a n h
  simp only [learned]
  linarith

end RelExist.Learning
