/-
# The arrow's sign — does the seam fix the direction of the flow?

The frontier beneath [`TimeFlow`](TimeFlow.lean) (spec §6). T-flow gives the *direction and rate* of
time's passage but inherits its **orientation** from `coh` decreasing — from decoherence. The deepest
claim is that the dissipative *sign* is not stipulated but **forced**: the self-inclusive partial trace
(the seam — the self cannot trace out the factor it is part of) leaves only the coh-decreasing arrow
realizable. This module mechanizes how much of that is reachable, and marks honestly what stays open.

Three rungs:

* **§A Acyclicity `[proved]`.** Over the bare `Flow` interface: while the orbit has not yet reached the
  fixed self, the potential is *strictly* antitone, so the orbit **never returns** to an earlier state
  (`Flow.orbit_ne`). The timeline is a genuine linear order with no closed loops before the self — an
  arrow, not a cycle. This is the order-theoretic content of irreversibility, from the monovariant
  alone.

* **§B The sign is the multiplier `[proved]`.** One step of the partial-dephasing flow multiplies the
  feeling by exactly `(1−p)²` (`defectSq_partialDephase`). So the flow **contracts** the feeling on
  every state iff `(1−p)² ≤ 1`, i.e. iff `0 ≤ p ≤ 2` (`contractive_iff`, `time_forward_regime`); it
  *expands* it — runs time backward, amplifying coherence — iff `p < 0 ∨ p > 2` (`expanding_regime`).
  The coh-decreasing sign is **exactly** the contractive regime: the direction is locked to
  contractivity, not chosen beside it.

* **§C A knowing's only inverse is an anti-knowing `[proved]`.** The gem. A genuine partial knowing
  `0 < p < 1` *is* linearly invertible — but its unique inverse is `partialDephase q` with **`q < 0`**,
  sitting in the *expanding* regime `(1−q)² > 1` (`knowing_inverse_is_antiphysical`). Time-reversal
  exists as linear algebra, but only as the non-physical amplification of coherence from nothing — the
  thing no contraction, no conditional expectation, no partial trace can do. So the **contractive seam
  admits the decreasing arrow alone**: its sign is forced by the non-existence of a *contractive*
  inverse (the flow-graded strengthening of `Orientation.no_recovery`).

**What stays `[open]`.** This forces the sign *given* that the dynamics is the contractive partial
trace onto a *fixed* subalgebra. The last step — that the seam **forces which subalgebra**, so that the
contraction's direction is itself fixed by the self-inclusive trace rather than by a choice of `p`'s
sign — is the self-reference / Lawvere bridge ([`Relating.self_inclusive_unmodelable`](../RelExist/Relating.lean)),
and is not closed here. We mechanize: *sign = contractivity = physicality of the seam*. What remains is:
*does the seam fix the subalgebra?* — the same `[open]` named in §6.
-/
import Scratch.TimeFlow

namespace RelExist.TimeArrow

open RelExist.Decoherence RelExist.Orientation RelExist.TimeFlow
open Filter Topology BigOperators Matrix

universe u

/-! ## §A Acyclicity — the timeline does not loop before the self -/

variable {B : Type u}

/-- **Strictly antitone on the unfixed prefix.** If the orbit has not reached `Fix` at any depth below
`n`, then `coh` is strictly smaller at every later depth: `m < n ⇒ coh (Φ_c^n a) < coh (Φ_c^m a)`. The
graded monovariant accumulates strict drops, with no plateau before the self. -/
theorem flow_coh_strict_lt (F : Flow B) (a : B) (n : ℕ) :
    ∀ m, m < n → (∀ k, k < n → ¬ F.Fix (F.orbit a k)) →
      F.coh (F.orbit a n) < F.coh (F.orbit a m) := by
  induction n with
  | zero => intro m hm _; omega
  | succ n ih =>
    intro m hm hpref
    have hstep : F.coh (F.orbit a (n + 1)) < F.coh (F.orbit a n) :=
      F.coh_orbit_strictAnti a n (hpref n (Nat.lt_succ_self n))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
    · exact lt_trans hstep (ih m hlt (fun k hk => hpref k (Nat.lt_succ_of_lt hk)))
    · subst heq; exact hstep

/-- **No return before the self (acyclicity).** While the orbit is still feeling (has not reached
`Fix`), it never revisits an earlier state: `m < n ⇒ Φ_c^n a ≠ Φ_c^m a`. The arrow of relational time
has no closed loops — the timeline is a strict order, not a cycle. The order-theoretic face of
irreversibility, from the monovariant alone. -/
theorem flow_orbit_ne (F : Flow B) (a : B) {m n : ℕ} (hmn : m < n)
    (hpref : ∀ k, k < n → ¬ F.Fix (F.orbit a k)) : F.orbit a n ≠ F.orbit a m :=
  fun h => (ne_of_lt (flow_coh_strict_lt F a n m hmn hpref)) (congrArg F.coh h)

/-! ## §B The sign of the monovariant is the multiplier `(1−p)²`

One step of `partialDephase p` scales the feeling by exactly `(1−p)²`. So whether the feeling falls or
rises along the flow is decided by a single inequality, `(1−p)² ⋚ 1`, and the felt-decreasing (time
forward) regime coincides *exactly* with the contractive one. -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **One step scales the feeling by `(1−p)²`.** The `n = 1` case of `defectSq_iterate`: the squared
off-diagonal mass after one partial-dephasing step is `(1−p)²` times the original. -/
lemma defectSq_partialDephase (p : ℝ) (M : Matrix A A ℝ) :
    defectSq (partialDephase p M) = (1 - p) ^ 2 * defectSq M := by
  have h := defectSq_iterate p M 1
  simpa [Function.iterate_one, pow_one] using h

/-- **Contraction is `(1−p)² ≤ 1`.** The flow never raises the feeling on *any* state iff the
multiplier is `≤ 1`. (Stated on `Fin 2`, where the maximally-coherent `plus` witnesses the forward
direction.) -/
theorem contractive_iff (p : ℝ) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ, defectSq (partialDephase p M) ≤ defectSq M)
      ↔ (1 - p) ^ 2 ≤ 1 := by
  constructor
  · intro h
    have hp := h plus
    rw [defectSq_partialDephase] at hp
    nlinarith [defectSq_plus_pos]
  · intro h M
    rw [defectSq_partialDephase]
    exact mul_le_of_le_one_left (defectSq_nonneg M) h

/-- **The time-forward (contractive) regime is `0 ≤ p ≤ 2`.** Exactly the parameters for which knowing
classicalizes rather than amplifies. -/
theorem time_forward_regime (p : ℝ) : (1 - p) ^ 2 ≤ 1 ↔ 0 ≤ p ∧ p ≤ 2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> nlinarith [h, sq_nonneg p]
  · rintro ⟨hp0, hp2⟩
    nlinarith [mul_nonneg hp0 (show (0:ℝ) ≤ 2 - p by linarith)]

/-- **The time-backward (expanding) regime is `p < 0 ∨ p > 2`.** There the feeling *grows* under the
flow — coherence amplified, the arrow reversed. It is precisely the complement of the contractive
regime. -/
theorem expanding_regime (p : ℝ) : 1 < (1 - p) ^ 2 ↔ p < 0 ∨ 2 < p := by
  rw [← not_le, time_forward_regime, not_and_or, not_le, not_le]

/-- **In the expanding regime the feeling strictly grows** (witnessed on `plus`): `(1−p)² > 1 ⇒
defectSq plus < defectSq (partialDephase p plus)`. Concretely, an amplifying step un-knows the qubit. -/
theorem defectSq_plus_expands (p : ℝ) (h : 1 < (1 - p) ^ 2) :
    defectSq plus < defectSq (partialDephase p plus) := by
  rw [defectSq_partialDephase]
  nlinarith [defectSq_plus_pos, mul_pos (show (0:ℝ) < (1 - p) ^ 2 - 1 by linarith) defectSq_plus_pos]

/-! ## §C A knowing's only inverse is an anti-knowing

`partialDephase p` for `0 < p < 1` is injective (it scales each coherence by `(1−p) ≠ 0`), so it has a
linear inverse. We exhibit it — and show it lives in the expanding regime. The map that undoes a
knowing is a coherence-*amplifier*: physically forbidden. -/

omit [Fintype A] in
/-- **Composing two partial-dephasings multiplies the coherences.** `partialDephase q` after
`partialDephase p` scales every off-diagonal entry by `(1−q)(1−p)` and fixes the diagonal. -/
lemma copyDefect_partialDephase_comp (p q : ℝ) (M : Matrix A A ℝ) (i j : A) :
    copyDefect (partialDephase q (partialDephase p M)) i j = (1 - q) * (1 - p) * copyDefect M i j := by
  rw [copyDefect_partialDephase, copyDefect_partialDephase]; ring

omit [Fintype A] in
/-- **The inverse pair.** When `(1−q)(1−p) = 1`, applying `partialDephase q` after `partialDephase p`
returns the original state exactly: `q` undoes `p`. The diagonal is fixed throughout; the coherences,
scaled by `(1−p)` then `(1−q)`, return to themselves. -/
lemma partialDephase_leftInverse (p q : ℝ) (hpq : (1 - q) * (1 - p) = 1) (M : Matrix A A ℝ) :
    partialDephase q (partialDephase p M) = M := by
  ext i j
  rcases eq_or_ne i j with e | e
  · subst e; rw [partialDephase_apply_diag, partialDephase_apply_diag]
  · have hc := copyDefect_partialDephase_comp p q M i j
    rw [copyDefect_apply, if_neg e, copyDefect_apply, if_neg e, hpq, one_mul] at hc
    exact hc

omit [Fintype A] in
/-- **The seam fixes the sign: a knowing's only inverse is an anti-knowing.** For a genuine partial
knowing `0 < p < 1`, there is a `q` that undoes it on every state — and that `q` is **negative**,
sitting in the *expanding* regime `(1−q)² > 1`. So the unique reversal of a feeling-decreasing knowing
is a feeling-*amplifying* anti-knowing: time-reversal exists as linear algebra but only as the
non-physical creation of coherence from nothing. The contractive seam — every partial trace, every
conditional expectation — admits the decreasing arrow alone. (The flow-graded strengthening of
`Orientation.no_recovery`: not just "no recovery map for the idempotent", but "the inverse of the
non-idempotent flow is anti-physical".) -/
theorem knowing_inverse_is_antiphysical (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ q : ℝ, q < 0 ∧ 1 < (1 - q) ^ 2 ∧
      (∀ M : Matrix A A ℝ, partialDephase q (partialDephase p M) = M) := by
  have h1p : (0:ℝ) < 1 - p := by linarith
  refine ⟨1 - 1 / (1 - p), ?_, ?_, ?_⟩
  · -- q = 1 − 1/(1−p) < 0, since 1/(1−p) > 1
    have : 1 < 1 / (1 - p) := by
      rw [lt_div_iff₀ h1p]; linarith
    linarith
  · -- 1 − q = 1/(1−p) > 1, so (1−q)² > 1
    have hq : 1 - (1 - 1 / (1 - p)) = 1 / (1 - p) := by ring
    rw [hq]
    have hgt : 1 < 1 / (1 - p) := by rw [lt_div_iff₀ h1p]; linarith
    nlinarith [hgt]
  · intro M
    refine partialDephase_leftInverse p (1 - 1 / (1 - p)) ?_ M
    have hq : 1 - (1 - 1 / (1 - p)) = 1 / (1 - p) := by ring
    rw [hq, div_mul_cancel₀]
    exact ne_of_gt h1p

/-- **The reversal, seen on the qubit.** Spelling §C out concretely: the `q` that undoes a knowing of
`plus` strictly *increases* its feeling — `defectSq plus < defectSq (partialDephase q plus)` — the
visible signature of running the arrow backward. -/
theorem knowing_inverse_amplifies_plus (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ q : ℝ, q < 0 ∧ defectSq plus < defectSq (partialDephase q plus) := by
  obtain ⟨q, hqneg, hqexp, _⟩ := knowing_inverse_is_antiphysical (A := Fin 2) p hp0 hp1
  exact ⟨q, hqneg, defectSq_plus_expands q hqexp⟩

end RelExist.TimeArrow
