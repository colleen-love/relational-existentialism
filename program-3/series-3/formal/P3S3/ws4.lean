/-
`program-3/series-3/formal/P3S3/ws4.lean`

WS4 - Interference on histories. Program 3 Series 3 (3.3), the phase.

The phase applied: with the parity sign now the classified nontrivial member of its family (WS3), two
co-terminal histories interfere by the parity of their winding difference.

- `ws4_amp_canonical`: the parity sign satisfies the classification's hypotheses and is nontrivial — it
  is the forced member, not a choice;
- `ws4_destructive_iff`: for all windings, the combined weight falls below the parts exactly when the
  winding difference is odd;
- `ws4_interference_on_histories`: both poles witnessed on named co-terminal histories from one state —
  destructive at windings `1` and `2`, additive at windings `1` and `3`;
- `ws4_exponent_not_forced`: every member of the `|·|^p` family (`p ≥ 1`) vanishes exactly at
  cancellation, so the cancellation test forces the phase and provably not the exponent — Series 2.12's
  ceiling, now a theorem at this scope.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws3

namespace P3S3

set_option linter.unusedVariables false

/-- The phase: the parity sign on windings. By WS3 this is the unique nontrivial member of the
composition-respecting `±1` family; the definition records the forced value, it does not choose one. -/
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1

/-- The parity sign satisfies the classification's hypotheses and is nontrivial: it is the forced
nontrivial member of its family. -/
theorem ws4_amp_canonical :
    (∀ a b : ℤ, amp (a + b) = amp a * amp b)
  ∧ (∀ n : ℤ, amp n = 1 ∨ amp n = -1)
  ∧ amp 1 = -1 := by
  refine ⟨?_, ?_, by decide⟩
  · intro a b
    unfold amp
    by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
    · rw [if_pos ha, if_pos hb, if_pos (by omega), one_mul]
    · rw [if_pos ha, if_neg hb, if_neg (by omega), one_mul]
    · rw [if_neg ha, if_pos hb, if_neg (by omega), mul_one]
    · rw [if_neg ha, if_neg hb, if_pos (by omega)]
      norm_num
  · intro n
    unfold amp
    split_ifs <;> simp

/-- Co-terminal histories interfere by the parity of their winding difference: the combined weight falls
strictly below the parts exactly when the difference is odd, for all windings. -/
theorem ws4_destructive_iff (w1 w2 : ℤ) :
    (amp w1 + amp w2) ^ 2 < (amp w1) ^ 2 + (amp w2) ^ 2 ↔ (w1 - w2) % 2 ≠ 0 := by
  unfold amp
  by_cases h1 : w1 % 2 = 0 <;> by_cases h2 : w2 % 2 = 0
  · rw [if_pos h1, if_pos h2]
    constructor
    · intro h; norm_num at h
    · intro h; exfalso; omega
  · rw [if_pos h1, if_neg h2]
    constructor
    · intro _; omega
    · intro _; norm_num
  · rw [if_neg h1, if_pos h2]
    constructor
    · intro _; omega
    · intro _; norm_num
  · rw [if_neg h1, if_neg h2]
    constructor
    · intro h; norm_num at h
    · intro h; exfalso; omega

/-- Both poles, witnessed on the named co-terminal histories of WS2: the direct and routed histories
(windings `1` and `2`) interfere destructively; the direct and long histories (windings `1` and `3`)
add. Same state, same endpoints, the parity of the winding difference deciding. -/
theorem ws4_interference_on_histories :
    (run P3S3.hDirect P3S1.gFwd = run P3S3.hRouted P3S1.gFwd
      ∧ (amp (wind hDirect P3S1.gFwd) + amp (wind hRouted P3S1.gFwd)) ^ 2
          < (amp (wind hDirect P3S1.gFwd)) ^ 2 + (amp (wind hRouted P3S1.gFwd)) ^ 2)
  ∧ (run hLong P3S1.gFwd = run hDirect P3S1.gFwd
      ∧ (amp (wind hDirect P3S1.gFwd)) ^ 2 + (amp (wind hLong P3S1.gFwd)) ^ 2
          ≤ (amp (wind hDirect P3S1.gFwd) + amp (wind hLong P3S1.gFwd)) ^ 2) := by
  refine ⟨⟨ws2_winding_path_dependent.1, ?_⟩, ⟨ws2_windings_both_parities.1, ?_⟩⟩ <;> decide

/-- Every member of the `|·|^p` family vanishes exactly at cancellation: the cancellation test forces the
phase (WS3) and provably not the exponent. Series 2.12's ceiling, restated as a theorem. -/
theorem ws4_exponent_not_forced (p : ℕ) (hp : 1 ≤ p) (a b : ℤ) :
    |a + b| ^ p = 0 ↔ a + b = 0 := by
  rw [pow_eq_zero_iff (by omega : p ≠ 0), abs_eq_zero]

end P3S3
