/-
`program-3/series-3/formal/P3S3/ws3.lean`

WS3 - The sign is forced, not chosen. Program 3 Series 3 (3.3), the phase.

The theorem Program Review 2-1 found missing in Series 2.11 (finding S-1): the parity sign was one free
choice among an unconstrained space of "earned" candidates. Here the space is constrained and classified:

- `ws3_sign_forced`: every composition-respecting, `±1`-valued phase on windings is either trivial
  (constantly `1`) or the parity sign. Nothing else exists in the family. A nontrivial sign has no
  freedom left; parity is not selected, it is what remains.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws2

namespace P3S3

set_option linter.unusedVariables false

/-- Every composition-respecting, `±1`-valued phase on windings is trivial or the parity sign. The
multiplicativity pins the phase at `0` to `1` and propagates the single choice at `1` to every winding;
`±1`-valuedness leaves that choice two values, and the nontrivial one is parity. -/
theorem ws3_sign_forced (s : ℤ → ℤ)
    (hmul : ∀ a b : ℤ, s (a + b) = s a * s b)
    (hval : ∀ n : ℤ, s n = 1 ∨ s n = -1) :
    (∀ n : ℤ, s n = 1) ∨ (∀ n : ℤ, s n = if n % 2 = 0 then 1 else -1) := by
  have hsq : ∀ n : ℤ, s n * s n = 1 := by
    intro n
    rcases hval n with h | h <;> rw [h] <;> norm_num
  have heven : ∀ k : ℤ, s (2 * k) = 1 := by
    intro k
    have : s (k + k) = s k * s k := hmul k k
    rw [hsq k] at this
    rw [two_mul]
    exact this
  have hodd : ∀ k : ℤ, s (2 * k + 1) = s 1 := by
    intro k
    have := hmul (2 * k) 1
    rw [heven k, one_mul] at this
    exact this
  rcases hval 1 with h1 | h1
  · left
    intro n
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, ← two_mul, heven]
    · rw [hk, hodd, h1]
  · right
    intro n
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmod : n % 2 = 0 := by omega
      rw [if_pos hmod, hk, ← two_mul, heven]
    · have hmod : ¬ n % 2 = 0 := by omega
      rw [if_neg hmod, hk, hodd, h1]

end P3S3
