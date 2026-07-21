/-
`program-2/series-9/formal/P2S9/ws3.lean`

WS3 - The cone is a rate, not the bare order (the anti-costume core). Program 2 Series 9 (2.9), THE CONE.

The costume gate. `ws3_rate_is_content`: the carriers `attSlow` (rate 1) and `attFast` (rate 2) have the SAME causal
order (`reaches attSlow = reaches attFast` — both reach exactly the forward events), yet DIFFERENT cones
(`ball attSlow p0 1 = {p0,p1} ≠ {p0,p1,p2} = ball attFast p0 1`), because their rates differ. So the cone is NOT
recoverable from the causal order: it carries `rate × depth`, content Series 2.5's order does not have. A "cone" that
stripped to the bare reachable set would be identical on the two carriers; ours is not.

`ws3_earned_from_attention`: the rate is a function of the finite attention (`rate att = univ.sup (span att)`,
definitional), MONOTONE in it (`ws1_rate_monotone`). No `c` is postulated; delete every numeral and the rate is still
`univ.sup (span att)`. The costume gate and the no-smuggling gate, both cleared here.

Design docs: `program-2/series-9/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S9.ws1

namespace P2S9

set_option linter.unusedVariables false

/-- **SAME ORDER, DIFFERENT RATE, DIFFERENT CONE (WS3).** `attSlow` and `attFast` have IDENTICAL causal reachability,
but different rate (1 ≠ 2) and so different cones. The rate is genuine content the order does not carry: the cone is
not a relabelling of Series 2.5's reachability. -/
theorem ws3_rate_is_content :
    (∀ x y, reaches attSlow x y = reaches attFast x y)
  ∧ rate attSlow ≠ rate attFast
  ∧ ball attSlow p0 1 ≠ ball attFast p0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- **THE RATE IS EARNED FROM THE ATTENTION (WS3).** `rate` is a `Finset.sup` over the attention (definitional), and
MONOTONE in the attention. A function of the finite attention alone — never a postulated `c`. -/
theorem ws3_earned_from_attention :
    (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (∀ a b : S → Finset S, (∀ x, a x ⊆ b x) → rate a ≤ rate b) := by
  refine ⟨fun att => rfl, ?_⟩
  exact ws1_rate_monotone

end P2S9
