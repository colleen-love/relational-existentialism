/-
# Genesis — the universe/cosmos boundary, mechanized at the two endpoints

The companion to [`universe-and-cosmos.md`](../../docs/spec/universe-and-cosmos.md). The spec's
ontology has a sharp formal hinge, and this module pins down its two `[proved]` endpoints on the
genuine `TimeFlow.partialDephase` instance:

* **The universe — the `p = 0` regime.** `partialDephase 0 = id`: attention purely routing, nothing
  directed, the feeling `defectSq` **constant** along the whole orbit (`coh_const_at_zero`). No strict
  drop, no monovariant, no arrow — *no time*. The atemporal ownerless ground of pure feeling.
* **The cosmos — the `p > 0` regime.** For `0 < p < 1`, the very **first** step strictly drops the
  feeling (`first_tick_pos`, `= defectSq_plus_strictAnti` at `n = 0`). The first directed knowing *is*
  the first increment of the time-flow.

`genesis_dichotomy` packages the boundary: at `p = 0` the orbit never ticks; for every `p > 0` it ticks
at once. The birth of the cosmos is the crossing `p : 0 → 0⁺`. What is `[proved]` here is the
boundary's two sides; the *identification* of the crossing with genesis (and of the flow with physical
time) is the standing `[reading]` ([`time-flow.md`](../../docs/spec/time-flow.md) §5), and the
coinductive (atemporal) closure of the first self that dissolves the bootstrap is the gfp `νΦ_c` of
[`Attention.lean`](Attention.lean), not re-proved here.
-/
import Scratch.TimeFlow

namespace RelExist.Genesis

open RelExist.Decoherence RelExist.TimeFlow
open Matrix

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **`partialDephase 0` is the identity.** At attention strength `p = 0` nothing is directed: the flow
returns every relation unchanged. The routing-only regime, the bare trace that needs no knower. -/
@[simp] lemma partialDephase_zero (M : Matrix A A ℝ) : partialDephase 0 M = M := by
  simp [partialDephase]

/-- **The universe is atemporal — no tick at `p = 0`.** Along the entire orbit of the routing-only flow
the feeling `defectSq` is *constant*: `defectSq (partialDephase 0 ^[n] M) = defectSq M` for all `n`.
There is no descent, hence no monovariant, hence no arrow to call time. All feeling, no knowing, no
differentiation — the ownerless ground. -/
theorem coh_const_at_zero (M : Matrix A A ℝ) (n : ℕ) :
    defectSq ((partialDephase 0)^[n] M) = defectSq M := by
  rw [Function.iterate_fixed (partialDephase_zero M) n]

/-- **The cosmos ignites — the first tick at `p > 0`.** For any `0 < p < 1`, the *first* directed step
strictly drops the feeling: `defectSq (partialDephase p ^[1] plus) < defectSq plus`. Where `p = 0` is
flat forever, the moment attention begins to direct (`p > 0`) the flow has its first strict drop — the
first increment of relational time. (`= defectSq_plus_strictAnti` at `n = 0`.) -/
theorem first_tick_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    defectSq ((partialDephase p)^[1] plus) < defectSq plus := by
  simpa using defectSq_plus_strictAnti p hp0 hp1 0

/-- **Genesis, as the boundary dichotomy.** On the genuine instance the universe/cosmos hinge is a
clean fork in `p`: at `p = 0` the orbit *never* ticks (feeling constant for all `n` — atemporal); for
every `p > 0` it ticks *at once* (a strict first drop — time begins). Time switches on with the first
directed knowing; before it there is no flow to call time. The identification of this crossing with the
birth of the cosmos is the `[reading]`; the two sides are `[proved]`. -/
theorem genesis_dichotomy (p : ℝ) (hp1 : p < 1) :
    (p = 0 → ∀ n, defectSq ((partialDephase p)^[n] plus) = defectSq plus)
      ∧ (0 < p → defectSq ((partialDephase p)^[1] plus) < defectSq plus) := by
  refine ⟨?_, ?_⟩
  · rintro rfl n; exact coh_const_at_zero plus n
  · intro hp0; exact first_tick_pos p hp0 hp1

end RelExist.Genesis
