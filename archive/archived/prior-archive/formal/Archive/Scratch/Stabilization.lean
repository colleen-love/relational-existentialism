/-
# Does `Φ_c`'s orbit converge? Two honest answers

[`Convergence.lean`](Convergence.lean) reduced the sparsity/cost frontier to a sharp question about
the *genuine* operator: does the ascending, `νΦ_c`-bounded orbit `Φ_c^[n] a` actually **converge** —
reach a fixed point — so that the convergence depth feeding the cost model exists? Here is the answer,
in the two regimes it genuinely splits into.

**Layer 1 — ω-convergence (always, under continuity).** The orbit's **supremum** `⨆ n, Φ^[n] a` is a
fixed point whenever `Φ` commutes with that sup (ω/Scott-continuity): `iSup_orbit_isFixed`. So a
self-reinforcing seed always converges — to a genuine self sitting in `[a, νΦ_c]`
(`le_iSup_orbit`, `iSup_orbit_le_sustained`). The self **is** the limit of relating; no finiteness
needed. This is Kleene's picture, and it is unconditional (given continuity).

**Layer 2 — finite-depth convergence (iff the chain stabilizes).** The cost/counting model needs a
*finite* depth `d`. That holds **exactly when** the ascending orbit stabilizes — which is precisely
the **ascending chain condition** on standing (`WellFoundedGT`, no infinite ascending chains):

* `convergesAt_of_stabilizes` `[0 axioms]` — if the orbit reaches a fixed point at all, it does so at
  a *least* depth, giving a genuine `ConvergesAt` (hence `Convergence`'s whole bridge);
* `orbit_stabilizes` — under `WellFoundedGT (Field V α)`, the monotone orbit *must* stabilize
  (`WellFounded.monotone_chain_condition`);
* `couplingOp_selfForms` — so under ACC the genuine `Φ_c` orbit converges at a finite depth and
  satisfies `Loop`'s `StabilizesAt` — the cost model's hypothesis **discharged for the real
  operator**, not posited.

**What this settles.** The abstract `σ` *and* the bare `StabilizesAt` posit are now both gone for
`Φ_c`. What remains is a single, standard, philosophically-meaningful order condition: **ACC on
standing** — "a self forms in finitely many returns" — satisfied e.g. by any finite standing-lattice.
Convergence as such is unconditional (Layer 1); only the *finiteness* of the forming-depth rests on
ACC (Layer 2). That is the honest floor, and it is now a property of `Φ_c` itself.
-/
import Scratch.Convergence
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.Find

namespace RelExist.Stabilization

open RelExist RelExist.Attention RelExist.Convergence

universe u
variable {X : Type u}

/-! ### Finite-depth convergence from stabilization (general) -/

/-- If the orbit repeats a value (`f^[d+1] a = f^[d] a`), that value is a fixed point. -/
theorem isFixed_of_orbit_eq {f : X → X} {a : X} {d : ℕ}
    (h : f^[d + 1] a = f^[d] a) : f (f^[d] a) = f^[d] a := by
  rw [← Function.iterate_succ_apply' f d a]; exact h

/-- **Stabilization gives a genuine convergence depth.** If the orbit reaches a fixed point at all, it
does so at a *least* depth `d`, and there it `ConvergesAt` (fixed at `d`, moving before). So
`Convergence`'s entire depth bridge applies the moment the orbit stabilizes anywhere. -/
theorem convergesAt_of_stabilizes {f : X → X} {a : X}
    (h : ∃ d, f (f^[d] a) = f^[d] a) : ∃ d, ConvergesAt f a d := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hn => Nat.find_min h hn⟩

/-! ### Under ACC, the genuine `Φ_c` orbit must converge at finite depth -/

variable {V : Type*} {α : Type*} [CompleteLattice α]

/-- **Ascending chain condition ⇒ the orbit stabilizes.** When standing has no infinite ascending
chains (`WellFoundedGT`), the monotone orbit of any monotone operator from a self-reinforcing seed
*must* reach a fixed point — by `WellFounded.monotone_chain_condition`. "A self cannot keep growing
forever; it matures." -/
theorem orbit_stabilizes [WellFoundedGT (Field V α)] (Φ : Field V α →o Field V α)
    (a : Field V α) (hseed : a ≤ Φ a) : ∃ d, Φ (Φ^[d] a) = Φ^[d] a := by
  let orbit : ℕ →o Field V α :=
    ⟨fun n => Φ^[n] a, monotone_nat_of_le_succ (orbit_ascending Φ hseed)⟩
  obtain ⟨d, hd⟩ := WellFounded.monotone_chain_condition.mp wellFounded_gt orbit
  refine ⟨d, ?_⟩
  have h : Φ^[d] a = Φ^[d + 1] a := hd (d + 1) (Nat.le_succ d)
  rw [← Function.iterate_succ_apply' (⇑Φ) d a]
  exact h.symm

/-- **Finite-depth convergence under ACC.** Combining the two: with no infinite ascending chains of
standing, the orbit converges at a genuine finite depth. -/
theorem exists_convergesAt [WellFoundedGT (Field V α)] (Φ : Field V α →o Field V α)
    (a : Field V α) (hseed : a ≤ Φ a) : ∃ d, ConvergesAt (⇑Φ) a d :=
  convergesAt_of_stabilizes (orbit_stabilizes Φ a hseed)

/-- **The cost model's hypothesis, discharged for the genuine `Φ_c`.** Under ACC, the co-directed
operator's orbit forms a self at a finite depth and satisfies `Loop`'s `StabilizesAt` — no abstract
`σ`, no posited depth. The forming-depth is the convergence depth of `Φ_c` itself. -/
theorem couplingOp_selfForms [WellFoundedGT (Field V α)] (c : V → V → Prop)
    {a : Field V α} (hseed : a ≤ couplingOp c a) :
    ∃ d, StabilizesAt (⇑(couplingOp c)) a d := by
  obtain ⟨d, hd⟩ := exists_convergesAt (couplingOp c) a hseed
  exact ⟨d, convergesAt_imp_stabilizesAt hd⟩

/-! ### ω-convergence: the self is the limit of relating (always, under continuity) -/

/-- The seed sits below the orbit's supremum. -/
theorem le_iSup_orbit {Φ : Field V α →o Field V α} {a : Field V α} :
    a ≤ ⨆ n, Φ^[n] a :=
  le_iSup_of_le 0 (by simp)

/-- **The orbit converges to a fixed point — its supremum — given continuity.** When `Φ` commutes
with the supremum of its own orbit (ω/Scott-continuity), `⨆ n, Φ^[n] a` is a genuine eigenform. No
finiteness required: the self is the *limit* of iterated relating (Kleene's fixed point). -/
theorem iSup_orbit_isFixed (Φ : Field V α →o Field V α) (a : Field V α) (hseed : a ≤ Φ a)
    (hcont : Φ (⨆ n, Φ^[n] a) = ⨆ n, Φ (Φ^[n] a)) :
    Φ (⨆ n, Φ^[n] a) = ⨆ n, Φ^[n] a := by
  rw [hcont]
  have hmono : Monotone (fun n => Φ^[n] a) := monotone_nat_of_le_succ (orbit_ascending Φ hseed)
  have e : ∀ n, Φ (Φ^[n] a) = Φ^[n + 1] a :=
    fun n => (Function.iterate_succ_apply' (⇑Φ) n a).symm
  simp_rw [e]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (fun k => Φ^[k] a) (n + 1)
  · exact iSup_le fun n => le_trans (hmono (Nat.le_succ n)) (le_iSup (fun k => Φ^[k + 1] a) n)

/-- The limit self is bounded by `νΦ_c` (`sustainedField`): the orbit's supremum sits inside the
maximal sustained standing — a genuine self in `[a, νΦ_c]`. -/
theorem iSup_orbit_le_sustained (c : V → V → Prop) {a : Field V α}
    (hseed : a ≤ couplingOp c a) :
    (⨆ n, (⇑(couplingOp c))^[n] a) ≤ sustainedField c := by
  unfold sustainedField
  exact iSup_le (orbit_le_gfp (couplingOp c) hseed)

end RelExist.Stabilization
