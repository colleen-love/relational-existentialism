/-
# The one bridge under the four costumes: depth and cost from `Φ_c`'s orbit itself

Across all four spec pages the *same* open seam recurs: nearly every proved result runs over an
**abstract proxy** for the co-directed operator, and the identification with the genuine `Φ_c`
([`Attention.couplingOp`](Attention.lean)) is the standing open/reading step. In
[03.7](../../docs/archive/03.7-sparsity.md) it is [`Loop.lean`](../RelExist/Loop.lean)'s abstract endomap
`σ` and "connect the threshold to the fixed point"; in [03.4](../../docs/spec/03.4-limits-of-knowing.md)
it is "viewing closes a loop"; in [03.6](../../docs/spec/03.6-the-self-quantified.md) it is "read `x`
off the actual `Φ_c`." They are one bridge, between the lattice/`Type`/Banach machinery one can prove
over and the specific **recurrent, asymmetric, saturating** operator the philosophy commits to.

This module takes that bridge at the node where closing it cashes out the most: it derives the
**depth/threshold structure** of `Loop.lean` from the **convergence behaviour of `Φ_c`'s orbit
directly**, rather than from an abstract `σ`.

* `iter_eq_iterate` — `Loop`'s hand-rolled iteration *is* function iteration `Φ^[n]`: the abstract
  `iter σ` and the genuine orbit are the same thing.
* `ConvergesAt` — the **intrinsic convergence depth** of an orbit: `Φ^[d] a` is the *first* fixed
  point (fixed at `d`, moving before). A property of the actual orbit, not a posit.
* `convergesAt_imp_stabilizesAt` — **the derivation** `[0 axioms]`: an orbit that converges at depth
  `d` satisfies `Loop`'s `StabilizesAt` at `d`. So the depth `Loop` *assumed* (as abstract
  `StabilizesAt`) is now *read off* the operator's convergence.
* `couplingOp_loopR_isEigen_iff` — the consequence: `Loop`'s threshold↔fixed-point bridge
  (`loop_R(x) = x ⟺ d·λ ≤ β`) now runs over the **genuine `Φ_c = couplingOp c`**, with `d` its orbit's
  convergence depth — discharging the "abstract `σ`" costume for the depth.
* `convergedValue_le_sustained` — the converged value is a real self bounded by `νΦ_c`
  (`sustainedField`): it sits inside the eigenstructure, not beside it.
* `selfCost_le_valuationGain` — and the **per-return cost `λ`** is the orbit's actual standing
  increment: given a valuation `μ`, if each return adds at least `λ`, the standing gained reaching the
  eigenform is at least `selfCost d λ = d·λ`. So `λ` too is read off the orbit, *given a valuation*.

**What is discharged, and what remains.** Discharged: the **depth `d`** — the load-bearing quantity
(A3's floor `d ≥ 2`) — is no longer an abstract `StabilizesAt` posit but the convergence depth of the
genuine `Φ_c` orbit, and `Loop`'s whole bridge instantiates at `couplingOp`. Still posited: a
**valuation `μ : X → ℕ`** turning lattice standing into a numeric cost (the residue of "λ from the
orbit"), and — the deeper frontier — that the orbit *does* converge at a finite depth `≥ 2` for the
selves the theory counts. The abstract `σ` is gone; what is left is a measure and a convergence
hypothesis about the real operator, both about `Φ_c` itself.
-/
import RelExist.Loop
import Scratch.Attention

namespace RelExist.Convergence

open RelExist RelExist.Attention

universe u
variable {X : Type u}

/-! ### `Loop`'s iteration is the genuine orbit -/

/-- `Loop.iter` is function iteration: the abstract `iter σ` and the orbit `σ^[n]` coincide. -/
theorem iter_eq_iterate (f : X → X) (n : ℕ) (x : X) : iter f n x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, Function.iterate_succ', Function.comp_apply, ih]

/-! ### Convergence depth, and the derivation of `StabilizesAt` -/

/-- An orbit **converges at depth `d`**: `f^[d] a` is the *first* fixed point — a genuine eigenform at
`d`, and not yet one before. This is the intrinsic stabilization index of the actual orbit, replacing
`Loop`'s abstract `StabilizesAt`. -/
def ConvergesAt (f : X → X) (a : X) (d : ℕ) : Prop :=
  f (f^[d] a) = f^[d] a ∧ ∀ n, n < d → f (f^[n] a) ≠ f^[n] a

/-- **The derivation.** An orbit that converges at depth `d` satisfies `Loop`'s `StabilizesAt` at
`d`: the abstract depth structure is *read off* the operator's convergence. Once fixed at `d` it
stays fixed (a fixed point iterated is itself); before `d` it is not yet fixed. -/
theorem convergesAt_imp_stabilizesAt {f : X → X} {a : X} {d : ℕ}
    (h : ConvergesAt f a d) : StabilizesAt f a d := by
  obtain ⟨hfix, hbefore⟩ := h
  intro n
  rw [iter_eq_iterate]
  show f (f^[n] a) = f^[n] a ↔ d ≤ n
  constructor
  · intro hn
    by_contra hlt
    exact hbefore n (Nat.not_le.mp hlt) hn
  · intro hdn
    have he : f^[n] a = f^[n - d] (f^[d] a) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hdn]
    rw [he, Function.iterate_fixed hfix]
    exact hfix

/-! ### The bridge, now over the genuine `Φ_c` -/

variable {V : Type*} {α : Type*} [CompleteLattice α]

/-- **The threshold↔fixed-point bridge over the actual co-directed operator.** `Loop.lean`'s bridge
ran over an abstract `σ`; here `σ` is the genuine `Φ_c = couplingOp c`, and the depth `d` is the
intrinsic convergence depth of *its* orbit (`ConvergesAt`). The budgeted loop is an eigenform iff the
budget covers `d·λ`. This is the "abstract `σ`" costume of the seam, discharged for the depth. -/
theorem couplingOp_loopR_isEigen_iff (c : V → V → Prop) (a : Field V α) (d lam beta : ℕ)
    (hlam : 0 < lam) (hconv : ConvergesAt (⇑(couplingOp c)) a d) :
    IsEigen (⇑(couplingOp c)) (loopR (⇑(couplingOp c)) lam beta a) ↔ d * lam ≤ beta :=
  loopR_isEigen_iff (⇑(couplingOp c)) a d lam beta hlam (convergesAt_imp_stabilizesAt hconv)

/-- The converged orbit value is a genuine self **bounded by `νΦ_c`** (`sustainedField`): from a
self-reinforcing seed it sits inside the maximal sustained standing, not beside it — tying the
convergence depth into the eigenstructure of [03.6](../../docs/spec/03.6-the-self-quantified.md). -/
theorem convergedValue_le_sustained (c : V → V → Prop) {a : Field V α} (d : ℕ)
    (hseed : a ≤ couplingOp c a) :
    (⇑(couplingOp c))^[d] a ≤ sustainedField c := by
  unfold sustainedField
  exact orbit_le_gfp (couplingOp c) hseed d

/-! ### The per-return cost is the orbit's standing increment -/

/-- Telescoping: if each of the first `d` returns adds at least `lam` to the valuation `μ`, the
standing at depth `d` exceeds the seed's by at least `d·λ`. -/
theorem valuationGain (f : X → X) (a : X) (μ : X → ℕ) (lam : ℕ) :
    ∀ d, (∀ n, n < d → μ (f^[n] a) + lam ≤ μ (f^[n + 1] a)) → μ a + d * lam ≤ μ (f^[d] a) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hstep
    have ihd : μ a + d * lam ≤ μ (f^[d] a) := ih (fun n hn => hstep n (Nat.lt_succ_of_lt hn))
    have hlast : μ (f^[d] a) + lam ≤ μ (f^[d + 1] a) := hstep d (Nat.lt_succ_self d)
    rw [Nat.succ_mul]
    omega

/-- **The per-return cost `λ` is the orbit's own standing increment.** Given a standing-valuation `μ`,
if each return adds at least `λ`, the total standing gained reaching the eigenform is at least
`Loop.selfCost d λ = d·λ`. So the abstract per-return cost is read off `Φ_c`'s orbit — `λ` made
intrinsic, modulo the valuation `μ`. -/
theorem selfCost_le_valuationGain (f : X → X) (a : X) (μ : X → ℕ) (d lam : ℕ)
    (hstep : ∀ n, n < d → μ (f^[n] a) + lam ≤ μ (f^[n + 1] a)) :
    selfCost d lam ≤ μ (f^[d] a) - μ a := by
  have h := valuationGain f a μ lam d hstep
  show d * lam ≤ μ (f^[d] a) - μ a
  omega

end RelExist.Convergence
