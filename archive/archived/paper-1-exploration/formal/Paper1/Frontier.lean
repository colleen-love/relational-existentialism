/-
# The frontier — theorems 2–5, 7 (explored; obstructions reported)

These are the theorems whose honest status is **open or obstructed** on the abstract arena. The exploration
*statements* live here where the arena can express them; the quantitative ones cannot be stated without `Q`'s
**trace** (the open arena seam), and those are recorded in prose in `spec/03-theorem-debt.md`. **No proof is
forced and no `sorry` is used** — what is proved is proved; what is obstructed is stated as a named target or
left to the ledger with the obstruction named.
-/
import Paper1.Existence

namespace Paper1.Frontier

variable {Q : Type*} [CompleteLattice Q] {A : Type*}

/-! ## Theorem 2 — the raising dynamics (A3 as a theorem)

A3 (generativity) was demoted to a theorem: a self-relation should evolve by **bounded, mutual, asymmetric
raising**. The abstract arena captures the **order** half of "raising" but not the **quantitative** half. -/

/-- A **raising seed**: a self-relation the process does not shrink (`R ≤ Φ R`). The order-theoretic content
of "raising" — being pulled upward by the dynamics. -/
def Raising (Φ : Dynamics Q A) (R : SelfRel Q A) : Prop := R ≤ Φ R

/-- **Raising ascends to the self `[proved]`.** A raising seed lies under the derived (greatest) self: the
dynamics carries it up, never past the self. This is the order-half of A3, and it holds from completeness +
monotonicity alone. -/
theorem raising_ascends_to_self (Φ : Dynamics Q A) {R : SelfRel Q A} (h : Raising Φ R) :
    R ≤ derivedSelf Φ :=
  self_greatest Φ h

/-- **Lattice-boundedness is free `[proved, but weak]`.** Every relation is `≤ ⊤`, so the orbit never escapes
the lattice. **Obstruction:** this is *not* A3's capacity bound. A3 asks for a *finite, quantitative* ceiling
(a bounded trace), so that growth is a finite achievement rather than a climb to `⊤`. That bound needs `Q`'s
trace — absent on the abstract arena — so the genuine "bounded raising" is **obstructed**, pending the trace
seam. -/
theorem bounded_by_top (Φ : Dynamics Q A) (R : SelfRel Q A) : Φ R ≤ ⊤ := le_top

/-
**Mutual / non-freezable** and **asymmetric** (sub-debts 2c, 2b): these read off the two-ended converse
weight — the weight of `R` versus `R°` at the two ends. Stating "the coupling moves only when both ends are
live" and "each end raises at its own rate" quantitatively requires comparing `Q`-weights numerically (a
trace), which the abstract `Q` does not provide. **Status: obstructed at the quantitative level; the order
proxy (`Raising`) holds.** See `spec/03-theorem-debt.md` (Theorem 2).
-/

/-! ## Theorems 3, 4, 5, 7 — obstructed at the statement level (need the trace)

The remaining theorems cannot even be *stated* on the abstract arena without `Q`'s trace / measure; forcing a
Lean statement here would smuggle in structure we have flagged as an open seam. They are recorded in
`spec/03-theorem-debt.md` with their precise obstructions. In brief:

* **Theorem 3 (selectivity / sparsity).** "Strong self-relations are few" needs a *measure* of how many
  relations clear a capacity threshold — a counting/density statement over `Q`-weights. No measure without the
  trace. **Obstructed**; depends on Theorem 2's capacity bound.

* **Theorem 4 (self-differentiation).** "The stable self has internal leading/lagging structure" is the
  relational re-grounding of the archived `capacity_orders_couplings`; it needs the per-end *rates* of Theorem
  2. **Obstructed**, downstream of 2.

* **Theorem 5 (stability dichotomy — the falsifiable headline).** "The symmetric configuration is unstable;
  stable selves are asymmetric" is a **dynamical** (repeller/attractor) claim, needing a metric/topology on
  the space of selves — again the trace. **Not settled.** It is to be built *true or false*, not engineered;
  the honest fallback, should symmetry prove only marginal, is "stable differentiation requires asymmetry"
  (≈ Theorem 4). **Obstructed**, downstream of 2; reported, not forced.

* **Theorem 7 (recovery — the real headline).** "The derived fixed self-relation *is* a collection of
  relations asymmetrically co-directing attention" — the proof that derive-don't-define worked. Its
  *structural* skeleton exists (the derived self is a fixed self-relation, `Existence.derivedSelf_fixed`; its
  converse may differ, the seed of asymmetry), but the full lived-description match needs the quantitative
  co-direction of Theorem 2. **Obstructed**, downstream of 2.
-/

end Paper1.Frontier
