# WS4 — Graded Parthood: Obligation Analysis

## What is at stake

WS4 must enrich the containment relation of the carrier from a two-valued membership predicate to a **graded** one, valued in a residuated ordered structure (interval `[0,1]`, a quantale `Q`, or a fixed subposet), and show the enriched observation functor `W_Q` still supports the carrier constructions inherited from WS1/WS2/WS3: a terminal coalgebra exists, bisimulation collapses to identity, weak pullbacks are preserved, and the weak composition law of WS3 persists.

The non-triviality has three coupled sources:

1. **The functor changes.** Replacing `P_κ` (a subobject of `Set`-powerset) with `W_Q κ X = {ρ : X → Q // supp(ρ) < κ}` (a bounded `Q`-weighting) changes the endofunctor whose terminal coalgebra is being built. Every property proved for `P_κ` (QPF structure, weak-pullback preservation, Lambek iso) must be re-established for `W_Q`, and some are known to be fragile: weighted/probabilistic functors can **fail** weak-pullback preservation, at which point bisimilarity and behavioral equivalence come apart, breaking criterion (ii).

2. **A second parameter appears.** The quantale `Q` joins the cardinal bound `κ`. The two interact: the join operation of `W_Q` (needed for the WS3 composition operator) is the `Q`-sup over a `< κ`-indexed family, so the `< κ` bound survival now depends on both `κ`'s regularity *and* `Q`'s completeness/distributivity.

3. **Two inherited ratification duties.** WS4 owns (a) weak-pullback preservation for its chosen functor, and (b) persistence of a well-behaved weak distributive law under the enrichment — because WS3 delivered criterion (iv) only via a weak Egli–Milner law whose canonicity is unproven, and WS4's functor change could destroy even the weak law.

The obligation **fails** if: no `Q`-enriched functor simultaneously (i) has a set-sized terminal coalgebra, (ii) preserves weak pullbacks / keeps bisim = behavioral equivalence, and (iii) carries a weak composition law reducing correctly to WS3's when `Q = 2`. A sharp proof that these are jointly unsatisfiable is itself a valid (impossibility) outcome.

---

## Candidate framings

### Framing 1 — Quantale-weighted functor `W_Q`, full re-derivation

**Idea.** Define `W_Q κ X` as `< κ`-supported functions `X → Q` for a fixed commutative unital quantale `Q`. Re-run the entire WS1→WS3 stack for this functor: QPF instance, terminal coalgebra, bisim = identity, weak-pullback preservation, weak law.

**Ambient theory.** ZFC; AFA modeled coalgebraically (terminal `W_Q`-coalgebra, no set-theoretic AFA axiom). `F = W_Q κ`. `T` = the `Q`-weighted-multiset monad on the same functor (unit = point mass, join = `Q`-sup of scaled weights). `λ` = weak (Egli–Milner-analogue) law only; strict law expected impossible (inherit WS3 Part A).

**Proof strategy.** Show `W_Q` is a QPF (shapes = `κ.ord.toType`, positions = initial segments, `abs` carries the `Q`-labeling); get terminal coalgebra from `Cofix`. Barr-lift the `Q`-metric relation and prove weak-pullback preservation by middle-point selection *weighted* by `Q` — this is the load-bearing step and the likely point of failure. Define graded `alg` via the Lambek inverse of the `Q`-sup join.

**Lean signature.**
```lean
structure WQObj (Q : Type u) [CommMonoid Q] [CompleteLattice Q]
    (κ : Cardinal.{u}) (X : Type u) where
  wt   : X → Q
  supp : Set X := {x | wt x ≠ ⊥}
  bdd  : Cardinal.mk ↥{x | wt x ≠ ⊥} < κ

def WQMap (Q) [CommMonoid Q] [CompleteLattice Q] {X Y : Type u}
    (f : X → Y) (ρ : WQObj Q κ X) : WQObj Q κ Y := ...

theorem ws4_terminal (Q) [CommMonoid Q] [CompleteLattice Q]
    (hreg : κ.IsRegular) : ∃ U : WQCoalg Q κ, IsTerminalWQCoalg U

theorem ws4_bisim_eq (Q) [CommMonoid Q] [CompleteLattice Q]
    (hreg : κ.IsRegular) (U : WQCoalg Q κ) (hU : IsTerminalWQCoalg U)
    (R : U.X → U.X → Prop) (hR : WQBisim U R) : ∀ x y, R x y → x = y

theorem ws4_weak_pullback (Q) [CommMonoid Q] [CompleteLattice Q]
    (hreg : κ.IsRegular) : WQPreservesWeakPullback Q κ
```

**Success condition.** All four theorems `sorry`-free and axiom-free (Mathlib's three only), with `Q = Prop`/`Bool`-instantiation recovering the WS2 statements definitionally.

**Failure.** `ws4_weak_pullback` provably false for the chosen `Q` (e.g. `Q = [0,1]` under `+`-truncated), witnessed by a cospan whose `WQ`-lift is not preserved → `IsEmpty` of the preservation predicate; or no QPF instance (terminal coalgebra non-existence).

**Trade-offs.** Most faithful to the charter's "enrich over a quantale," maximally general. Highest risk: weak-pullback preservation for genuinely quantitative `Q` is exactly the known danger zone. Heavy Lean cost (rebuild everything).

---

### Framing 2 — Restrict to weak-pullback-preserving quantales (a *provable* subclass)

**Idea.** Don't claim all quantales work. Identify a checkable condition on `Q` (e.g. `Q` a *completely distributive* / *frame*-like quantale, or `Q` = a totally ordered complete lattice with `⊗ = ∧`) under which `W_Q` provably preserves weak pullbacks, and prove the WS stack only for `Q` in that class.

**Ambient theory.** As Framing 1, but `Q` constrained by a typeclass `[GoodQuantale Q]` bundling completeness + the distributivity law that makes middle-point selection go through.

**Proof strategy.** Prove a metatheorem: `[GoodQuantale Q] → WQPreservesWeakPullback Q κ`. Then bisim = behavioral equivalence follows uniformly. Instantiate with the Łukasiewicz/Gödel `[0,1]`-with-`min` quantale to exhibit non-emptiness of the class.

**Lean signature.**
```lean
class GoodQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  tensor_iSup : ∀ (a : Q) (s : Set Q), a * (sSup s) = sSup ((a * ·) '' s)
  -- + whatever the weak-pullback proof consumes

theorem ws4_good_weak_pullback (Q) [GoodQuantale Q] (hreg : κ.IsRegular) :
    WQPreservesWeakPullback Q κ

theorem ws4_good_class_nonempty :
    GoodQuantale (WithTop (OrderDual ℝ≥0))   -- or Gödel [0,1]
```

**Success condition.** The metatheorem proved, plus at least one instance, plus a definitional-recovery lemma that `Bool : GoodQuantale` reproduces WS2.

**Failure.** The distributivity axiom is inconsistent with `< κ`-support survival (join escapes the bound), or the only quantales satisfying it are the trivial `{⊥,⊤}` → grading collapses to two-valued (non-degeneracy of grading fails).

**Trade-offs.** Honest and likely provable; converts a risky universal claim into a scoped one. Cost: leaves open whether the charter's *intended* `[0,1]` grading is in the good class — must be checked, and may not be for additive `[0,1]`.

---

### Framing 3 — Grading as a *coalgebra over a fixed base*, not a new functor

**Idea.** Avoid changing the functor at all. Keep `P_κ` as the observation functor; model grading as an **extra structure map** `g : X → (X →₀ Q)` (a `Q`-labeling of the already-existing edges), living in the same terminal `νP_κ`. Graded parthood becomes a derived predicate, not a new carrier.

**Ambient theory.** `F = P_κ` unchanged; carrier `= νP_κ` from WS2, reused verbatim. `Q` a quantale. No new terminal-coalgebra obligation.

**Proof strategy.** Define `grade : (νPk κ).X → (νPk κ).X → Q` by terminal corecursion from the edge-labeling; prove it refines binary membership (`grade x y ≠ ⊥ ↔ y ∈ dest x`) and is compatible with `alg` (WS3). Bisim = identity is inherited free from WS2 — no re-proof.

**Lean signature.**
```lean
noncomputable def grade (Q) [CommMonoid Q] [CompleteLattice Q]
    (lab : (νPk κ).X → (νPk κ).X → Q) : (νPk κ).X → (νPk κ).X → Q := ...

theorem grade_refines (Q) [CommMonoid Q] [CompleteLattice Q]
    (x y : (νPk κ).X) : grade Q lab x y ≠ ⊥ ↔ y ∈ ((νPk κ).str x).1

theorem grade_alg_compat (Q) [CommMonoid Q] [CompleteLattice Q]
    (hreg : κ.IsRegular) (t : PkObj κ (νPk κ).X) (y : (νPk κ).X) :
    grade Q lab (alg hreg t) y = ⨆ x ∈ t.1, grade Q lab x y
```

**Success condition.** Grading defined and compatible with WS3's `alg` (Egli–Milner join becomes `Q`-sup), with WS2/WS3 theorems reused unmodified.

**Failure.** The labeling cannot be made canonical/bisimulation-invariant — two bisimilar (hence equal, by WS2) states carry different grades → `grade` ill-defined on the quotient carrier. This is the crux risk: grading may force distinctions the terminal carrier already collapsed.

**Trade-offs.** Cheapest; sidesteps the weak-pullback re-proof and *cannot* invalidate WS1/WS2. But it may not satisfy the charter's intent that grading be *constitutive* of the objects (Framing 1's stronger reading) — grading here is decoration, not ontology. If `grade` fails bisimulation-invariance, that failure is itself informative: it says genuine grading *requires* leaving `P_κ`, vindicating Framing 1's functor change.

---

### Framing 4 — `Q`-enriched-category / Lawvere-metric carrier

**Idea.** Read "whole or in part" as enrichment in the Lawvere sense: the carrier is a `Q`-category (objects + hom-object `X(x,y) ∈ Q` = degree to which `x` contains `y`), and the terminal coalgebra is taken in `Q-Cat` rather than `Set`.

**Ambient theory.** Base = the closed symmetric monoidal `V = Q` (a commutative quantale as a thin monoidal category). `F` = a `V`-enriched powerset endofunctor on `V-Cat`. Terminal object sought in `V-Coalg`.

**Proof strategy.** Use America–Rutten metric-space final-coalgebra machinery generalized to `Q`-categories: realize `νF` as a Cauchy-complete `Q`-category; contraction gives existence. Bisim = identity becomes "the terminal `Q`-category is skeletal / separated."

**Lean signature.**
```lean
structure QCat (Q : Type u) [CommMonoid Q] [CompleteLattice Q] where
  carrier : Type u
  hom     : carrier → carrier → Q
  id_le   : ∀ x, 1 ≤ hom x x
  comp_le : ∀ x y z, hom x y * hom y z ≤ hom x z

theorem ws4_qcat_terminal (Q) [CommMonoid Q] [CompleteLattice Q]
    (hreg : κ.IsRegular) : ∃ U : QCatCoalg Q κ, IsTerminalQCatCoalg U

theorem ws4_qcat_separated (Q) [CommMonoid Q] [CompleteLattice Q]
    (U : QCatCoalg Q κ) (hU : IsTerminalQCatCoalg U) (x y : U.carrier) :
    (U.hom x y = 1 ∧ U.hom y x = 1) → x = y
```

**Success condition.** Terminal `Q`-categorical coalgebra exists and is separated (the enriched analogue of bisim = identity).

**Failure.** No Cauchy-complete separated terminal object (enriched Lambek obstruction), or separatedness fails so distinct objects are at `Q`-distance `1` (enriched collapse). Also fails if `Q-Cat` lacks the zero object / bound needed to stay set-sized.

**Trade-offs.** Most conceptually aligned with the Lawvere-metric remark and with §3.6's contraction/convergence apparatus (shares infrastructure with WS5). Highest formalization cost in Lean (enriched category theory is thin in Mathlib). Ties WS4's success to metric machinery WS5 also needs — shared risk, shared payoff.

---

### Framing 5 — Weak-law-persistence as the *primary* obligation (WS3 hand-off first)

**Idea.** Treat WS4's core deliverable as the WS3-pinned duty: prove that a well-behaved weak distributive law survives the enrichment, *conditionally* on whatever functor/quantale is chosen. Make the weak law, not the carrier, the theorem.

**Ambient theory.** `F = W_Q κ` (parametric); `T` = `Q`-weighted composition monad; `λ_w` = graded Egli–Milner law `dest(alg t) = ⨆_{x} (t-weight of x) ⊗ dest x`.

**Proof strategy.** Assume (as hypotheses, discharged by Framing 1/2 separately) terminality + Lambek for `W_Q`. Define graded `alg` via Lambek inverse of the `Q`-weighted join; prove the weak-law multiplication square (`alg_pentagon`, `alg_join` analogues) reduce to `Q`-sup associativity + `⊗`-distributivity. Prove reduction: `Q = Bool` gives WS3's `alg` back.

**Lean signature.**
```lean
noncomputable def wqAlg (Q) [GoodQuantale Q] (hreg : κ.IsRegular)
    (hU : IsTerminalWQCoalg (νWQ Q κ)) (t : WQObj Q κ (νWQ Q κ).X) : (νWQ Q κ).X

theorem ws4_weak_law_persists (Q) [GoodQuantale Q] (hreg : κ.IsRegular) :
    ∀ t, (νWQ Q κ).str (wqAlg Q hreg _ t)
       = wqJoin Q hreg (WQMap Q (νWQ Q κ).str t)

theorem ws4_weak_law_reduces (hreg : κ.IsRegular) :
    ∀ t, wqAlg Bool hreg _ t = Series3.WS3.alg hreg (boolToPk t)
```

**Success condition.** Graded weak law proved coherent *and* proved to specialize to WS3's — closing criterion (iv)'s pending ratification.

**Failure.** No graded law satisfies the multiplication square for any non-trivial `Q` (weak-law non-persistence) → criterion (iv) stays permanently Partial; or the reduction to `Q = Bool` disagrees with WS3's `alg`, showing the graded law is not a conservative extension.

**Trade-offs.** Directly discharges the criterion-(iv)-blocking hand-off, which is the highest-value residual. But it is conditional on the carrier obligation (Framing 1/2) — cannot stand alone; must be paired.

---

### Framing 6 — Impossibility-first (dual of Framing 1)

**Idea.** Attempt to *prove* that no non-trivial `Q`-grading can coexist with all of {set-sized terminal coalgebra, bisim = identity, weak-pullback preservation} — i.e., grading and the WS2 collapse are jointly unsatisfiable for genuinely quantitative `Q`.

**Ambient theory.** `F = W_Q`; the target is `IsEmpty` of the full-characterization structure for `Q` outside a degenerate class.

**Proof strategy.** Adapt the WS3 Klin–Salamanca diagonal: build a fixed finite `Q`-weighted cospan whose Barr lift is not preserved, for every `Q` with two comparable-but-distinct non-⊥ degrees, forcing bisim ≠ behavioral equivalence.

**Lean signature.**
```lean
theorem ws4_no_graded_characterization (Q) [CommMonoid Q] [CompleteLattice Q]
    (hnontrivial : ∃ a b : Q, a ≠ b ∧ a ≠ ⊥ ∧ b ≠ ⊥ ∧ a ≤ b)
    (hreg : κ.IsRegular) : IsEmpty (WQFullCharacterization Q κ)
```

**Success condition.** The `IsEmpty` proved for the stated non-triviality class — a sharp negative, valid per the charter's outcome vocabulary.

**Failure.** (As an outcome, this *is* the negative branch; it "fails to be impossible" if a counterexample quantale is exhibited, which just routes back to Framing 1/2.)

**Trade-offs.** Cleanest possible resolution if grading genuinely can't be reconciled — turns a risk into a theorem. But committing to it prematurely wastes effort if Framing 2's good-quantale class is non-empty; run it only after Framing 2's instance search stalls.

---

## Cross-cutting trade-off summary

The decisive fork is **whether grading changes the carrier (Framings 1, 2, 4, 6) or decorates it (Framing 3)**. Decoration is safe but may not be constitutive; a new functor is faithful but re-opens weak-pullback preservation — the single property whose failure would break criterion (ii).

The two ratification duties split cleanly: **weak-pullback preservation** is owned by the carrier framings (1/2/4/6), **weak-law persistence** by Framing 5. Framing 5 is conditional and must be paired with 1 or 2.

Recommended sequencing: attempt **Framing 2** (scoped, provable) to fix a good-quantale class; **pair with Framing 5** to discharge the WS3 hand-off; keep **Framing 3** as a cheap fallback that provably cannot damage upstream; hold **Framing 6** as the terminal negative outcome if the good-quantale class collapses to trivial. **Framing 1** is the maximal target subsumed by 2 once the class is fixed; **Framing 4** is the high-cost/high-alignment option that shares infrastructure with WS5 and is worth it only if the metric route is pursued program-wide.

Each framing's failure mode is a distinct, informative result — non-existence (no QPF/terminal), collapse (grading trivializes or bisim collapses distinctions grading needs), non-preservation (weak pullbacks lost → bisim ≠ behavioral), or non-persistence (no graded weak law) — and per the charter's methodology any of these, proved sharply, is a valid terminal outcome rather than a defeat.
