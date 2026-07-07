# WS4 Triage

## Decidable-on-paper triage per candidate

Each candidate is checked against gates that can be settled by inspection of the upstream Lean artifacts and finite algebra — no new proof effort required to answer them.

**Gate definitions (all decidable by inspection):**

- **G1 — Carrier reuse.** Does the candidate reuse `νPk`/`ws2_characterization` verbatim, or must it rebuild a terminal coalgebra for a new functor? (Rebuild = re-open QPF + `Cofix` + weak-pullback + Lambek.)
- **G2 — Weak-pullback status.** Is weak-pullback preservation *already proved* (inherited from `ws2.lean`), *newly required and plausibly true*, or *newly required and at genuine risk of failing*?
- **G3 — `< κ`-bound survival.** Does the join/sup needed by the composition operator provably stay `< κ` under the upstream hypotheses (`hreg : κ.IsRegular`, from `pkJoin`/`iSup_lt_of_isRegular`), or does it need a *new* completeness/distributivity axiom on `Q` that could escape the bound?
- **G4 — Mathlib support.** Are the required structures present in Mathlib (`QPF`, `Cofix`, `CompleteLattice`, `CommMonoid`) or do they require building absent infrastructure (enriched category theory, `V-Cat` final coalgebras)?
- **G5 — Bisim-invariance hazard.** Can the candidate's central object *fail to be well-defined on the terminal carrier* because WS2 already forced bisimilar states equal? (Decidable: does the construction assign data to edges that bisimulation would have to preserve?)
- **G6 — Criterion-(iv) closure.** Does the candidate, if it succeeds, actually discharge the WS3-pinned weak-law-persistence hand-off, or leave it open?
- **G7 — Standalone.** Can the candidate be a complete theorem on its own, or is it conditional on another candidate?

**Decidability note:** every entry below is read off the imported files or from finite quantale algebra. None requires running a proof.

| | G1 Carrier | G2 Weak-pullback | G3 `<κ` bound | G4 Mathlib | G5 Bisim-inv hazard | G6 Closes (iv) | G7 Standalone |
|---|---|---|---|---|---|---|---|
| **F1** full `W_Q` | Rebuild | **At risk** | New axiom on `Q` | OK (`Cofix`) | Low | Yes (with F5) | Yes |
| **F2** good-`Q` class | Rebuild | Plausible *by construction* of class | Provable *if* class demands it | OK | Low | Yes (with F5) | Yes |
| **F3** grading-as-decoration | **Reuse** | **Inherited** | Provable (`pkJoin`) | OK | **HIGH** | No | Yes |
| **F4** `Q`-Cat / Lawvere | Rebuild in `V-Cat` | Recast as separatedness | Needs new axiom | **Absent** (no enriched cat) | Medium | Partial | No (needs WS5) |
| **F5** weak-law-persistence | (assumes carrier) | (assumes) | Provable given good-`Q` | OK | Low | **Yes — directly** | **No** (conditional) |
| **F6** impossibility-first | N/A (proves `IsEmpty`) | Proves *failure* of it | N/A | OK | N/A | Resolves negatively | Yes |

## Reading the table

Three candidates are eliminated on decidable grounds before any proof:

- **F4** fails **G4** outright: Mathlib has no usable enriched-category / `V-Cat` terminal-coalgebra machinery. Building it is a program in itself, and **G7** makes it non-standalone (coupled to WS5's metric route). Defer.
- **F3** is the cheapest (**G1 reuse, G2 inherited**) but carries a **HIGH G5 hazard** *and* fails **G6**: it cannot close the criterion-(iv) hand-off because grading-as-decoration never touches the weak law. The G5 hazard is not merely a risk — it is close to a paper theorem that it *fails*: WS2's `ws2_bisim_behavioural` forces bisimilar states equal, so any edge-labeling `grade` that distinguishes bisimilar configurations is ill-defined on the quotient carrier. So F3 is either trivial (grades collapse with the edges) or ill-defined. Keep only as a fallback sanity check, not a deliverable.
- **F5** fails **G7**: it is conditional on a carrier existing. It cannot be the primary selection, but it is exactly the piece that closes **G6**.

That leaves the real decision between **F1** and **F2**, with **F6** as the negative branch and **F5** as a mandatory companion.

**F1 vs F2 is settled by G2 + G3.** F1's weak-pullback preservation is *at genuine risk* for arbitrary `Q` — this is the known failure of quantitative functors, and it is not decidable on paper whether it holds for "all quantales" (it doesn't). F2 dissolves exactly this: by *defining* the good-quantale class through the distributivity law the weak-pullback proof consumes, G2 becomes "plausible by construction" and G3 becomes "provable because the class demands the completeness the bound needs." F2 is F1 restricted to precisely the quantales where the risky gate is discharged by hypothesis rather than by hope.

**Selection: F2 (good-quantale class) as the carrier deliverable, paired with F5 (weak-law persistence) to close criterion (iv), with F6 held as the terminal negative outcome if the good-quantale class proves to contain only degenerate `Q`.**

The pairing is the honest unit: F2 delivers the carrier + weak-pullback + bisim = identity for a checkable class; F5 rides on F2's carrier to discharge the WS3 hand-off; and the whole thing is only meaningful if the class is non-degenerate, which is itself a decidable instance-exhibition obligation.

---

# WS4 Design: Graded Parthood over a Good Quantale

## 0. Selection statement

Build the `Q`-weighted `< κ`-supported observation functor `W_Q` for `Q` in a typeclass `GoodQuantale`; prove it is a QPF and hence has a terminal coalgebra via `Cofix`; prove weak-pullback preservation, bisim = identity, and behavioural equivalence = identity for it; then define the graded composition operator via the Lambek inverse and prove the graded weak distributive law persists and reduces to WS3's `alg` at `Q = Bool`. Exhibit at least one non-degenerate instance.

## 1. Ambient theory and imports

- **Set theory:** ZFC. AFA modeled **coalgebraically** (the terminal `W_Q`-coalgebra *is* the non-well-founded universe for the graded functor); **no set-theoretic AFA axiom imported**, matching WS1/WS2/WS3.
- **Functor `F`:** `W_Q κ X = { ρ : X → Q // supp(ρ) is < κ-sized }`, `supp(ρ) = {x | ρ x ≠ ⊥}`.
- **Monad `T`:** the `Q`-weighted composition monad on `W_Q`; unit = point mass at `⊤`, join = `Q`-sup of `⊗`-scaled fibres.
- **Distributive law:** **weak only** — the graded Egli–Milner law. The strict law is inherited-impossible: WS3's `ws3_no_distributive_law` specializes back at `Q = Bool`, and no strict law can exist for a functor that surjects onto `P_κ`. WS4 does **not** re-attempt a strict law.

**Imported upstream theorems (used as black boxes, cited by name):**

From `ws1.lean`:
- `PkObj`, `PkMap`, `PkMap_id`, `PkMap_comp` — the `P_κ = W_Bool` reduction target.
- `qpfPk` (the QPF pattern: shapes `κ.ord.toType`, positions initial segments `{b // b < a}`, `abs = range`, `reprPk` the enumeration) — **the template `W_Q`'s QPF instance follows**.
- `card_typein_toType_lt`, `mk_range_le` — the bound arithmetic reused for `W_Q`'s `abs`.
- `IsTerminalCoalg`, `hom_unique`, `endo_eq_id`, `lambek` — the terminal-coalgebra API, generalized to `W_Q`.

From `ws2.lean`:
- `PkRel`, `PkRel_le_comp`, `PkRel_comp_le`, `PkRel_functorial`, `ws2_weak_pullback` — **the weak-pullback proof template**; `W_Q`'s version is the `Q`-weighted analogue of `PkRel_le_comp`'s middle-point selection.
- `ws2_bisim_behavioural`, `diagBisim`, `bisim_comp` — the behavioural-equivalence and composition machinery whose `Q`-lift WS4 rebuilds.
- `ws2_characterization` — the target shape WS4's deliverable mirrors, plus the reduction anchor at `Q = Bool`.

From `ws3.lean`:
- `pkJoin`, `pkJoin_val`, `mem_pkJoin`, `Cardinal.iSup_lt_of_isRegular` usage — **the bound-survival template**; `wqJoin` is its `Q`-sup generalization and `hreg` remains load-bearing for the same reason.
- `alg`, `alg_pentagon`, `alg_unit_idem`, `alg_join`, `reflects_part`, `omega_fix` — the weak-law coherence WS4's graded `alg` must reduce to.
- `ws3_no_distributive_law` — cited to justify not attempting a strict law; specializes to the `Q=Bool` no-go.
- `WeakBialgebra` — the structure WS4's `GradedWeakBialgebra` extends.

## 2. The `GoodQuantale` class (the pivot definition)

The class must bundle exactly the algebraic facts the two risky gates (G2, G3) consume, and no more, so that instance-checking is decidable.

```lean
class GoodQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  -- ⊗ distributes over arbitrary joins (residuation / quantale law): closes G2
  tensor_sSup : ∀ (a : Q) (s : Set Q), a * sSup s = ⨆ b ∈ s, a * b
  sSup_tensor : ∀ (a : Q) (s : Set Q), sSup s * a = ⨆ b ∈ s, b * a
  -- unit is the top (so point-mass unit interacts correctly with support): closes reduction
  one_eq_top  : (1 : Q) = ⊤
  -- ⊥ is a ⊗-annihilator (so support = "non-⊥" is stable under ⊗): closes G3 support control
  bot_tensor  : ∀ a : Q, ⊥ * a = ⊥
```

**Why these four and nothing else.** `tensor_sSup`/`sSup_tensor` are exactly what the weak-pullback middle-point selection needs to commute `⊗` past the witness join (G2). `bot_tensor` guarantees the support of a `⊗`-scaled join stays inside the union of supports, so the `< κ` bound is inherited by the same `iSup_lt_of_isRegular` argument WS3 uses (G3). `one_eq_top` makes the point-mass unit a genuine "full-degree singleton," which is what reduces to WS3's `pkPure` at `Q = Bool`.

**Decidable instance check.** For any concrete `Q`, all four are finite/algebraic conditions verifiable without the WS stack.

## 3. Definitions

```lean
-- The functor object
structure WQObj (Q) [GoodQuantale Q] (κ : Cardinal.{u}) (X : Type u) where
  wt  : X → Q
  bdd : Cardinal.mk ↥{x | wt x ≠ ⊥} < κ

-- Functorial action: pushforward with Q-sup over fibres
noncomputable def WQMap (Q) [GoodQuantale Q] {X Y : Type u}
    (f : X → Y) (ρ : WQObj Q κ X) : WQObj Q κ Y :=
  ⟨fun y => ⨆ x ∈ f ⁻¹' {y}, ρ.wt x, by
    -- support of pushforward ⊆ f '' support, which is < κ by mk_image_le
    ...⟩

-- Coalgebra, terminality (mirrors ws1)
structure WQCoalg (Q) [GoodQuantale Q] (κ) where
  X : Type u
  str : X → WQObj Q κ X
def IsTerminalWQCoalg (Q) [GoodQuantale Q] (U : WQCoalg Q κ) : Prop := ...

-- The Q-weighted join (T-monad multiplication)
noncomputable def wqJoin (Q) [GoodQuantale Q] (hreg : κ.IsRegular)
    (tt : WQObj Q κ (WQObj Q κ X)) : WQObj Q κ X :=
  ⟨fun x => ⨆ ρ, tt.wt ρ * ρ.wt x, ...⟩   -- bound via bot_tensor + iSup_lt_of_isRegular

-- Point mass (T-unit)
noncomputable def wqPure (Q) [GoodQuantale Q] (x : X) : WQObj Q κ X :=
  ⟨fun y => if y = x then ⊤ else ⊥, ...⟩

-- Barr relation lifting (Q-weighted)
def WQRel (Q) [GoodQuantale Q] {X Y} (R : X → Y → Prop) :
    WQObj Q κ X → WQObj Q κ Y → Prop := ...
```

## 4. Proof architecture (dependency-ordered)

**Layer A — Functor + QPF (template: `qpfPk`).**
1. `WQMap_id`, `WQMap_comp` — functoriality (uses `tensor_sSup` to push weights through composition).
2. `qpfWQ : QPF (WQObj Q κ)` — shapes `κ.ord.toType`, positions `{b // b < a}`, `abs ⟨a,f⟩ = ` the `Q`-labeled range, `repr` enumerates support by `(#supp).ord`. **Directly parallels `reprPk`/`absPk`; the only new content is carrying the `Q`-label along the enumeration.**
3. `exists_terminal_wq : ∃ U, IsTerminalWQCoalg U` — via `Cofix (WQObj Q κ)`, `Cofix.corec`/`dest_corec`/`bisim'`. **Structurally identical to `exists_terminal_coalg`.**

**Layer B — Lambek + bisim (template: `lambek`, `bisim_eq`).**
4. `wqLambek : Function.Bijective U.str` — verbatim generalization of `lambek` (uses only terminality + `WQMap_comp`/`WQMap_id`).
5. `ws4_bisim_eq` — bisim ⊆ diagonal, from terminality alone (mirrors `bisim_eq`).

**Layer C — Weak-pullback preservation (template: `PkRel_le_comp`; the load-bearing gate G2).**
6. `WQRel_le_comp` — the substantive direction. Middle-point selection now selects *and weights*: for each element of the composed witness, `Classical.choice` picks a middle point and `tensor_sSup` splits its weight `w = ⨆(wᵢⱼ)` across the two factor legs. **This is where `GoodQuantale.tensor_sSup` is consumed; it is the one genuinely new proof, not a template port.**
7. `WQRel_comp_le` — the free/merge direction (uses `bot_tensor` + `iSup_lt_of_isRegular` for the bound, as `PkRel_comp_le` uses `mul_lt_of_lt`).
8. `ws4_weak_pullback : WQPreservesWeakPullback Q κ` — assembles 6+7 (mirrors `ws2_weak_pullback`).
9. `ws4_bisim_behavioural` — behavioural equivalence = identity (mirrors `ws2_bisim_behavioural`, using `diagBisim`-analogue + `bisim_comp`-analogue built on 8).

**Layer D — Graded weak law (template: `alg`/`alg_pentagon`/`alg_join`; closes G6 via F5).**
10. `destEquivWQ` — Lambek iso as `Equiv` (mirrors `destEquiv`).
11. `wqAlg (hreg) (t) := (destEquivWQ).symm (wqJoin hreg (WQMap str t))` — graded composition (mirrors `alg`).
12. `wqAlg_pentagon : str (wqAlg t) = wqJoin hreg (WQMap str t)` — from `apply_symm_apply` (mirrors `alg_pentagon`).
13. `wqAlg_unit`, `wqAlg_join`, `wqReflects_part`, `wqOmega_fix` — the weak-law coherence (mirror the WS3 quartet; associativity of `⊗`-scaled `Q`-sup replaces union associativity, needs `tensor_sSup` + `CommMonoid` assoc).
14. `wqAlg_nontrivial` — incomparable witnesses (mirror `alg_nontrivial`).

**Layer E — Reduction + assembly (the conservativity check, closes G7 for the pair).**
15. `boolGood : GoodQuantale (ULift Bool)` — the anchor instance; `⊗ = ∧`, `sSup = ∃`, `⊤ = true`, `⊥ = false`. All four class axioms are finite Bool identities.
16. `wq_reduces_to_pk : ∀ t, wqAlg (Q := ULift Bool) hreg t = alg hreg (boolIso t)` — the graded law *is* WS3's `alg` at `Q = Bool`, via a functor iso `W_Bool ≅ P_κ`. **This is the theorem that makes F5 conservative and closes the criterion-(iv) hand-off honestly rather than by reinterpretation.**
17. `GradedWeakBialgebra` structure extending the WS3 shape with the graded fields + `noStrictLaw := ws3_no_distributive_law`-analogue.
18. `ws4_graded_bialgebra (Q) [GoodQuantale Q] (hreg) : Nonempty (GradedWeakBialgebra Q hreg)` — the deliverable.
19. `ws4_class_nonempty` — a *non-degenerate* instance (a `Q` with ≥3 elements, e.g. the Gödel three-chain `{⊥ < m < ⊤}` with `⊗ = ∧`), so grading is provably not two-valued.

## 5. Hypothesis accounting

- `hreg : κ.IsRegular` — **genuinely load-bearing** in `wqJoin` (Layer D) and `WQRel_comp_le` (Layer C step 7), for exactly WS3's reason: `< κ`-indexed `Q`-sup of `< κ` supports stays `< κ` only by regularity. Not needed for existence (Layer A), matching WS1.
- `hinf = hreg.aleph0_le` — singletons/pairs.
- No new cardinal hypothesis beyond WS3.
- **No custom axioms.** Everything rests on Mathlib's `propext`/`Classical.choice`/`Quot.sound`. `Classical.choice` enters exactly at the middle-point selection in step 6, as in `PkRel_le_comp`. `#print axioms ws4_graded_bialgebra` and `#print axioms ws4_weak_pullback` to confirm.

## 6. Success condition

Steps 1–19 `sorry`-free and axiom-free; `ws4_weak_pullback` and `ws4_bisim_behavioural` proved for the whole `GoodQuantale` class; `wq_reduces_to_pk` proved (conservativity); `ws4_class_nonempty` exhibits a ≥3-element `Q`. On success, WS4 ratifies the shared `(F, κ)` for its enriched functor *and* the quantale `Q`, discharges the WS3-pinned weak-law-persistence duty, and criterion (iv) moves from Partial toward closure (final closure still pending the *canonicity* question, which WS4 scopes but does not claim to settle — see §7).

## 7. What would count as this obligation failing

- **Non-existence.** `qpfWQ` cannot be formed (the `Q`-labeled enumeration escapes `κ.ord.toType`) → no terminal coalgebra. *Decidably not the case for `GoodQuantale`, since support is `< κ` and the label is a total function on it.*
- **Collapse (grading).** The only `Q` satisfying `GoodQuantale` are `{⊥,⊤}` → `ws4_class_nonempty` fails and grading is two-valued. Guarded against by step 19; if step 19 provably fails, **route to F6** (impossibility outcome).
- **Non-preservation (the real risk, G2).** `WQRel_le_comp` (step 6) is false — a `Q`-weighted cospan whose Barr lift is not preserved even under `tensor_sSup`. This would mean bisim ≠ behavioural for `W_Q`, breaking criterion (ii) for the enriched carrier. If it fails despite the class axioms, the class definition is under-constrained and must be tightened (or the obligation is genuinely impossible → F6). **This is the single step to attack first**, because it is the only one not a template port and the only one that can invalidate the selection.
- **Non-persistence / non-conservativity.** `wqAlg_join` (step 13) or `wq_reduces_to_pk` (step 16) fails — the graded weak law is incoherent, or disagrees with WS3 at `Q = Bool`. Either leaves criterion (iv) permanently Partial and means the enrichment is not a conservative extension of WS3.
- **Canonicity (out of scope, flagged).** Even on full success, WS4 does **not** prove the graded weak law is the *unique*/canonical one — only that a well-behaved one persists. That residual stays open and is *not* to be reported as criterion-(iv) closure; it remains the WS3-originated canonicity question, now inherited at the `(Q, κ)` level.

**First action for the build phase:** attempt step 6 (`WQRel_le_comp`) in isolation against the `GoodQuantale` axioms. It is the decision point — if it goes through, the rest is template-portable from WS1/WS2/WS3; if it resists, tighten `GoodQuantale` or pivot to F6.
