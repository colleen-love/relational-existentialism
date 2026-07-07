# WS4 Design v2: Graded Parthood over a Good Quantale

*Revision addressing four defects found in v1: (P1) `one_eq_top` collapses the class to frames; (P2) the `wqJoin` sup ranges over a too-large index set, breaking the `< κ` bound; (P3) step 6 (`WQRel_le_comp`) needs a residuation/divisibility axiom beyond the four; (P4) the QPF shape-count depends on an unstated bound on `#Q`.*

---

## 0. Selection statement (unchanged in intent, tightened in scope)

Build the `Q`-weighted `< κ`-supported observation functor `W_Q` for `Q` in a typeclass `GoodQuantale`; prove it is a QPF and hence has a terminal coalgebra via `Cofix`; prove weak-pullback preservation, bisim = identity, and behavioural equivalence = identity for it; then define the graded composition operator via the Lambek inverse and prove the graded weak distributive law persists and reduces to WS3's `alg` at `Q = Bool`. Exhibit a *genuinely quantitative* (non-idempotent) non-degenerate instance, not merely a non-two-valued frame.

The scope change from v1: the class is now split into a **base** class (`GoodQuantale`) carrying only what existence, functoriality, bisim and the bound need, and a **preservation** extension (`DivisibleQuantale`) carrying the residuation-surjectivity that step 6 actually consumes. The unit is no longer forced to `⊤`. The QPF construction now carries an explicit smallness hypothesis on `Q`.

---

## 1. Ambient theory and imports

Unchanged from v1 except as noted below.

- **Set theory:** ZFC. AFA modeled coalgebraically. No set-theoretic AFA axiom imported.
- **Functor `F`:** `W_Q κ X = { ρ : X → Q // supp(ρ) is < κ-sized }`, `supp(ρ) = {x | ρ x ≠ ⊥}`.
- **Monad `T`:** the `Q`-weighted composition monad on `W_Q`; unit = point mass at `1` (**not** `⊤` — see P1 fix); join = `Q`-sup of `⊗`-scaled fibres over the *support* (**not** all of `WQObj` — see P2 fix).
- **Distributive law:** weak only — the graded Egli–Milner law. Strict law inherited-impossible via `ws3_no_distributive_law` at `Q = Bool`. WS4 does not re-attempt a strict law.

Imported upstream theorems (`ws1.lean`, `ws2.lean`, `ws3.lean`): as in v1 — `qpfPk`, `PkRel_le_comp`/`PkRel_comp_le`, `ws2_bisim_behavioural`, `pkJoin`/`Cardinal.iSup_lt_of_isRegular`, `alg`/`alg_pentagon`/`alg_join`, `ws3_no_distributive_law`, `WeakBialgebra`. The reuse of these as templates is unchanged; the corrections below concern the *new* `Q`-layer, which is where all four defects lived.

---

## 2. The class hierarchy (P1 + P3 fix)

### 2.1 What went wrong in v1

v1 bundled four axioms into a single `GoodQuantale`, including `one_eq_top : (1 : Q) = ⊤`. That axiom forces the monoid unit to be the lattice top. Combined with the requirement that `wqPure` (point mass) be a genuine two-sided unit for `wqJoin`, it forces `⊤ * a = a` for all `a`, i.e. `⊤` is the `⊗`-unit. The only quantales where `⊤` is the unit are exactly those where `⊗ = ∧` (meet), i.e. **frames / Heyting-style idempotent quantales**. So v1's "good quantales" were secretly frames, and its three-element witness (`{⊥ < m < ⊤}`, `⊗ = ∧`) was non-two-valued but not *quantitative*: it satisfied `a * a = a`, so it carried no genuine degree composition. The Lawvere quantale `([0,∞], +, ≥)` — the canonical quantitative example, with `1 = 0 ≠ ⊤ = ∞` — was silently excluded.

Additionally, v1 listed both `tensor_sSup` and `sSup_tensor`; under the `CommMonoid` base these are interderivable, so one is redundant. v1's "exactly four and nothing else" minimality claim was therefore false.

### 2.2 The corrected base class

```lean
class GoodQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  -- ⊗ distributes over arbitrary joins (the quantale law). Under CommMonoid this
  -- single axiom yields the other side; we do NOT also assume sSup_tensor.
  tensor_sSup : ∀ (a : Q) (s : Set Q), a * sSup s = ⨆ b ∈ s, a * b
  -- ⊥ is a two-sided ⊗-annihilator. Left form suffices under CommMonoid; we state
  -- it once and derive the right form. This is what keeps supp(a * b) ⊆ supp a ∩ supp b.
  bot_tensor  : ∀ a : Q, (⊥ : Q) * a = ⊥
```

**Removed:** `one_eq_top` (the P1 defect) and the redundant `sSup_tensor`.

**Consequences that must now be re-derived rather than assumed:**
- `1` need not be `⊤`. `wqPure x` assigns `1` (not `⊤`) at `x` and `⊥` elsewhere. `1` is the `⊗`-unit by `CommMonoid`, so `wqPure` is a genuine unit for `wqJoin` *without* the frame collapse.
- `tensor_sSup` at `s = ∅` gives `a * ⊥ = a * sSup ∅ = ⨆_{b ∈ ∅} … = ⊥`, so `bot_tensor`'s right form and `a * ⊥ = ⊥` both follow; `bot_tensor` as a field is then only needed for the *left* annihilation used before commutativity is in scope. (Kept as a field to avoid an ordering dependency in the support lemmas; noted as derivable.)
- Monotonicity of `⊗` in each argument follows from `tensor_sSup` (`a * b ≤ a * (b ⊔ c) = (a*b) ⊔ (a*c)`).

### 2.3 The preservation extension (P3 fix)

Step 6 (`WQRel_le_comp`, weak-pullback preservation) does **not** merely need `⊗` to distribute over joins. The middle-point construction must *reconstruct* a target weight `w` exactly from the two factor legs: given leg-weight `a` and target `w`, it needs `b` with `a * b = w` (not merely `a * b ≤ w`). The residual `a → w := sSup {b | a * b ≤ w}` always satisfies `a * (a → w) ≤ w`; equality is a *separate* property (call it "surjectivity of `a * (-)` onto its down-set", i.e. divisibility). It holds in frames and in the Lawvere quantale but fails in general quantales.

```lean
class DivisibleQuantale (Q : Type u) extends GoodQuantale Q where
  -- For a ≠ ⊥ and w ≤ a * ⊤, the residual is a genuine section:
  -- a * (residual a w) = w whenever w is ⊗-reachable from a.
  -- Equivalently: a ≤ b in the ⊗-divisibility preorder ⟺ ∃ c, b = a * c on the
  -- relevant sublattice. This is exactly what step 6's weight-splitting consumes.
  tensor_section : ∀ (a w : Q), w ≤ a * ⊤ → a * (sSup {b | a * b ≤ w}) = w
```

Weak-pullback preservation (Layer C, steps 6–9) is proved **for `DivisibleQuantale`**, not for the bare `GoodQuantale`. Existence, functoriality, Lambek, and the bound (Layers A–B and the `wqJoin` well-definedness) need only `GoodQuantale`. This split is the honest statement of what each gate consumes; v1's G2 rating of "plausible by construction" from the four base axioms was optimistic, because `tensor_section` is genuinely additional and genuinely can fail.

**Both anchor instances satisfy the extension:**
- `ULift Bool` (frame): `tensor_section` is a finite Bool identity.
- Lawvere `([0,∞], +, ≥^op)`: residual is truncated subtraction; `a + (w - a) = w` whenever `w ≥ a`, i.e. `w ≤ a * ⊤` in the order-dual, so `tensor_section` holds. This is the instance that makes the enrichment quantitative.

---

## 3. Definitions (P2 + P4 fix)

```lean
-- P4 fix: the functor is defined only when Q is < κ-small in the shape sense.
-- The QPF shape type carries a Q-label per position, so #shapes depends on #Q.
-- We record the smallness hypothesis explicitly rather than hiding it in "carry the label".
variable {Q : Type u} [GoodQuantale Q] {κ : Cardinal.{u}}

structure WQObj (Q) [GoodQuantale Q] (κ : Cardinal.{u}) (X : Type u) where
  wt  : X → Q
  bdd : Cardinal.mk ↥{x | wt x ≠ ⊥} < κ

-- Functorial action: pushforward with Q-sup over fibres.
-- NOTE (v1 correction): this uses ONLY complete-lattice joins, NOT tensor_sSup.
-- ⊗ enters at wqJoin, never in the functor action. (v1 §4 step 1 misattributed this.)
noncomputable def WQMap {X Y : Type u}
    (f : X → Y) (ρ : WQObj Q κ X) : WQObj Q κ Y :=
  ⟨fun y => ⨆ x ∈ f ⁻¹' {y}, ρ.wt x, by
    -- supp(pushforward) ⊆ f '' supp(ρ); #(f '' supp ρ) ≤ #supp ρ < κ by mk_image_le
    ...⟩

structure WQCoalg (Q) [GoodQuantale Q] (κ) where
  X : Type u
  str : X → WQObj Q κ X

def IsTerminalWQCoalg (Q) [GoodQuantale Q] (U : WQCoalg Q κ) : Prop := ...

-- P2 FIX: the T-monad multiplication. The outer join ranges over supp(tt.wt),
-- a < κ-sized set, NOT over all of WQObj Q κ (WQObj Q κ X). Regularity only
-- controls a < κ-indexed sup; ranging over the whole functor object would index
-- by a ≥ κ (or proper-class) set and iSup_lt_of_isRegular would not apply.
noncomputable def wqJoin (hreg : κ.IsRegular)
    (tt : WQObj Q κ (WQObj Q κ X)) : WQObj Q κ X :=
  ⟨fun x => ⨆ ρ ∈ {ρ | tt.wt ρ ≠ ⊥}, tt.wt ρ * ρ.wt x, by
    -- supp ⊆ ⋃_{ρ ∈ supp tt} supp(ρ.wt):
    --   tt.wt ρ * ρ.wt x ≠ ⊥ ⟹ tt.wt ρ ≠ ⊥ (ρ ∈ index set) AND ρ.wt x ≠ ⊥ (by bot_tensor + comm)
    -- #supp tt < κ, each #supp ρ < κ, κ regular ⟹ union < κ via iSup_lt_of_isRegular
    ...⟩

-- Point mass (T-unit): assigns 1, NOT ⊤ (P1 fix). 1 is the ⊗-unit by CommMonoid.
noncomputable def wqPure (x : X) : WQObj Q κ X :=
  ⟨fun y => if y = x then (1 : Q) else ⊥, by
    -- support ⊆ {x}, size ≤ 1 < κ since κ ≥ ℵ₀
    ...⟩

def WQRel {X Y} (R : X → Y → Prop) : WQObj Q κ X → WQObj Q κ Y → Prop := ...
```

**The three concrete corrections in this section:**
1. `wqPure` assigns `1`, restoring the unit law without frame collapse (P1).
2. `wqJoin`'s outer `⨆` is explicitly bounded to `ρ ∈ supp(tt.wt)`, a `< κ` set, so `iSup_lt_of_isRegular` applies as in WS3's `pkJoin` (P2). The support-containment lemma uses `bot_tensor` + commutativity to get `a * b ≠ ⊥ ⟹ b ≠ ⊥`.
3. `WQMap` is annotated to use only lattice joins; `tensor_sSup` is not invoked here.

---

## 4. Proof architecture (dependency-ordered, with corrected gate attributions)

**Layer A — Functor + QPF (base class + P4 smallness).**
1. `WQMap_id`, `WQMap_comp` — functoriality. **Uses only `CompleteLattice` join commutation, not `tensor_sSup`** (v1 misattribution corrected).
2. `qpfWQ : QPF (WQObj Q κ)` — shapes `Σ (a : κ.ord.toType), (positions a → Q)`; positions `{b // b < a}`; `abs` the `Q`-labeled range; `repr` enumerates support by `(#supp).ord` and records the label. **P4: this is well-formed as a QPF only under `hQsmall : #Q ≤ κ` (or `#Q < κ`), because the shape type has cardinality `≥ #Q` per position.** If `#Q ≥ κ` the shape count can escape `κ.ord.toType` and `Cofix` machinery does not port. Record `hQsmall` as a standing hypothesis of the functor.
3. `exists_terminal_wq` — via `Cofix (WQObj Q κ)`. Structurally identical to `exists_terminal_coalg` once step 2 is well-formed.

**Layer B — Lambek + bisim (base class).**
4. `wqLambek : Function.Bijective U.str` — verbatim generalization of `lambek`.
5. `ws4_bisim_eq` — bisim ⊆ diagonal, from terminality alone.

**Layer C — Weak-pullback preservation (`DivisibleQuantale`; the load-bearing gate G2).**
6. `WQRel_le_comp` — the substantive direction. Middle-point selection selects and weights; the weight-split `a * b = w` is discharged by **`DivisibleQuantale.tensor_section`**, not by `tensor_sSup` alone (P3 fix). **This is the one genuinely new proof and the one requiring the extension axiom. Attack first.**
7. `WQRel_comp_le` — merge direction (uses `bot_tensor` + `iSup_lt_of_isRegular` for the bound).
8. `ws4_weak_pullback : WQPreservesWeakPullback Q κ` — assembles 6+7. **Stated for `[DivisibleQuantale Q]`.**
9. `ws4_bisim_behavioural` — behavioural equivalence = identity, built on 8.

**Layer D — Graded weak law (`DivisibleQuantale`; closes G6 via F5).**
10. `destEquivWQ` — Lambek iso as `Equiv`.
11. `wqAlg (hreg) (t) := (destEquivWQ).symm (wqJoin hreg (WQMap str t))`.
12. `wqAlg_pentagon : str (wqAlg t) = wqJoin hreg (WQMap str t)` — from `apply_symm_apply`.
13. `wqAlg_unit`, `wqAlg_join`, `wqReflects_part`, `wqOmega_fix` — weak-law coherence. `wqAlg_unit` now needs `1 * a = a` (holds by `CommMonoid`, was masked by `one_eq_top` in v1). Associativity uses `tensor_sSup` + `CommMonoid` assoc; the join reassociation ranges over the `< κ` support sets from the P2 fix.
14. `wqAlg_nontrivial` — incomparable witnesses.

**Layer E — Reduction + assembly (conservativity; closes G7 for the pair).**
15. `boolGood : DivisibleQuantale (ULift Bool)` — `⊗ = ∧`, `sSup = ∃`, `1 = ⊤ = true`, `⊥ = false`. Here `1 = ⊤` holds *as a theorem about Bool*, not as a class axiom — the frame case is recovered as a special instance rather than being the definition.
16. `wq_reduces_to_pk : ∀ t, wqAlg (Q := ULift Bool) hreg t = alg hreg (boolIso t)` — graded law is WS3's `alg` at `Q = Bool` via `W_Bool ≅ P_κ`. The iso intertwines `sSup`-of-`∧` with `⋃`; on Bool `1 = ⊤` so `wqPure` matches `pkPure`. Conservativity survives the P1 fix precisely because Bool is one of the frames where `1 = ⊤`.
17. `GradedWeakBialgebra` extends the WS3 shape with graded fields + `noStrictLaw`.
18. `ws4_graded_bialgebra (Q) [DivisibleQuantale Q] (hQsmall) (hreg) : Nonempty (GradedWeakBialgebra Q hreg)` — the deliverable.
19. **`ws4_quantitative_witness`** — a *non-idempotent* `DivisibleQuantale` instance, i.e. one with `a * a ≠ a` for some `a`. **P1 fix makes this the real non-degeneracy obligation:** the v1 three-chain frame `{⊥<m<⊤}` with `⊗=∧` is idempotent and no longer counts as demonstrating quantitative grading. Use a finite Łukasiewicz/MV chain, or a `< κ`-truncated Lawvere quantale (e.g. `{0,1,…,n}` under truncated addition `a ⊕ b = min(a+b, n)`, order-dual join), where `1 ⊕ 1 = 2 ≠ 1`. Exhibiting this discharges "grading is genuinely quantitative, not merely multivalued."

---

## 5. Hypothesis accounting (updated)

- `hreg : κ.IsRegular` — load-bearing in `wqJoin` (Layer D) and `WQRel_comp_le` (Layer C step 7), for WS3's reason. Now *correctly* load-bearing because the join index set is `< κ` (P2 fix); in v1 as literally written the sup was over a `≥ κ` set and regularity was insufficient.
- **`hQsmall : #Q ≤ κ`** — NEW, and genuinely required for `qpfWQ` (Layer A step 2, P4 fix). Absent in v1. Both anchor instances satisfy it: `#Bool = 2 < κ`; the truncated `{0,…,n}` chain has `#Q = n+1 < κ` for `κ ≥ ℵ₀`. The unbounded Lawvere quantale `[0,∞]` has `#Q = 𝔠`, so it needs `κ > 𝔠` or a `< κ`-truncation — a real constraint the design must state, not assume away.
- `hinf = hreg.aleph0_le` — singletons/pairs.
- **Class split:** existence/functoriality/bisim/bound need `GoodQuantale` (2 axioms); weak-pullback + graded law need `DivisibleQuantale` (+1 axiom). No single "four-axiom" class; v1's minimality claim is replaced by an honest two-tier statement.
- **No custom global axioms.** Rests on `propext`/`Classical.choice`/`Quot.sound`. `Classical.choice` enters at middle-point selection (step 6) and inside `sSup`. `#print axioms ws4_graded_bialgebra`, `#print axioms ws4_weak_pullback` to confirm.

---

## 6. Success condition (updated)

Steps 1–19 `sorry`-free and axiom-free; `ws4_weak_pullback` and `ws4_bisim_behavioural` proved for the whole **`DivisibleQuantale`** class (not bare `GoodQuantale`); `wq_reduces_to_pk` proved (conservativity); **`ws4_quantitative_witness` exhibits a non-idempotent `Q`** (strictly stronger than v1's non-two-valued requirement). On success, WS4 ratifies the shared `(F, κ)` for the enriched functor *and* a genuinely quantitative `Q`, discharges the WS3-pinned weak-law-persistence duty, and criterion (iv) moves toward closure (canonicity still out of scope, §7).

---

## 7. What would count as this obligation failing (updated)

- **Non-existence (now includes P4).** `qpfWQ` cannot be formed *either* because the `Q`-labeled enumeration escapes `κ.ord.toType` (support-count, as v1) *or because `#Q ≥ κ`* so the shape type is too large (new). Guarded by `hQsmall`; a `Q` of interest with `#Q ≥ κ` forces raising `κ` or truncating `Q`.
- **Collapse (now sharper).** If the only `DivisibleQuantale` instances are idempotent (frames), then grading is qualitatively multivalued but never quantitative, and `ws4_quantitative_witness` fails. This is a *stronger* collapse test than v1's two-valued test and is the honest bar. If step 19 provably fails, route to F6.
- **Non-preservation (the real risk, G2, now correctly located).** `WQRel_le_comp` (step 6) is false even with `tensor_section`. Then `DivisibleQuantale` is still under-constrained (or the obligation is impossible → F6). Attack step 6 first. Note the risk moved: v1 hoped the four base axioms sufficed; v2 isolates `tensor_section` as the exact load and tests *it*.
- **Non-persistence / non-conservativity.** `wqAlg_join` (step 13) or `wq_reduces_to_pk` (step 16) fails. With the P1 fix, watch step 13's `wqAlg_unit` specifically: it now relies on `1 * a = a` rather than the old `⊤`-unit; if some intended instance lacks a genuine `⊗`-unit distinct from `⊤`, unit coherence breaks there.
- **Canonicity (out of scope, flagged).** Unchanged: WS4 proves a well-behaved graded weak law persists, not that it is unique.

**First action for the build phase:** attempt step 6 (`WQRel_le_comp`) against the `DivisibleQuantale` axioms — specifically test whether `tensor_section` is sufficient, or whether an even stronger divisibility law (e.g. full GBL-algebra structure) is needed. This is the decision point. If it goes through, the rest is template-portable; if it resists, strengthen the extension or pivot to F6.

---

## Appendix: summary of changes from v1

| # | v1 defect | v2 fix | Location |
|---|-----------|--------|----------|
| P1 | `one_eq_top` silently collapses "good quantale" to frame; kills quantitative grading | Removed the axiom; `wqPure` uses `1` not `⊤`; unit laws from `CommMonoid`; frames recovered only as instances (`boolGood`) | §2.2, §3, step 15, step 19 |
| P2 | `wqJoin` outer `⨆` ranges over all of `WQObj`, a `≥ κ` index; regularity insufficient | Bounded the sup to `ρ ∈ supp(tt.wt)`, a `< κ` set; matches WS3 `pkJoin` | §3 `wqJoin`, §5 |
| P3 | Step 6 needs weight-reconstruction `a*b = w`, not just `tensor_sSup`; four axioms don't discharge G2 | Added `DivisibleQuantale.tensor_section`; weak-pullback + graded law require the extension | §2.3, Layer C, §5, §7 |
| P4 | QPF shape-count depends on `#Q`; "carry the label" understates it | Added `hQsmall : #Q ≤ κ` as a standing hypothesis; unbounded Lawvere quantale needs `κ > 𝔠` or truncation | §3, step 2, §5, §7 |
| — | `sSup_tensor` redundant under `CommMonoid`; "exactly four" minimality false | Dropped; two-tier class with honest per-gate attribution | §2.1, §2.2 |
| — | v1 step 1 claimed functoriality uses `tensor_sSup` | Corrected: functor action uses only lattice joins; `⊗` enters at `wqJoin` | §3, Layer A step 1 |
