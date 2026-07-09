# WS14 — Phase 2: Design

## Triage (decidable on paper, per candidate)

| # | Candidate | Paper-decidable? | New math? | Risk | Lean cost | Consumers | Verdict |
|---|---|---|---|---|---|---|---|
| G1 | `loopState q` (one-point corecursion) | yes (unique map from the one-point `Q`-coalgebra; `pushQ` computes on a singleton) | no | low | S | G2, G3, G4, G5⁻, G8 | **select, wave 1** |
| G2 | `ws14_loop_ne` (`q₁ ≠ q₂ → loop q₁ ≠ loop q₂`) | yes (`congrArg str` + evaluate at the loop point) | no | none | XS | G4 | **select, wave 1** |
| G3 | hereditary support of loops (`WReaches`, `HereditarilySupported`) | yes (loop reaches only itself) | no | low | S | G4, G5 | **select, wave 1** |
| G4 | headline: atomless ∧ plural satisfiable on the weighted carrier | yes (= G1+G2+G3 assembled; opposite-verdict branch also assemble-only) | no | low | XS | ledger, external | **select, wave 1** |
| G7 | `ws14_wq_card_ge` (Lambek–Cantor transfer) | yes (verbatim shape of the plain-carrier bound) | no | low | S | G8 | **select, wave 1** |
| G9 | `ℕ∞ᵒᵈ` Lawvere quantale instance package | yes except one convention check (distributivity field orientation at `∅` — checkable in one minute against `GoodQuantale`'s field, deferred to first execute step) | no | medium (instance plumbing) | M | G4-at-∞ witness, G5⁺ | **select, wave 1** |
| G5 | core closure under `wqAlg` — two-sided fork | **partially** — negative half (Łₙ nilpotent) fully paper-decidable; positive half (BotFree ⇒ closure) decidable modulo one lemma (weighted reach through a join decomposes) whose statement is fixed here and whose proof is routine sup-algebra | borderline (the fork itself is the finding) | medium | M | ledger | **select, wave 2** |
| G8 | weighted standpoints (distinct / non-global / proper) | yes (transport of the plain-carrier proofs along G7) | no | low | S | prose only | **select, wave 2** |
| G6 | `WeakDistLaw` class: inhabitation + uniqueness | **gated** — the cardinality pre-check is itself paper-decidable and is run *in this design* (below): passes at `κ₀ = ℵ₀`, fails for general regular κ, passes again at strong-limit κ. Inhabitation then decidable on paper at `ℵ₀`; **uniqueness is not** fully paper-decidable (the naturality-pinning argument has one step — transversal-set reconstruction — that may need an extra axiom on the law) | yes (uniqueness half) | **high** | L | ledger (O3) | **select, wave 3, with pre-registered Partial** |

Decision: waves **1 = {G1, G2, G3, G4, G7, G9}**, **2 = {G5, G8}**, **3 = {G6}**. Bundle name: `ws14_graded_core` (per naming discipline: no `_resolved`, no verdict in the name — the bundle records *which* verdict was proved).

**The G6 gate, run now (paper computation).** The Egli–Milner transversal transformation is `θ S := {T | T ⊆ ⋃₀ S ∧ ∀ A ∈ S, (A ∩ T).Nonempty}`. For `S` with `#S < κ` and each `#A < κ`: `#⋃₀S < κ` (regularity), but `#θ(S) ≤ 2^{#⋃₀S}`, i.e. up to `2^{<κ}`. For the law to be typed `PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)` the outer set must stay `< κ`:

- at `κ = ℵ₀`: `⋃₀S` finite, `2^{finite}` finite `< ℵ₀` — **gate passes**;
- at general regular κ (e.g. `ℵ₁`): `2^{ℵ₀} ≥ ℵ₁` — **gate fails**; the transversal law is not even well-typed;
- at strong-limit regular κ (inaccessible): `2^{λ} < κ` for `λ < κ` — gate passes, but no such κ is exhibited in the development.

**Design consequence:** G6 is typed at `κ₀ = ℵ₀` only, with the type-failure at general κ *stated as a lemma-shaped remark* (the transversal set of a countably infinite family can have cardinality `2^{ℵ₀}`), so the restriction is a recorded fact rather than a silent choice. This mirrors the precedent of the dynamics bridge, which also ratifies `ℵ₀` specifically.

---

## Proof architecture

**File:** `series-3/formal/ws14.lean`, namespace `Series3.WS14`, `import ws4, ws10` (ws4 for the entire weighted stack — `GoodQuantale`, `DivisibleQuantale`, `Luk`, `WQObj`, `pushQ`, `Qsupp`, `νWQ`, `wqLambek`, `wq_bisim_eq`, `destEquivWQ`, `wqAlg`, `wqAlg_pentagon`, `wqJoinFun`, `wqJoin_supp_subset` — ws10 for the unweighted collapse theorem to be contrasted and for the `Reaches` idiom). G6 additionally `import ws3` for the square shapes.

Throughout, `Q` carries `[GoodQuantale Q]`; theorems state their quantale hypotheses (`∃ q ≠ ⊥`, `BotFree`, …) explicitly rather than via a bespoke class, so each result advertises exactly what it consumes.

### Block 0 — the weighted state-former and evaluation lemmas

`destEquivWQ` already exists (ws4:556); re-export the two directions with the naming that parallels the plain carrier's interface:

```lean
noncomputable def mkStateW (s : WQObj Q κ (νWQ Q κ).X) : (νWQ Q κ).X :=
  (destEquivWQ Q κ).symm s
@[simp] theorem str_mkStateW (s) : (νWQ Q κ).str (mkStateW s) = s
@[simp] theorem mkStateW_str (u) : mkStateW ((νWQ Q κ).str u) = u
theorem mkStateW_inj : Function.Injective (mkStateW (Q := Q) (κ := κ))
```

Gap note 1: check at execute whether ws4's canonicity section already exports these under another name; reuse, do not duplicate.

### Block 1 — loops (G1, G2)

The self-loop cannot come from `mkStateW` (self-reference); it comes from terminality applied to the one-point weighted coalgebra:

```lean
def loopCoalg (q : Q) (hq : ℵ₀ ≤ κ) : WQCoalg Q κ :=
  { X := PUnit, str := fun _ => ⟨fun _ => q, small_of_singleton …⟩ }
noncomputable def loopState (q : Q) (hq : ℵ₀ ≤ κ) : (νWQ Q κ).X :=
  ((νWQ_terminal Q κ).hom (loopCoalg q hq)).f PUnit.unit
```

Lemma ladder:

```lean
lemma str_loopState (q hq) :
    ((νWQ Q κ).str (loopState q hq)).1 =
      fun y => if y = loopState q hq then q else ⊥
-- from the homomorphism square: str (h pt) = pushQ (str_loopCoalg pt) h;
-- pushQ on the one-point domain: sup over {x | h x = y} of the constant q
-- = q at y = h pt (nonempty index), ⊥ at y ≠ h pt (empty sup).
theorem ws14_loop_ne {q₁ q₂ : Q} (hq : ℵ₀ ≤ κ) (hne : q₁ ≠ q₂) :
    loopState q₁ hq ≠ loopState q₂ hq
-- suppose equal; congrArg str; evaluate both weight functions at the common
-- loop point: the if-branches fire on both sides, giving q₁ = q₂.
```

Gap note 2: the `pushQ` empty-sup step needs `⨆ x, ⨆ (_ : False), ρ x = ⊥` — `iSup_eq_bot` / `iSup_false` at the pin; the nonempty branch needs `iSup` over a subsingleton — `iSup_iSup_eq_left` shape. Both are one-liners but the exact Mathlib names are execute-time lookups.

### Block 2 — weighted reachability and hereditary support (G3)

```lean
def WReaches (x y : (νWQ Q κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => ((νWQ Q κ).str a).1 b ≠ ⊥) x y
def HereditarilySupported (x : (νWQ Q κ).X) : Prop :=
  ∀ y, WReaches x y → (Qsupp ((νWQ Q κ).str y).1).Nonempty

lemma wreaches_loop (q hq) : ∀ y, WReaches (loopState q hq) y → y = loopState q hq
-- ReflTransGen.head_induction_on: each step out of the loop has nonzero weight
-- only at the loop itself (str_loopState if-form).
theorem loop_hereditarily_supported (q : Q) (hq) (hq⊥ : q ≠ ⊥) :
    HereditarilySupported (loopState q hq)
-- every reachable y is the loop; its support contains the loop point since q ≠ ⊥.
```

### Block 3 — the headline (G4)

```lean
theorem ws14_graded_core_plural (hq : ℵ₀ ≤ κ)
    {q₁ q₂ : Q} (h₁ : q₁ ≠ ⊥) (h₂ : q₂ ≠ ⊥) (hne : q₁ ≠ q₂) :
    ∃ x y : (νWQ Q κ).X, x ≠ y ∧
      HereditarilySupported x ∧ HereditarilySupported y

structure WS14GradedCore (Q κ) where   -- the bundle, all fields proofs
  hq      : ℵ₀ ≤ κ
  x y     : (νWQ Q κ).X
  ne      : x ≠ y
  hx      : HereditarilySupported x
  hy      : HereditarilySupported y
```

Instantiated at `Luk 2` (weights `1/2, 1`, both `≠ 0`) and — after G9 — at `ℕ∞ᵒᵈ` (weights `1, 2`). The contrast is then stated *as a pair of citations, not a new proof*: on the unweighted carrier the corresponding statement is refuted (the ws10 collapse theorem: any two hereditarily nonempty states are equal), on the weighted carrier it is realized, and the mechanism is visible in the proof term — the collapse argument's projection step (`fst '' (A × B) = A`) has no weighted analogue because an Aczel–Mendler `WQBisim` must *preserve weights*, and the two loops carry different ones. A short remark lemma makes the mechanism a checkable fact rather than prose:

```lean
theorem ws14_loops_not_bisim … : ¬ WQBisimRel (loopState q₁ hq) (loopState q₂ hq)
-- immediate from ws14_loop_ne + wq_bisim_eq (equality *is* bisimilarity on the
-- terminal carrier), stated so the blocked-collapse diagnosis is machine-checked.
```

**Pre-registered alternative outcome (from the BR):** if, contrary to the paper argument, some collapse *does* go through on the weighted carrier (i.e. `ws14_loop_ne` fails because the two loops are identified), the reportable result inverts: weighting does not defeat the collapse, and the bundle records the impossibility instead. The paper argument (weight preservation blocks the projection step) makes this branch very unlikely; it is registered so the outcome cannot be reframed.

### Block 4 — the weighted cardinality bound (G7)

```lean
theorem ws14_wq_card_ge (hq2 : ∃ q : Q, q ≠ (⊥ : Q)) (κ) (hinf : ℵ₀ ≤ κ) :
    κ ≤ Cardinal.mk (νWQ Q κ).X
```

Lemma ladder: (i) `small_supp_of_small : mk X < κ → ∀ ρ : X → Q, mk (Qsupp ρ) < κ` (subset bound); (ii) hence `WQObj Q κ X ≃ (X → Q)` when `mk X < κ` (the subtype is full); (iii) `wqLambek` gives `X ≃ WQObj Q κ X`; compose to `X ≃ (X → Q)`; (iv) `2 ≤ mk Q` from `⊥` and the witness; Cantor: `2 ^ mk X ≤ mk Q ^ mk X = mk X`, contradicting `Cardinal.cantor`. This is the plain-carrier proof with `Set X` replaced by `X → Q`; no new idea, and its consumers (G8) are stated at the same hypotheses.

### Block 5 — the Lawvere witness (G9)

Instance package on `ℕ∞ᵒᵈ := (WithTop ℕ)ᵒᵈ` exactly as in the BR (`⊗ = +`, unit `0 = ⊤ᵒᵈ`, `⊥ᵒᵈ = ∞`):

```lean
instance : GoodQuantale ℕ∞ᵒᵈ
instance : DivisibleQuantale ℕ∞ᵒᵈ          -- weight_split via b := w ∸ a
theorem ws14_lawvere_quantitative : IsQuantitative ℕ∞ᵒᵈ    -- 1 + 1 ≠ 1
theorem ws14_lawvere_botfree : ∀ a b : ℕ∞ᵒᵈ, a * b = ⊥ → a = ⊥ ∨ b = ⊥
theorem ws14_lawvere_card : Cardinal.mk ℕ∞ᵒᵈ = Cardinal.aleph0
```

The single design-review checkpoint (from triage): `GoodQuantale`'s distributivity field is `a * sSup S = ⨆ b ∈ S, a * b` in the *dualized* order; on `ℕ∞` this is `a + ⨅ S = ⨅ (a + ·) '' S`, which holds **including** `S = ∅` (`⨅ ∅ = ∞`, `a + ∞ = ∞`) — verify the field's `∅` convention on first execute contact; if the field is oriented the other way, the accommodation is mechanical (`sSup ∅ = ⊥ᵒᵈ = ∞`). Pre-registered fallback (from the BR): dyadic-supported complete sublattice of `[0,1]`; hard failure (no countable divisible witness under the class's exact axioms) is itself reportable.

### Block 6 — the closure fork (G5)

**Negative half (unconditional, Łₙ).** In `Luk 2` (`{0, 1/2, 1}`, `a ⊗ b = max 0 (a + b − 1)`): `1/2 ⊗ 1/2 = 0 = ⊥`. Build a two-level tower whose join annihilates:

```lean
-- outer: weight 1/2 on the state innerHalf; innerHalf: weight 1/2 on loopState 1
noncomputable def towerLuk : WQObj (Luk 2) κ (WQObj (Luk 2) κ (νWQ (Luk 2) κ).X)
theorem ws14_core_not_closed_luk (hreg : κ.IsRegular) :
    ∃ t : WQObj (Luk 2) κ (νWQ (Luk 2) κ).X,
      (∀ w ∈ Qsupp t.1, HereditarilySupported w) ∧
      ¬ HereditarilySupported (wqAlg hreg t)
```

Proof plan: `wqJoinFun` computes the composite weight as `⨆ w, t w * w x`; on the tower every composite passes through `1/2 * 1/2 = ⊥`, so the joined state's support at the relevant reachable point is empty — the exact `< κ` bookkeeping rides `wqJoin_supp_subset` (already in ws4). Gap note 3: the statement quantifies hereditary support of the *members*, so the witness members must be loops (Block 1) — arrange the tower so its support is `{loopState 1}`-rooted with the annihilating weights on the edges, and reach the dead point in two `WReaches` steps.

**Positive half (conditional on `BotFree`).** One decomposition lemma, then closure:

```lean
lemma wreach_wqAlg_decomp (hreg) (t) {y} (h : WReaches (wqAlg hreg t) y) :
    y = wqAlg hreg t ∨ ∃ w ∈ Qsupp t.1, WReaches w y
-- head-step analysis: str (wqAlg t) is the join (wqAlg_pentagon supplies the
-- computation square); a nonzero joined weight ⨆ w, t w * w x ≠ ⊥ yields some w
-- with t w * w x ≠ ⊥; under BotFree both factors ≠ ⊥, so the step enters w's
-- own reach set; ReflTransGen induction propagates.
theorem ws14_core_closed_of_botfree (hbf : BotFree Q) (hreg) (t)
    (ht : ∀ w ∈ Qsupp t.1, HereditarilySupported w)
    (hne : (Qsupp t.1).Nonempty) :
    HereditarilySupported (wqAlg hreg t)
```

Gap note 4: the root case (`y = wqAlg t` itself) needs the join's own support nonempty — from `hne` plus one member's nonempty support and `BotFree` again (a nonzero `t w * w x`). The fork verdict as shipped: **closure holds exactly when the quantale is `⊥`-divisor-free among the exhibited instances** — positive at `ℕ∞ᵒᵈ` (Block 5), refuted at `Luk 2` — with full generality of the "exactly" (converse for arbitrary `Q` with `⊥`-divisors) *not* claimed: the converse needs the annihilating pair to be realizable at reachable weights, which the design asserts only per-instance. This scope line is pre-registered so the summary cannot say "iff."

### Block 7 — weighted standpoints (G8)

Transport of the plain-carrier trio along G7, with the weighted `view` = support membership of the base's unfolding. Three short theorems (`distinct`, `not_global`, `proper`), each ≤ 15 lines given Block 4; consumed by prose only, so scheduled last in wave 2.

### Block 8 — the weak-law class (G6, gated as above, at `κ₀ = ℵ₀`)

```lean
structure WeakDistLaw where
  law     : ∀ X : Type, PkObj ℵ₀ (PkObj ℵ₀ X) → PkObj ℵ₀ (PkObj ℵ₀ X)
  natural : …    -- square against PkMap (PkMap f), bound verbatim to ws3's shapes
  unit_l  : …    -- the unit laws in the *weak* orientation (lax unit)
  weak_mult : …  -- the corrected multiplication square (the one ws3's no-go
                 -- shows cannot be strict) — copy the exact strict square from
                 -- ws3 and weaken precisely the edge the no-go breaks
noncomputable def emLaw : WeakDistLaw   -- transversal transformation; typing uses
                                        -- the ℵ₀ gate computation (finite ⋃₀S)
theorem ws14_weak_law_unique : ∀ L L' : WeakDistLaw, L = L'   -- or the counterexample
```

Sub-plan: (a) definitions + `emLaw` inhabitation (paper-decidable at `ℵ₀`; the finiteness plumbing is `Set.Finite.powerset`-shaped); (b) uniqueness by naturality-pinning: evaluate an arbitrary `L` at the test families that drive the ws3 no-go (singletons, doubletons, and the two-level mixing family), and show naturality + units force the transversal values pointwise. **Pre-registered Partial (from triage):** the pinning argument's last step — reconstructing `L` on an arbitrary finite family from its test values — may require a monotonicity or union-preservation axiom not derivable from naturality alone. If so, ship `ws14_weak_law_unique_of_monotone` with the extra field explicit, declare the unrestricted uniqueness **open**, and record the second-inhabitant question as the remaining O3 content. A second genuine inhabitant, if found instead, is the opposite reportable outcome (the weak law is a choice). Under no branch is the ws3 unique-*realization* theorem cited for canonicity.

## Dependencies and ordering

```
Block 0 ──► Block 1 (G1,G2) ──► Block 2 (G3) ──► Block 3 (G4 headline)
Block 4 (G7) independent after Block 0            Block 5 (G9) independent
wave 2: Block 6 (G5) needs Blocks 1–3 + ws4 join lemmas; Block 7 (G8) needs Block 4
wave 3: Block 8 (G6) independent of all weighted blocks (plain functor), ws3-bound
```

Upstream imports consumed: `destEquivWQ`, `wqLambek`, `wq_bisim_eq`, `pushQ`, `Qsupp`, `wqJoinFun`, `wqJoin_supp_subset`, `wqAlg`, `wqAlg_pentagon`, `Luk`, `DivisibleQuantale` (ws4); collapse theorem + `Reaches` idiom (ws10); square shapes (ws3, Block 8 only). Exports offered downstream: `loopState`, `WReaches`, `HereditarilySupported`, `WS14GradedCore`, `ws14_wq_card_ge` (consumed by any later weighted work), `ℕ∞ᵒᵈ` instances (general-purpose).

## Risk register

1. **G6 uniqueness** — the one item with genuinely open mathematics; gated to wave 3, Partial pre-registered, cannot block waves 1–2.
2. **`pushQ`/`iSup` plumbing at the pin** (Blocks 1, 6) — mechanical but fiddly; the two named sup-lemmas are looked up before committing to the `if`-form of `str_loopState`.
3. **`GoodQuantale` distributivity orientation at `∅`** (Block 5) — one-minute check, fallback witness named.
4. **Tower bookkeeping in G5⁻** — the annihilation must occur at a *reachable* point; the two-step tower is designed so the dead weight sits exactly at depth 2; if the `< κ` subtype plumbing bloats, the witness may be restated at `κ₀ = ℵ₀` (finite supports) without loss, since the fork verdict is per-instance anyway.
5. **Duplication hazard** — Block 0 re-exports; check ws4's existing surface first (gap note 1); duplication is a review finding against this workstream.
