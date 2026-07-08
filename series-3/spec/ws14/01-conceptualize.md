# WS14 — Phase 1: Conceptualize (blind register source)

*Charter-free by construction; BR for WS14's blind phases. Timestamp + hash selected candidates at Phase-2 commit.*

## The mathematical objects at stake

Three related targets on the weighted side, one on the plain side.

**(α) The hereditarily-supported subclass of `νWQ Q κ`.** For the weighted functor (`WQObj Q κ X` = functions `X → Q` with `< κ` support `Qsupp ρ = {x | ρ x ≠ ⊥}`, over a `GoodQuantale Q`), it is known that on the *plain* carrier `νPk κ` the hereditarily-nonempty states form a **singleton** (any two are equal via an Aczel–Mendler bisimulation whose projections agree exactly because supports are nonempty). At stake: whether weighting breaks that collapse — i.e., whether the weighted carrier contains **at least two distinct states all of whose reachable states have nonempty support**. The candidate mechanism: two self-loop states at distinct weights `q₁ ≠ q₂`, distinguishable by the *weight* of the loop rather than by reachable emptiness. Non-trivial because distinctness must pass through the terminal identification (`wq_bisim_eq`), and because the collapse argument's failure point (weight-matching in `WQBisim.ζ`) must be exactly where the proof lives.

**(β) Closure of the composition operator on the subclass.** `wqAlg : WQObj Q κ (νWQ).X → (νWQ).X` composes a weighted collection of states. At stake: whether composing hereditarily-supported states yields a hereditarily-supported state. Non-trivial — and plausibly **false for some quantales**: the composite weights involve the quantale multiplication, and quantales with `⊥`-divisors (e.g., Łukasiewicz chains: `a ⊗ b = ⊥` with `a, b ≠ ⊥`) can starve a weight to `⊥` in composition. The honest target is a **split**: closure under a no-`⊥`-divisors hypothesis, and an explicit failure witness in a nilpotent quantale.

**(γ) Uniqueness of weak distributive laws (plain functor).** For `PkObj κ` over itself, the strict distributive law is known empty; a weak law (Egli–Milner) exists as an algebra-side package. At stake: the *transformation-level* class — natural transformations `θ : Pk ∘ Pk ⇒ Pk ∘ Pk` satisfying the weak-law equations — its inhabitation and its uniqueness. Non-trivial: uniqueness (the analogue of the known set-functor result of Garner / Goy–Petrişan) requires pinning `θ` on arbitrary inputs from naturality against small test objects, the same technique as the strict no-go but run positively.

**(δ) A countably infinite divisible quantale.** All quantitative results are currently witnessed at the finite chains `Luk n`. At stake: an infinite `Q` with `Cardinal.mk Q ≤ κ` at `κ₀ = ℵ₀`, satisfying `GoodQuantale`, `IsQuantitative` (`∃ a, a * a ≠ a`), and — the interesting part — `DivisibleQuantale` (`weight_split`'s residuation). Candidate: the **Lawvere cost quantale** `ℕ∞` under the *reversed* order (lattice join = numeric `min`, `⊥` = numeric `∞`) with `⊗ = +` (truncated at `∞`), unit `0`. Divisibility check on paper: `w ≤ a ⊗ ⊤` in the reversed order means `w ≥ a` numerically (since `⊤ = 0`, `a ⊗ ⊤ = a`), and `b := w ∸ a` gives `w = a + b` — divisible, with no `⊥`-divisors (`a + b = ∞` iff one is `∞`). So `ℕ∞` simultaneously serves (δ) and the positive branch of (β).

Ambient theory throughout: `Cofix`-of-QPF encodings; functors `PkObj κ` (γ) and `WQObj Q κ` (α, β); the only "monad-like" structure is the union/`wqJoin` algebra; the strict law is known empty and never assumed. Universe note: quantale witnesses are `Type 0`, forcing `Cardinal.{0}` at instantiation (the standing constraint, inherited).

## Candidates

### G1 — Loop states at every weight

```lean
noncomputable def loopState (Q) [GoodQuantale Q] (κ) (q : Q) : (νWQ Q κ).X
-- the image of ⋆ under the terminal map from the one-state coalgebra
-- str ⋆ = (fun _ => q)  (support {⋆}, size 1 < κ)

theorem ws14_loop_str (hinf : ℵ₀ ≤ κ) (q : Q) :
    ((νWQ Q κ).str (loopState Q κ q)).1 (loopState Q κ q) = q
  ∧ ∀ y ≠ loopState Q κ q, ((νWQ Q κ).str (loopState Q κ q)).1 y = ⊥
```

**Strategy:** terminality gives the hom `h`; the hom equation computes `str (h ⋆) = WQMap h (const q)`, and `WQMap` is `pushQ` (sup over the preimage): at `h ⋆` the preimage is `{⋆}` so the weight is `q`; elsewhere the preimage is empty so the weight is `⊥` (`iSup` over `∅`).
**Success:** both conjuncts. **Failure condition:** the `pushQ` sup-computation needs `q ≠ ⊥` or decidable equality it doesn't have — engineering only; a genuine failure is not on the table.

### G2 — Plurality of loops (the anti-collapse witness)

```lean
theorem ws14_loop_ne (hinf) {q₁ q₂ : Q} (h : q₁ ≠ q₂) :
    loopState Q κ q₁ ≠ loopState Q κ q₂
```

**Strategy:** if equal (call it `s`), then by G1 `str s s = q₁` and `str s s = q₂`. Two lines given G1.
**Success:** proved — with G3 this is the statement that weighting defeats the plain-carrier collapse. **Failure condition:** would mean the terminal identification merges loops of distinct weights, i.e., `WQBisim` ignores weights — directly refutable against `wq_bisim_eq`'s definition; not expected.

### G3 — Loops are hereditarily supported

```lean
def WReaches (x y : (νWQ Q κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => ((νWQ Q κ).str a).1 b ≠ ⊥) x y
def HereditarilySupported (x) : Prop :=
  ∀ v, WReaches x v → Qsupp ((νWQ Q κ).str v).1 ≠ ∅

theorem ws14_loop_hereditary (hinf) {q : Q} (hq : q ≠ ⊥) :
    HereditarilySupported (loopState Q κ q)
```

**Strategy:** by G1, the only `⊥`-avoiding successor of the loop is itself, so `WReaches (loop q) v → v = loop q` (ReflTransGen induction); its support is `{loop q} ≠ ∅` by `hq`.
**Success/Failure:** as G1.

### G4 — The headline bundle: a plural, hereditarily-supported subclass

```lean
theorem ws14_graded_core_plural (hinf) {q₁ q₂ : Q}
    (h₁ : q₁ ≠ ⊥) (h₂ : q₂ ≠ ⊥) (hne : q₁ ≠ q₂) :
    ∃ x y : (νWQ Q κ).X, x ≠ y
      ∧ HereditarilySupported x ∧ HereditarilySupported y
```

**Strategy:** assemble G1–G3. Instantiate at `Luk n` (`n ≥ 2`: two non-`⊥` distinct weights exist) and, given G9, at `ℕ∞`.
**Success:** the theorem — the direct weighted counterpart, with opposite verdict, of the plain-carrier collapse. **Failure condition:** any of G1–G3 failing; a *mathematical* failure here (the weighted carrier also collapsing) would itself be a sharp reportable result, pre-registered as the alternative outcome.

### G5 — Closure of composition on the subclass: a split

```lean
/-- No ⊥-divisors. -/
def BotFree (Q) [GoodQuantale Q] : Prop := ∀ a b : Q, a * b = ⊥ → a = ⊥ ∨ b = ⊥

theorem ws14_core_closed (hreg : κ.IsRegular) [BotFree-hypothesis]
    (t : WQObj Q κ (νWQ Q κ).X)
    (ht : Qsupp t.1 ≠ ∅)
    (hmem : ∀ x ∈ Qsupp t.1, HereditarilySupported x) :
    HereditarilySupported (wqAlg hreg t)

theorem ws14_core_not_closed_Luk :   -- the failure witness, n ≥ 2
    ∃ (t : WQObj (Luk n) κ (νWQ (Luk n) κ).X), (hypotheses as above) ∧
      ¬ HereditarilySupported (wqAlg hreg t)
```

**Strategy (positive half):** `wqAlg_pentagon` computes the composite's unfolding as `wqJoin`; under `BotFree`, a composite weight `t s ⊗ (str s) y` is `≠ ⊥` whenever both factors are, so the composite's support contains the members' successor supports, nonemptiness propagates, and every state `WReaches`-reachable from the composite is reachable from some member (one lemma: reach-decomposition through the join) — then `hmem` closes. **Strategy (negative half):** in `Luk n`, pick weights `a, b ≠ ⊥` with `a ⊗ b = ⊥` (exists for `n ≥ 2` by `IsQuantitative`-adjacent arithmetic — verify the exact pair on paper per the `Luk` `⊗` definition at execute); build `t` weighting a loop state by `a` where the loop's own weight is `b`, so the one-step composite weight is `⊥` — the composite's support empties where the members' did not.
**Success:** the split, both halves. **Failure conditions, pre-registered per half:** (i) the positive half may need more than `BotFree` if `wqJoin` sups over ⊗-products in a shape that loses lower bounds — then the hypothesis is strengthened to the exact sufficient condition found, surfaced as a signature correction; (ii) the negative half may fail if `wqJoinFun`'s sup rescues the weight through another path — then the witness is redesigned with a single-path `t`; if no witness exists at all, closure is proved unconditionally and the split collapses to a positive (also reportable). The fork is open in both directions at conceptualize and that is the point.

### G6 — The weak-law transformation class: inhabitation and uniqueness

```lean
structure WeakDistLaw (κ : Cardinal.{u}) where
  θ : ∀ X : Type u, PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)
  natural : ∀ {X Y} (f : X → Y) S,
    θ Y (PkMap κ (PkMap κ f) S) = PkMap κ (PkMap κ f) (θ X S)
  -- unit and multiplication fields: bind to ws3's weak-bialgebra equations
  -- (the T-unit law on singletons and the Egli–Milner multiplication square),
  -- transcribed at transformation level; exact field shapes fixed at design review
  unit_law : …
  mult_law : …

theorem ws14_weak_law_inhabited (hinf hreg) : Nonempty (WeakDistLaw κ)
theorem ws14_weak_law_unique : ∀ L L' : WeakDistLaw κ, L = L'   -- or its refutation
```

**Strategy (inhabitation):** the Egli–Milner transformation `θ S := {T | T ⊆ ⋃S ∧ ∀ A ∈ S, (A ∩ T).Nonempty}` bounded to `< κ` members — carrying the cardinality of `θ S` below `κ` is the one non-formal step to check on paper first (the set of such `T` can be large: **pre-check before committing**; if `mk (θ S)` can reach `2^{<κ}`, the transformation-level object does not live in `PkObj κ` and the class must be re-typed over an enlarged codomain or the sub-`< κ` members only — this is a real design fork, flagged now). **Strategy (uniqueness):** naturality-pinning on small test types, reusing the fibre-map machinery (`fst`/`snd`/`xor` style) from the strict no-go, run positively: naturality against characteristic functions forces `θ`'s value pointwise.
**Success:** inhabitation + uniqueness (or a second inhabitant — reportable non-canonicity). **Failure conditions:** (i) the cardinality pre-check fails → re-typed class, surfaced as a signature correction before any proof effort; (ii) uniqueness resists pinning → Partial: uniqueness within a monotonicity-constrained subclass, with the constraint stated in the theorem, never in prose only.

### G7 — Weighted carrier cardinality lower bound

```lean
theorem ws14_wq_card_ge (hQ : ∃ q : Q, q ≠ ⊥) (κ) :
    κ ≤ Cardinal.mk (νWQ Q κ).X
```

**Strategy:** the Lambek–Cantor transfer: if `mk X < κ` then every `X → Q` has small support, so `WQObj Q κ X ≃ (X → Q)`; `wqLambek` gives `X ≃ (X → Q)`; with `#Q ≥ 2` (`⊥` and the witness `q`) this contradicts Cantor (`2^{mk X} ≤ mk (X → Q) = mk X`).
**Success:** proved; unlocks weighted analogues of the observer/standpoint properness results. **Failure:** none expected (same shape as the plain-carrier bound, already mechanized).

### G8 — Weighted standpoints (distinct, non-global, proper)

Weighted `Standpoint` (view = support membership of the base's unfolding) with the three theorems: distinct bases with distinct observations give distinct views; no view surjects onto the carrier; every view misses a state — all via G7. **Trade-off:** cheap, but consumed only by prose; **second wave** — after G4/G7, before G6.

### G9 — The Lawvere quantale `ℕ∞` as an infinite divisible witness

```lean
instance : GoodQuantale ℕ∞ᵒᵈ := …       -- reversed-order lattice, ⊗ = +, unit 0
instance : DivisibleQuantale ℕ∞ᵒᵈ := …  -- b := w ∸ a realizes weight_split
theorem ws14_lawvere_quantitative : IsQuantitative ℕ∞ᵒᵈ      -- 1 + 1 ≠ 1
theorem ws14_lawvere_botfree : BotFree ℕ∞ᵒᵈ                   -- a + b = ∞ → a = ∞ ∨ b = ∞
theorem ws14_lawvere_card : Cardinal.mk ℕ∞ᵒᵈ = Cardinal.aleph0
```

**Strategy:** `WithTop ℕ` order-dual; lattice completeness of `ℕ∞` is in Mathlib; distributivity of `+` over the dualized sups is the paper-checked step (`a + ⨅ S = ⨅ (a + S)` on `ℕ∞`, true including the `∞` cases — verify the empty-set convention against `GoodQuantale`'s exact distributivity field at design review). Divisibility via truncated subtraction.
**Success:** all five; combined with G4 and the positive half of G5, this yields an *infinite, divisible, quantitative, `⊥`-divisor-free* instantiation with `#Q = ℵ₀ ≤ κ₀`. **Failure condition:** the `GoodQuantale` distributivity field may quantify over sups in the orientation where `ℕ∞` fails at `∅` — then either the field's convention is accommodated (`sSup ∅ = ⊥` cases) or the witness is swapped for the dyadic-supported complete sublattice; if *no* countable divisible witness exists under the class's exact axioms, that impossibility is itself the reportable outcome.

## Trade-off summary

G1–G4 are one construction and decide the central question (does weighting defeat the collapse) with a concrete mechanism; they are the mandatory first wave. G7 is a cheap transfer that unlocks G8. G9 is self-contained instance work whose payoff (an infinite quantitative witness with `#Q ≤ κ`, divisible, `⊥`-free) upgrades every "at the finite witness" caveat at once and feeds G5's positive half. G5 is the sharpest and riskiest item — a genuine two-sided fork about composition vs support, with the quantale's `⊥`-divisor structure as the deciding invariant. G6 is the heaviest and most independent; its cardinality pre-check is a hard gate before any proof effort is spent.
