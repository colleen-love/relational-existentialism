# WS12 — Phase 1: Conceptualize (blind register source)

*Charter-free by construction; BR for WS12's blind phases. Timestamp + hash selected candidates at Phase-2 commit.*

## The mathematical object at stake

On the terminal coalgebra `νPk κ`, all existing "no state dominates" results quantify over the **one-step** successor set: `IsMaximal u := ∀ v, v ∈ (str u).1`, and the observer/standpoint theorems restrict to `SelfSupport κ u` (the subtype of immediate successors). At stake is the **hereditary** strengthening: the reflexive-transitive closure `Reaches u v` (already defined) and the reachable set

```lean
def ReachSet (u : (νPk κ).X) : Set (νPk κ).X := {y | Reaches u y}
```

Three questions, in decreasing order of foundational weight:

1. How large can `ReachSet u` be, as a function of `κ`? (An upper bound theorem.)
2. How large is the carrier itself — strictly larger than the reachable bound? (`carrier_card_ge` gives only `κ ≤ #X`; a **strict** gap is needed and is not currently proved for any `κ`.)
3. Given 1 + 2: no state hereditarily reaches every state, and no map from a reachable set surjects onto the carrier.

Non-trivial because: (1) needs the regularity of `κ` for the level-wise unions but the ω-indexed union at `κ = ℵ₀` only yields `≤ ℵ₀`, not `< ℵ₀`, so the strict gap must come from (2); and (2) requires injecting `2^ℵ₀` pairwise-distinct states into the carrier at `κ₀ = ℵ₀` — the carrier's states are finitely branching there, so the injection must code subsets of `ℕ` into infinite-depth branching patterns and prove distinctness through the terminal identification. At a strong-limit regular `κ` the strict gap plausibly **fails** (`2^{<κ} = κ`), so the general-`κ` form is not a target; the concrete `ℵ₀` instance is.

## Candidates

Ambient theory throughout: `Cofix`-of-QPF encoding, `F = PkObj κ`; no monad, no distributive law. Candidates R2–R4 fix `κ = Cardinal.aleph0.{0}`.

### R1 — Reachable-set cardinality bound

```lean
theorem ws12_reachable_card_le (hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ)
    (u : (νPk κ).X) : Cardinal.mk ↥(ReachSet u) ≤ κ

theorem ws12_reachable_card_lt (hreg : κ.IsRegular) (hunc : ℵ₀ < κ)
    (u : (νPk κ).X) : Cardinal.mk ↥(ReachSet u) < κ
```

**Strategy:** define `level u : ℕ → Set X` by `level 0 = {u}`, `level (n+1) = ⋃ v ∈ level n, (str v).1`; prove `ReachSet u = ⋃ n, level u n` (induction on `Relation.ReflTransGen`); `mk (level n) < κ` by induction using the regular-cardinal union bound (the `iSup_lt_of_isRegular` pattern already consumed in ws3's `pkJoin`); the ω-union gives `≤ ℵ₀ * sup ≤ κ`, and `< κ` when `cof κ > ω` (regular uncountable).
**Success:** both statements. **Failure condition:** the uncountable strict form stalls on Mathlib cofinality API — then ship the `≤ κ` form plus the `ℵ₀` instance (`≤ ℵ₀`), which is all R3/R4 consume; declared Partial-in-generality.

### R2 — Continuum injection at `ℵ₀` (the keystone)

```lean
theorem ws12_carrier_card_continuum :
    2 ^ Cardinal.aleph0 ≤ Cardinal.mk (νPk Cardinal.aleph0.{0}).X

theorem ws12_carrier_card_gt :
    Cardinal.aleph0 < Cardinal.mk (νPk Cardinal.aleph0.{0}).X
```

**Strategy:** for `A : Set ℕ` define the **spine coalgebra** on `Option ℕ`:
`str none = ∅`; `str (some n) = {some (n+1)} ∪ (if n ∈ A then {none} else ∅)` — finitely branching (≤ 2). Let `h_A` be the map to the terminal coalgebra; set `encode A := h_A (some 0)`. Injectivity of `encode`: from `encode A = encode B` derive by induction `∀ n, h_A (some n) = h_B (some n) ∧ (n ∈ A ↔ n ∈ B)`, using three facts: (a) `h(none) = bottomState` (its unfolding is the image of `∅`, hence `∅`; conclude by injectivity of `str`); (b) `h(some k) ≠ bottomState` (nonempty unfolding image); (c) equal states have equal unfoldings, and inside the unfolding the spine child is separated from `bottomState` by (b), so the presence of `bottomState` reads off `n ∈ A` and the spine children propagate the induction. Then `2^ℵ₀ = mk (Set ℕ) ≤ mk X` by `mk_le_of_injective`, and the strict corollary is Cantor.
**Success:** both statements. **Failure condition:** the induction stalls on image-of-finite-set bookkeeping — then every downstream theorem ships **conditionally** on a typed hypothesis `hgt : ℵ₀ < mk (νPk ℵ₀).X` (visible, never silent), declared Partial. A genuine mathematical failure (encode non-injective) is not expected; it would mean two distinct spine systems are bisimilar, refutable on paper by the depth-`n` argument above.
**Non-target (recorded):** the general-`κ` strict gap `κ < mk (νPk κ).X` is *not* claimed; at strong-limit regular `κ` it may be false. Left as an open remark, not an obligation.

### R3 — Hereditary non-domination at `ℵ₀`

```lean
theorem ws12_no_hereditary_maximal (u : (νPk Cardinal.aleph0.{0}).X) :
    ¬ ∀ v, Reaches u v
```

**Strategy:** a hereditarily-dominating `u` makes `ReachSet u` the whole carrier; R1 bounds it by `ℵ₀`, R2 bounds the carrier strictly above. **Success:** proved. **Failure:** only via R1/R2 failing; then the conditional form on `hgt`.

### R4 — No surjection from a reachable set

```lean
theorem ws12_no_hereditary_observer (obs : (νPk Cardinal.aleph0.{0}).X) :
    ¬ ∃ f : ↥(ReachSet obs) → (νPk Cardinal.aleph0.{0}).X, Function.Surjective f
```

**Strategy:** a surjection gives `mk X ≤ mk (ReachSet obs) ≤ ℵ₀ < mk X`. Strictly stronger than the existing one-step observer theorem (the domain is the full hereditary closure, i.e., every finite-depth observation round simultaneously). **Success/Failure:** as R3.

### R5 — Generic conditional architecture

Not a separate theorem: state R3/R4 first at generic regular `κ` under the typed hypotheses `(hreach : mk ↥(ReachSet u) ≤ κ)` and `(hgt : κ < mk (νPk κ).X)`, then instantiate at `ℵ₀` by R1 + R2. **Trade-off:** costs a small amount of statement plumbing; buys the fallback path for R2's failure condition and reusability at any future `κ` where a strict gap is proved.

### R6 — Hereditary view properness

```lean
theorem ws12_hereditary_view_proper (u : (νPk Cardinal.aleph0.{0}).X) :
    ∃ y, ¬ Reaches u y
```

**Strategy:** contrapositive of R3 restated existentially (classically equivalent; stated separately because it is the form downstream consumers want: every state's hereditary horizon misses some state). Free given R3.

### R7 — ω-round observer towers (folded)

An observer enumerating in ω rounds reaches exactly `ReachSet` — extensionally identical to R4's domain. **Folded into R4**; recorded so the equivalence is explicit rather than tacit.

## Trade-off summary

R2 is the only genuinely new mathematics and the only real risk; everything else is cardinal arithmetic hanging off it and R1. The candidate set deliberately contains its own fallback (R5): if R2 stalls, the workstream still ships hereditary theorems with one visible typed hypothesis, and the `hgt` discharge becomes a routed obligation rather than a silent assumption.
