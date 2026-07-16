# WS12 — Phase 2: Design

## Triage (decidable on paper, per candidate)

| # | Candidate | Paper-decidable? | New math? | Risk | Lean cost | Consumers | Verdict |
|---|---|---|---|---|---|---|---|
| R1 | reachable ≤ κ (+ strict for uncountable) | yes (regular unions; ws3 pattern exists) | no | low (`≤` form), med (`<` form) | M | R3, R4, R6 | **select** (`≤` form mandatory; `<` form best-effort) |
| R2 | `2^ℵ₀ ≤ #X` at `ℵ₀` | yes (classic; depth-induction argument closes on paper) | **yes — keystone** | med-high (bookkeeping) | L | R3, R4, R6 | **select** |
| R3 | no hereditary maximal | trivial given R1+R2 | no | low | S | summaries | **select** |
| R4 | no reachable-set surjection | trivial given R1+R2 | no | low | S | summaries | **select** |
| R5 | generic conditional architecture | n/a (architecture) | no | none | S | fallback path | **adopt** |
| R6 | hereditary view properness | trivial given R3 | no | low | XS | summaries | **select** |
| R7 | ω-round towers | identical to R4 | no | — | — | — | fold into R4 |

Decision: architecture R5; theorems R1 (`≤` mandatory), R2, R3, R4, R6. The `<`-for-uncountable half of R1 is a stretch goal, not load-bearing (nothing at the ratified tuple `κ₀ = ℵ₀` consumes it).

## Proof architecture

**File:** `series-03/formal/ws12.lean`, namespace `Series03.WS12`, `import ws10` (brings `Reaches`, `carrier_card_ge`, and transitively ws1/ws2/ws6 — `bottomState` lives in ws6).

### Block 1 — levels and the reachable bound (R1)

```lean
def level (u : (νPk κ).X) : ℕ → Set (νPk κ).X
  | 0     => {u}
  | n + 1 => ⋃ v ∈ level u n, ((νPk κ).str v).1

lemma reachSet_eq_iUnion_level (u) : ReachSet u = ⋃ n, level u n
```

Forward inclusion: induction on `Relation.ReflTransGen` (its `head`/`tail` recursor; a reachable `y` sits at the depth of its witnessing chain). Reverse: induction on `n`, `Reaches` is closed under one successor step (`ReflTransGen.tail`).

```lean
lemma mk_level_lt (hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ) (u) (n) :
    Cardinal.mk ↥(level u n) < κ
```

Induction: base is `mk {u} = 1 < κ`; step is a union over an index set of size `< κ` of sets of size `< κ` — the exact shape of ws3's `iSup_lt_of_isRegular` use (`Cardinal.mk_biUnion_le` + `Cardinal.mul_lt_of_lt` under regularity; confirm the precise Mathlib lemma names at execute — gap note 1).

```lean
theorem ws12_reachable_card_le … : Cardinal.mk ↥(ReachSet u) ≤ κ
```

`mk ⋃ n, level n ≤ ∑ n, mk (level n) ≤ ℵ₀ * κ = κ` (using `hinf`; `Cardinal.mk_iUnion_le`, `Cardinal.aleph0_mul_eq` / `mul_eq_max`). Stretch: `<` when `ℵ₀ < κ` via `Cardinal.iSup_lt_of_isRegular` applied to the ω-indexed family (regularity gives `cof κ > ω` — `Cardinal.IsRegular.aleph0_lt_cof` or equivalent; gap note 1 covers name drift).

### Block 2 — the spine injection (R2, the keystone)

```lean
def spineCoalg (A : Set ℕ) : Coalg Cardinal.aleph0.{0} where
  X := Option ℕ
  str
    | none        => ⟨∅, by simp⟩
    | some n      => ⟨insert (some (n+1)) (if n ∈ A then {none} else ∅), hfin⟩
```

(`hfin`: a set of ≤ 2 elements is finite, `mk < ℵ₀`; `Classical.dec` for the membership test — no decidability instance on `A` required.)

Let `hA := (νPk_terminal _ ).choose`-style: bind to the exact `∃!` shape of `IsTerminalCoalg` to extract the hom `h_A : Option ℕ → (νPk ℵ₀).X` and its equation `hhom : ∀ z, str (h_A z) = PkMap _ h_A (spineCoalg A |>.str z)` (gap note 2: extraction idiom).

Supporting lemmas, in dependency order:

```lean
lemma hA_none : h_A none = bottomState (le_refl ℵ₀ …)
-- str (h_A none) = PkMap h_A ∅ = ∅ = str bottomState; conclude by str-injectivity (lambek)

lemma hA_spine_ne_bottom (n) : h_A (some n) ≠ bottomState …
-- str (h_A (some n)) contains h_A (some (n+1)): PkMap of a set containing some (n+1);
-- nonempty ≠ ∅

lemma str_hA_spine (n) :
    ((νPk _).str (h_A (some n))).1
      = insert (h_A (some (n+1))) (if n ∈ A then {bottomState …} else ∅)
-- image computation: PkMap = Set.image on the .1 component (ws1:91), plus hA_none
```

The induction core:

```lean
lemma spine_step {A B : Set ℕ} {n : ℕ}
    (h : h_A (some n) = h_B (some n)) :
    (n ∈ A ↔ n ∈ B) ∧ h_A (some (n+1)) = h_B (some (n+1))
```

From `h`, equal unfoldings; by `str_hA_spine` both sides are `insert (spine child) (bottom-or-not)`. Membership of `bottomState` in the set decides `n ∈ A` (spine children are `≠ bottomState` by `hA_spine_ne_bottom`, so `bottomState ∈ set ↔ n ∈ A` exactly) — giving the first conjunct; removing `bottomState` leaves singleton spine children equal — the second. Gap note 3: the two-element set extensionality is the fiddliest step; do it via `Set.ext_iff` specialized at `bottomState` and at each spine child, never via general finite-set automation.

```lean
def encode (A : Set ℕ) : (νPk Cardinal.aleph0.{0}).X := h_A (some 0)

theorem encode_injective : Function.Injective encode
-- from encode A = encode B, strong induction with spine_step gives
-- ∀ n, n ∈ A ↔ n ∈ B; Set.ext

theorem ws12_carrier_card_continuum : 2 ^ Cardinal.aleph0 ≤ Cardinal.mk _ :=
  by simpa [Cardinal.mk_set] using Cardinal.mk_le_of_injective encode_injective

theorem ws12_carrier_card_gt : Cardinal.aleph0 < Cardinal.mk _ :=
  lt_of_lt_of_le (Cardinal.cantor _) ws12_carrier_card_continuum
```

Subtle point (pre-registered, from the paper argument): the induction needs `h_A (some (n+1)) = h_B (some (n+1))` as states of the *terminal* carrier — the homs come from different coalgebras but land in the same codomain, so equality is well-typed and `spine_step` closes; no bisimulation-up-to machinery is needed anywhere.

### Block 3 — generic conditional forms + `ℵ₀` instances (R5, R3, R4, R6)

```lean
theorem ws12_no_hereditary_maximal' (hreach : Cardinal.mk ↥(ReachSet u) ≤ κ)
    (hgt : κ < Cardinal.mk (νPk κ).X) : ¬ ∀ v, Reaches u v
theorem ws12_no_hereditary_observer' (hreach …) (hgt …) : ¬ ∃ f, Surjective f
theorem ws12_hereditary_view_proper' (hreach …) (hgt …) : ∃ y, ¬ Reaches u y
```

Each is a three-line cardinal comparison (`ReachSet = univ` forces `mk X ≤ mk ReachSet`; surjection forces the same via `Cardinal.mk_le_of_surjective`). Instantiate all three at `ℵ₀` with R1 + R2:

```lean
theorem ws12_no_hereditary_maximal (u) : ¬ ∀ v, Reaches u v := …
theorem ws12_no_hereditary_observer (obs) : ¬ ∃ f, Surjective f := …
theorem ws12_hereditary_view_proper (u) : ∃ y, ¬ Reaches u y := …
```

### Block 4 — bundle and axiom check

```lean
structure WS12Hereditary where
  reach_le      : ∀ u, Cardinal.mk ↥(ReachSet u) ≤ Cardinal.aleph0
  card_gt       : Cardinal.aleph0 < Cardinal.mk (νPk Cardinal.aleph0.{0}).X
  no_her_max    : ∀ u, ¬ ∀ v, Reaches u v
  no_her_obs    : ∀ obs, ¬ ∃ f : ↥(ReachSet obs) → _, Function.Surjective f

theorem ws12_hereditary_scope : WS12Hereditary
```

Named for the scope upgrade it delivers, not `ws12_resolved` (the uncountable strict bound and the general-`κ` gap remain open remarks). `#print axioms ws12_hereditary_scope` added to `AxiomCheck.lean`.

## Dependencies

| Import | Used for |
|---|---|
| ws10: `Reaches` | everywhere |
| ws1: `Coalg`, `PkObj`, `PkMap`, `lambek`, `IsTerminalCoalg` | Block 2 |
| ws2: `νPk`, `νPk_terminal` | Block 2 |
| ws6: `bottomState`, its `str = ∅` lemma (ws6:207) | Block 2 |
| ws3 (pattern only): `iSup_lt_of_isRegular` usage | Block 1 |
| Mathlib: `Cardinal.mk_iUnion_le`, `mk_biUnion_le`, `mk_le_of_injective`, `mk_le_of_surjective`, `cantor`, `mk_set`, regular-cardinal API | Blocks 1–3 |

## Risk register and fallback

1. **R2 bookkeeping (main risk).** Mitigation: the three supporting lemmas isolate every image computation; `spine_step` is the only place set-extensionality is bashed. Fallback (pre-registered): ship Block 3's conditional forms with `hgt` as a visible typed hypothesis; the `ℵ₀` instances move to a routed obligation. The workstream still reports the hereditary theorems — conditionally — and is honest about it.
2. **R1 strict form at uncountable κ** — stretch only; absence costs nothing downstream.
3. **Name drift on cardinal lemmas** (gap notes 1–2) — resolved at execute against the pinned Mathlib.

*Selected candidates for hashing at commit: R1(≤), R2, R3, R4, R5-architecture, R6.*
