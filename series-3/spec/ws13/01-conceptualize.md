# WS13 — Phase 1: Conceptualize (blind register source)

*Charter-free by construction; BR for WS13's blind phases. Timestamp + hash selected candidates at Phase-2 commit.*

## The mathematical object at stake

On the terminal coalgebra `νPk κ`, Lambek's lemma makes `str : X → PkObj κ X` a **bijection**: every `< κ`-sized subset of the carrier is the unfolding of exactly one state. This gives an internal state-former

```lean
noncomputable def mkState : PkObj κ (νPk κ).X → (νPk κ).X :=
  (Equiv.ofBijective _ (lambek (νPk_terminal κ))).symm
```

with `str_mkState : (νPk κ).str (mkState s) = s` and `mkState_inj`. At stake: whether **ordered pairs of states, and hence binary relations between states, exist as states** — i.e., an injective pairing `X × X ↪ X` definable through `mkState`, and a faithful reification `{R : Set (X × X) // mk R < κ} ↪ X` whose membership structure recovers `R`. Non-trivial not because injectivity is in doubt (the carrier is strongly extensional, so the classical Kuratowski argument should transfer verbatim) but because it upgrades the sense in which edges/relations are first-class: currently "a relation" is only a successor occurrence with no identity of its own; after this workstream a `< κ` relation is a *state*, with pairs as states, iterable (relations between relations are again states).

Ambient theory for all candidates: `Cofix`-of-QPF encoding; `F = PkObj κ`; `hinf : ℵ₀ ≤ κ` (so finite sets are `< κ`); no monad, no distributive law. Everything is `noncomputable` through `mkState` (a choice-backed inverse); no new axioms.

## Candidates

### P1 — Kuratowski pairing

```lean
noncomputable def sing (hinf : ℵ₀ ≤ κ) (x : (νPk κ).X) : (νPk κ).X :=
  mkState ⟨{x}, by …⟩          -- mk {x} = 1 < κ
noncomputable def doub (hinf) (x y) : (νPk κ).X := mkState ⟨{x, y}, by …⟩
noncomputable def pairK (hinf) (x y) : (νPk κ).X :=
  mkState ⟨{sing hinf x, doub hinf x y}, by …⟩

theorem ws13_pair_inj (hinf : ℵ₀ ≤ κ) :
    Function.Injective2 (pairK (κ := κ) hinf)
```

**Strategy:** `mkState_inj` + `Subtype.ext_iff` reduce pair equality to set equality of two-element sets of states; `sing`/`doub` injectivity likewise reduce to `{x} = {x'}` and `{x,y} = {x',y'}`; then the standard Kuratowski case analysis (`Set.pair_eq_pair_iff` or hand-rolled ~40 lines). Membership of a `doub` in a `sing`-position and vice versa is ruled out by cardinality of the unfoldings (`{x}` vs `{x,y}` with `x ≠ y`), exactly as in ZF.
**Success:** `Injective2`. **Failure condition:** none mathematical (failure would contradict `mkState_inj` + set extensionality, i.e., strong extensionality of the carrier); residual risk is proof-engineering only.

### P2 — Tagged/nested pairing variant

`pair x y := mkState {sing x, mkState {sing y}}` (asymmetric nesting encodes order). **Trade-off:** avoids the two-doubleton Kuratowski bash but introduces its own collision analysis (`sing x` vs `mkState {sing y}` can coincide when `x = sing y`), so the case count is not actually smaller. **Rejected unless P1 stalls**; kept as the named fallback.

### P3 — Relation reification

```lean
noncomputable def reify (hinf) (R : Set ((νPk κ).X × (νPk κ).X))
    (hR : Cardinal.mk ↥R < κ) : (νPk κ).X :=
  mkState ⟨(fun p => pairK hinf p.1 p.2) '' R, by …⟩   -- mk image ≤ mk R < κ

theorem ws13_reify_inj (hinf) :
    ∀ {R S hR hS}, reify hinf R hR = reify hinf S hS → R = S
```

**Strategy:** `mkState_inj` gives image equality; `pairK` injectivity (P1) makes `Set.image` injective on relations (`Set.image_injective.mpr` of an injective function, modulo the uncurrying); conclude `R = S`. Cardinality side: `Cardinal.mk_image_le`.
**Success:** faithfulness. **Failure:** inherits only P1's (none mathematical).

### P4 — Membership characterization

```lean
theorem ws13_reify_mem (hinf) (R) (hR) (x y) :
    pairK hinf x y ∈ ((νPk κ).str (reify hinf R hR)).1 ↔ (x, y) ∈ R
```

**Strategy:** `str_mkState` computes the unfolding as the image; forward direction uses P1's injectivity to pull the witnessing pair back; backward is `Set.mem_image_of_mem`. This is the statement that reified relations are *usable* (application/lookup), not just distinct.
**Success/Failure:** as P3.

### P5 — Domain/range recovery (optional corollary)

`ws13_dom`, `ws13_ran`: the domain and range of `R` are recoverable from the reified state's second-level unfoldings. **Trade-off:** true and cheap once P4 exists, but consumed by nothing downstream. **Deferred** — recorded as a corollary target, cut if time-boxed.

### P6 — Iterated reification (closure demonstration)

```lean
theorem ws13_reify_iterated (hinf) (R S hR hS) :
    ∃ r : (νPk κ).X,
      ((νPk κ).str r).1 = {pairK hinf (reify hinf R hR) (reify hinf S hS)}
```

**Strategy:** `r := mkState ⟨{pairK …}, _⟩`; `str_mkState`. One line of content — its value is making iterability (relations whose relata are reified relations) an explicit theorem rather than a remark.
**Success:** trivially; **Failure:** none.

### P7 — Graded pairing on `νWQ` (routed)

The same construction through `wqLambek` on the weighted carrier. **Routed** to the graded workstream (it needs that workstream's support conventions); recorded here only so the plain/graded split is visible.

## Trade-off summary

P1 is the only real work; P3, P4, P6 are short consequences that turn it into a usable interface. P2 buys nothing unless P1's case bash misbehaves. P5 is decoration. The bundle {P1, P3, P4, P6} makes the following composite statement provable, which is the point of the workstream: *for every `< κ` binary relation `R` on the carrier there is a state `⌜R⌝` such that `⌜R⌝`'s unfolding consists exactly of pair-states, membership of a pair-state in `⌜R⌝` decides `R`, distinct relations get distinct states, and `⌜·⌝` may be applied to relations between reified relations.* Every ingredient is `noncomputable` but axiom-clean (choice enters only through `mkState`).
