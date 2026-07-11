# WS13 — Phase 2: Design

## Triage (decidable on paper, per candidate)

| # | Candidate | Paper-decidable? | New math? | Risk | Lean cost | Consumers | Verdict |
|---|---|---|---|---|---|---|---|
| P1 | Kuratowski pairing, `Injective2` | yes (classical argument transfers verbatim under strong extensionality) | no (transfer) | low (case-bash volume) | M | P3, P4, P6, WS15 | **select** |
| P2 | nested-tag pairing | yes | no | low | M | — | fallback only |
| P3 | reify + faithfulness | yes | no | low | S | P4, P6 | **select** |
| P4 | membership characterization | yes | no | low | S | P6, external | **select** |
| P5 | dom/ran recovery | yes | no | low | S | none | defer |
| P6 | iterated reification | yes | no | none | XS | external | **select** |
| P7 | graded pairing | yes | no | — | — | graded workstream | route |

Decision: **{P1, P3, P4, P6}**, P2 named fallback, P5 deferred corollary, P7 routed. Note the cross-workstream export: `mkState` and its two lemmas are consumed by WS15 (self-model construction) — they belong in a shared section at the top of this file, stated once.

## Proof architecture

**File:** `series-03/formal/ws13.lean`, namespace `Series03.WS13`, `import ws2`.

### Block 0 — the state-former (exported interface)

```lean
noncomputable def destEquivPk (κ) : (νPk κ).X ≃ PkObj κ (νPk κ).X :=
  Equiv.ofBijective _ (lambek (νPk_terminal κ))

noncomputable def mkState (s : PkObj κ (νPk κ).X) : (νPk κ).X :=
  (destEquivPk κ).symm s

@[simp] theorem str_mkState (s) : (νPk κ).str (mkState s) = s :=
  (destEquivPk κ).apply_symm_apply s
@[simp] theorem mkState_str (u) : mkState ((νPk κ).str u) = u :=
  (destEquivPk κ).symm_apply_apply u
theorem mkState_inj : Function.Injective (mkState (κ := κ)) :=
  (destEquivPk κ).symm.injective
```

Gap note 1: ws4 already has a `destEquivWQ` for the weighted functor (ws4:556) — mirror its naming and idioms so the two carriers' interfaces stay parallel; if a plain `destEquiv` for `νPk` already exists in ws8's canonicity section, **reuse it** instead of redefining (check at execute; duplication would be a review finding against this workstream).

### Block 1 — small-set cardinality helpers

```lean
theorem mk_singleton_lt (hinf : ℵ₀ ≤ κ) (x : α) : Cardinal.mk ↥({x} : Set α) < κ
theorem mk_pair_lt (hinf) (x y : α) : Cardinal.mk ↥({x, y} : Set α) < κ
```

Both via `Cardinal.mk_singleton` / `mk_insert_le` and `Nat.cast_lt_aleph0`-style facts, chained with `hinf`. These feed every `⟨_, _⟩` subtype introduction below; making them standalone keeps the constructions one-liners.

### Block 2 — pairing (P1)

Definitions `sing`, `doub`, `pairK` as in the BR. Lemma ladder (each reduces to the previous):

```lean
@[simp] lemma str_sing (x) : ((νPk κ).str (sing hinf x)).1 = {x}
@[simp] lemma str_doub (x y) : ((νPk κ).str (doub hinf x y)).1 = {x, y}
lemma sing_inj : Function.Injective (sing hinf)
lemma doub_eq_iff : doub hinf x y = doub hinf x' y' ↔ ({x, y} : Set _) = {x', y'}
lemma sing_ne_doub (h : x ≠ y) : sing hinf z ≠ doub hinf x y
-- unfoldings have different cardinalities: {z} vs {x, y} with x ≠ y
```

Core case analysis:

```lean
theorem ws13_pair_inj (hinf) : Function.Injective2 (pairK (κ := κ) hinf)
```

Proof plan: from `pairK x y = pairK x' y'`, `mkState_inj` + `Subtype.ext_iff` give
`({sing x, doub x y} : Set _) = {sing x', doub x' y'}`. Split on `x = y` vs `x ≠ y` (and primed). Degenerate branch (`x = y`): `pairK x x` has unfolding `{sing x, doub x x} = {sing x}` (since `doub x x = sing x` — prove `doub_self : doub hinf x x = sing hinf x` via set `{x,x} = {x}` and `mkState` congruence); equality then forces the primed side degenerate too and `sing_inj` closes. Non-degenerate branch: `sing_ne_doub` separates the two elements on each side, so `sing x = sing x'` and `doub x y = doub x' y'` (two-element set matching, done by hand at the two named elements — gap note 2: do **not** reach for general `Set.pair_eq_pair_iff` unless it exists at the pin; the by-hand version is 15 lines and stable). Then `sing_inj` gives `x = x'` and `doub_eq_iff` + Kuratowski's last step gives `y = y'`.

Mathlib assist check (gap note 3): `Set.pair_eq_pair_iff` exists in current Mathlib; verify presence at v4.15.0, else inline.

### Block 3 — reification (P3, P4)

```lean
noncomputable def pairFun (hinf) : (νPk κ).X × (νPk κ).X → (νPk κ).X :=
  fun p => pairK hinf p.1 p.2
lemma pairFun_inj : Function.Injective (pairFun hinf) :=
  fun _ _ h => Prod.ext_iff.mpr (ws13_pair_inj hinf h …)

noncomputable def reify (hinf) (R : Set (_ × _)) (hR : Cardinal.mk ↥R < κ) : (νPk κ).X :=
  mkState ⟨pairFun hinf '' R, lt_of_le_of_lt (Cardinal.mk_image_le …) hR⟩

theorem ws13_reify_inj … := -- mkState_inj → image eq → Set.image_injective pairFun_inj
theorem ws13_reify_mem … :
    pairFun hinf (x, y) ∈ ((νPk κ).str (reify hinf R hR)).1 ↔ (x, y) ∈ R
-- str_mkState; ← : mem_image_of_mem; → : rcases the image witness, pairFun_inj
```

Gap note 4: `Cardinal.mk_image_le` states `mk ↥(f '' s) ≤ mk ↥s` — confirm exact form (it may be stated via `lift`; at a single universe this is transparent, but the `.{0}` vs `.{u}` bookkeeping should be pinned once here since WS15 will re-consume `reify`).

### Block 4 — iteration (P6) and the bundle

```lean
theorem ws13_reify_iterated (hinf) (R S hR hS) :
    ∃ r, ((νPk κ).str r).1
      = {pairK hinf (reify hinf R hR) (reify hinf S hS)} :=
  ⟨mkState ⟨{_}, mk_singleton_lt hinf _⟩, by simp [str_mkState]⟩

structure WS13Reification (κ) (hinf : ℵ₀ ≤ κ) where
  pair_inj  : Function.Injective2 (pairK (κ := κ) hinf)
  reify_inj : ∀ {R S hR hS}, reify hinf R hR = reify hinf S hS → R = S
  reify_mem : ∀ R hR x y, pairK hinf x y ∈ ((νPk κ).str (reify hinf R hR)).1 ↔ (x,y) ∈ R
  iterated  : ∀ R S hR hS, ∃ r, ((νPk κ).str r).1 = {pairK hinf (reify …) (reify …)}

theorem ws13_reification (hinf : ℵ₀ ≤ κ) : WS13Reification κ hinf
```

`#print axioms ws13_reification` added to `AxiomCheck.lean` (expected `[propext, Classical.choice, Quot.sound]` — choice enters via `destEquivPk`; record that nothing else does).

## Dependencies

| Import | Used for |
|---|---|
| ws1: `lambek`, `PkObj`, subtype plumbing | Block 0 |
| ws2: `νPk`, `νPk_terminal` | Block 0 |
| ws8 (check-only): possible existing `destEquiv` | Block 0 gap note 1 |
| Mathlib: `Equiv.ofBijective`, `Cardinal.mk_singleton/mk_insert/mk_image_le`, `Set.pair_eq_pair_iff` (or inline) | Blocks 1–3 |

Exports consumed downstream: `mkState`, `str_mkState`, `mkState_inj` (WS15); `pairK`, `reify`, `ws13_reify_mem` (any future graded transfer).

## Risk register

1. Kuratowski case volume (Block 2) — bounded by the `doub_self` degenerate-branch trick and by refusing general set automation; fallback P2 pre-registered but not expected to trigger.
2. Universe/`lift` friction in `mk_image_le` (gap note 4) — pin once in Block 3.
3. Duplication hazard with an existing `destEquiv` (gap note 1) — resolved by a grep at execute before writing Block 0.

Nothing in this workstream has a mathematical failure mode; a "failure" here is an engineering stall, to be reported as Partial with the stalled lemma named.

*Selected candidates for hashing at commit: P1, P3, P4, P6 (bundle `ws13_reification`).*
