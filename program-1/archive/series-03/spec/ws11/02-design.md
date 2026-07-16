# WS11 — Phase 2: Design

## Triage (decidable on paper, per candidate)

| # | Candidate | Non-vacuous? | Upstream API only? | Decides a direction? | New defs | Lean cost | Verdict |
|---|---|---|---|---|---|---|---|
| K1 | terminal downward determination | yes (anchor) | `lambek`, `νPk_terminal` | no (known) | 0 | XS | keep as corollary |
| K2 | extensional ⇒ downward-determined | yes | `Bisim` (ws1), nothing else | yes — negative, general | 3 | S | **select** |
| K3 | redundancy corollary | marginal | K2 | no | 0 | XS | keep as corollary |
| K4 | ¬(extensional ∧ upward-load-bearing) | yes | K2 | yes — the impossibility form | 1 | XS | **select** |
| K5 | 3-state witness | yes | `Coalg`, `PkObj`, `hinf` | yes — positive, concrete | 1 | S–M | **select** |
| K6 | terminal map erases upward distinctions | yes | `IsTerminalCoalg`, `PkMap` | mechanism (explanatory) | 1 | S | **select** |
| K7 | quotient-reflection characterization | yes | needs new reflection infra | no extra decision | many | L | reject |

Decision: **{K2, K4, K5, K6}**, corollaries K1, K3. Both admissible terminal outcomes are covered: the impossibility is proved at schema level (K2/K4) and the possibility is proved by witness (K5); no outcome of this workstream can require reframing.

## Proof architecture

**File:** `series-03/formal/ws11.lean`, namespace `Series03.WS11`, `import ws2` (which transitively brings ws1).

### Block 1 — definitions

`DownwardDetermined`, `UpView`, `StronglyExtensional`, `JointlyDetermined`, `UpwardLoadBearing`, `IsCoalgHom` exactly as in the BR. No `noncomputable` needed anywhere in this block.

### Block 2 — the schema (K2)

Key lemma:

```lean
/-- Equality-of-unfoldings is a bisimulation on any coalgebra. -/
def strEqBisim (C : Coalg κ) : Bisim C (fun a b => C.str a = C.str b) where
  ζ := fun p => PkMap κ (fun v => ⟨(v, v), rfl⟩) (C.str p.1.1)
  -- projection fields: both projections of ζ p compute
  -- PkMap κ Prod.fst/snd ∘ (diagonal) = C.str p.1.1 = C.str p.1.2 (by p.2)
```

Gap note 1 (binds at execute): the exact field names and orientation of `Bisim`'s two projection laws (ws1:179) must be read off; the diagonal construction satisfies them up to `PkMap_comp`/`PkMap_id` rewriting (both `@[simp]`-available in ws1's PkMap lemma set — confirm; if absent, prove `PkMap_comp` locally, 5 lines). The reflexivity obligation `R v v` for successors is `rfl`.

Then:

```lean
theorem ws11_extensional_downward (C : Coalg κ)
    (hext : StronglyExtensional C) : DownwardDetermined C :=
  fun x y h => hext _ (strEqBisim C) x y h

theorem ws11_no_upward_identity (C : Coalg κ)
    (hext : StronglyExtensional C) : ¬ UpwardLoadBearing C :=
  fun ⟨hnd, _⟩ => hnd (ws11_extensional_downward C hext)
```

Corollary K1 specializes via `ws2_bisim_eq` (which says `νPk κ` is strongly extensional in exactly this sense — confirm statement shape; else derive from `lambek` directly, one line either way). Corollary K3 is `fun x y h _ => ws11_extensional_downward C hext x y h`.

### Block 3 — the witness (K5)

```lean
def upCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ where
  X := ULift (Fin 3)
  str := fun i => match i.down with
    | 0 => ⟨∅, by simpa using lt_of_lt_of_le Cardinal.mk_emptyCollection_lt… hinf⟩
    | 1 => ⟨∅, …⟩
    | 2 => ⟨{⟨0⟩}, by simpa using one_lt_aleph0.trans_le hinf …⟩
```

Cardinality lemmas needed: `mk ↥(∅ : Set X) = 0 < κ` and `mk ↥({a} : Set X) = 1 < κ` — both from `hinf` (`Cardinal.mk_emptyCollection`, `Cardinal.mk_singleton`; `0 < ℵ₀`, `1 < ℵ₀`). Then

```lean
theorem ws11_upward_witness (hinf : ℵ₀ ≤ κ) : ∃ C : Coalg κ, UpwardLoadBearing C
```

Proof plan: `refine ⟨upCoalg hinf, ?_, ?_⟩`.
¬DownwardDetermined: instantiate `x := ⟨0⟩`, `y := ⟨1⟩`; `str` values are both `⟨∅, _⟩`, equal by `Subtype.ext rfl`; `⟨0⟩ ≠ ⟨1⟩` by `decide`-style discrimination on `ULift`/`Fin`.
JointlyDetermined: `intro x y hstr hup`; case on `x.down`, `y.down` (`fin_cases`/`interval_cases`). Six off-diagonal cases: pairs involving `⟨2⟩` are killed by `hstr` (membership of `⟨0⟩` in one side only — `Set.ext_iff` at `⟨0⟩`); the pair `(⟨0⟩,⟨1⟩)` is killed by `hup` at `⟨2⟩` (`⟨0⟩ ∈ UpView` since `⟨0⟩ ∈ str ⟨2⟩`; `⟨1⟩ ∉`). Diagonal cases are `rfl`.

Gap note 2: `Set`-membership through the `PkObj` subtype means every membership fact is `x ∈ (upCoalg hinf).str i |>.1` — write a local `@[simp]` unfolding lemma `upCoalg_str` per constructor to keep the case bash mechanical.

### Block 4 — the mechanism (K6)

```lean
theorem ws11_terminal_identifies (C : Coalg κ) {x y : C.X}
    (h : C.str x = C.str y) (f : C.X → (νPk κ).X) (hf : IsCoalgHom C f) :
    f x = f y :=
  (lambek (νPk_terminal κ)).injective (by rw [hf x, hf y, h])
```

Gap note 3: `IsCoalgHom` must match the homomorphism equation used inside `IsTerminalCoalg` (ws1:131) so the corollary below can consume the `∃!`:

```lean
theorem ws11_witness_collapsed (hinf : ℵ₀ ≤ κ) :
    ∀ f, IsCoalgHom (upCoalg hinf) f → f ⟨0⟩ = f ⟨1⟩
```

— the concrete statement that the (unique) map into the terminal carrier identifies exactly the pair only upward data separated.

### Block 5 — bundle

```lean
structure WS11IdentitySplit (κ : Cardinal.{u}) where
  no_upward_on_extensional :
    ∀ C : Coalg κ, StronglyExtensional C → ¬ UpwardLoadBearing C
  upward_witness : ℵ₀ ≤ κ → ∃ C : Coalg κ, UpwardLoadBearing C

theorem ws11_identity_split (κ) : WS11IdentitySplit κ
```

Named for what it proves (a split), not `ws11_resolved`. Add `#print axioms ws11_identity_split` to `AxiomCheck.lean` (expected `[propext, Classical.choice, Quot.sound]`; the witness half should be choice-light — record if choice-free).

## Dependencies on upstream theorems

| Import | Used for |
|---|---|
| ws1: `Coalg`, `PkObj`, `PkMap` (+ `PkMap_id/comp` if present), `Bisim`, `lambek`, `IsTerminalCoalg` | Blocks 1–4 |
| ws2: `νPk`, `νPk_terminal`, `ws2_bisim_eq` | K1 corollary, Block 4 |
| Mathlib: `Cardinal.mk_emptyCollection`, `Cardinal.mk_singleton`, `Cardinal.one_lt_aleph0` | Block 3 side conditions |

No dependency on ws3–ws10; WS11 is fully parallel to WS12–WS15.

## Risk register

1. `Bisim` field shape (gap note 1) — low; fallback is the `νPk`-only statement (Partial-in-generality, pre-registered).
2. `ULift`/universe friction on the witness — low; the coalgebra is stated at generic `κ : Cardinal.{u}` with `ULift (Fin 3) : Type u`.
3. Nothing in this workstream can force a reframe: both terminal outcomes are in the deliverable by construction.

*Selected candidates for hashing at commit: K2, K4, K5, K6 (bundle `ws11_identity_split`).*
