# WS3 triage → design (v2, corrected)

> **Change log vs v1.** This revision fixes six defects found on review:
> (1) the distributive law `λ` in §2.2 was the *collapsing* map `P_κ(η)∘μ`, which fails `lam_unit_F`; (2) `T = P_κ` has no naive union self-distributive law, so "a coherent law exists" was smuggled in as a definition; (3) `Pk_biUnion_lt` was claimed `hinf`-only but the `iSup` step needs **regularity**; (4) `alg_pentagon` "for free" inherited the §2.2 defect; (5) `reflects_part` and `nontrivial` did not hold for the chosen `λ`; (6) the `AdequateBialgebra` signature used `lam ‹_›` with a `Prop` hypothesis that won't resolve, and `nontrivial` was too weak to discharge T1.
>
> The corrected design **changes `T`** away from `P_κ`-with-a-self-law and instead builds the composition operation *directly from the terminal-coalgebra universal property* (a structural, law-free route), keeping F4-over-a-law only as an explicitly-gated alternative. This makes the honest F5 outcome visible rather than hidden.

## Part 1 — Paper-decidable triage

Triage questions T1–T5 are unchanged in intent (see below), but the verdicts change because the v1 "primary construction" (F1 union-law) does **not** in fact pass T3: it imports "a coherent semilattice-over-powerset law exists," which is a genuine external mathematical black box, not a Mathlib lemma.

- **T1 — Vacuity-proof?** False for `T = Id`?
- **T2 — Upstream-safe?** Leaves WS1/WS2 discharged results intact *by construction*?
- **T3 — Self-contained proof surface?** Only WS1/WS2 API + Mathlib, no imported "law exists" axiom?
- **T4 — Failure is informative?** Failure yields a sharp named outcome, not a silent `sorry`?
- **T5 — Discharges the charter obligation?** Success entails a real, observation-coherent composition on `νP_κ`?

### Revised triage table

| | T1 | T2 | T3 | T4 | T5 | Verdict |
|---|---|---|---|---|---|---|
| **F1** law-first (union self-law on `P_κ`) | Partial | Yes | **No**¹ | Yes | Partial | **rejected as primary** (imports law existence) |
| **F2** lifting | Partial | Yes | **No**¹ | Yes | Partial | same defect as F1 |
| **F3** existence-only | **No** | Yes | Yes | No | **No** | rejected (vacuous) |
| **F4′** adequate, **structural** `alg` | **Yes** | **Yes** | **Yes**² | **Yes** | **Yes** | **deliverable target** |
| **F5** gating verdict | n/a | Yes | Yes | Yes | n/a | **run first** (scaffold) |
| **F6** carrier-changing | Yes | No | Partial | Yes | Yes | fallback only |

¹ **Key correction.** A distributive law `P_κ P_κ ⇒ P_κ P_κ` making `(P_κ, μ)` distribute over `(P_κ, μ)` is not given by union-flattening; the collapsing map `P_κ(η)∘μ` fails the `F`-unit axiom, and no closed-form union law is a Mathlib fact. Asserting one is an imported black box → **T3 = No**. F1/F2 are therefore *not* self-contained and cannot be the substrate.

² F4′ is self-contained because `alg` is now defined by the **terminal universal property directly** (§2.3), consuming only `νPk_terminal` + `hom_unique` + `endo_eq_id`, with **no** distributive-law layer. The monad structure on `T` is still needed for the *statement* of `algUnit`/`algJoin`, but not for the *existence* of `alg`.

### Collapsed decision

- **Scaffold / gate: F5.** Run first; upstream-safe, self-contained; retires structural risk before construction.
- **Deliverable: F4′ — adequate bialgebra with a *structurally-defined* `alg`.** The composition operator is the unique coalgebra morphism out of a lifted coalgebra whose one-step structure is written **without** a distributive law, using only `PkMap` and `dest`/`corec`. The law-based F1 route is demoted to an *optional* alternate justification, gated behind F5, and only attempted if one wants the extra bialgebraic packaging.
- **Fallback: F6**, entered if F5 returns `impossible` for the structural `alg` itself.

**Selected candidate: F4′ (adequate bialgebra over a structural `alg`), gated by F5. No self-distributive-law obligation on the critical path.**

---

## Part 2 — Full mathematical design (corrected)

### 2.0 Imported upstream theorems

Unchanged from v1: `Coalg κ`, `PkObj κ X`, `PkMap κ f` with `PkMap_id/_comp/_val`; `IsTerminalCoalg`, `hom_unique`, `endo_eq_id`; `νPk κ`, `νPk_terminal`, `lambek` (so `dest := (νPk κ).str` bijective, `corec := Cofix.corec`); `Bisim`, `ws2_bisim_eq`, `ws2_coinduction`, `bisim_comp` (needs `hinf`), `ws2_bisim_behavioural`; `mk_singleton_lt`, `mk_empty_lt`, `omegaCoalg`, `emptyCoalg`, `omega_selfsingleton`, `ws2_nondegenerate`; `qpfPk : QPF (PkObj κ)`.

No external mathematical import beyond these + Mathlib's three standard axioms.

### 2.1 Choice of `T`, and the cardinality lemma (corrected hypotheses)

**What `PkObj` is.** Fix the reading explicitly: `PkObj κ X := {s : Set X // Cardinal.mk s < κ}`, the **bounded-powerset** functor, *not* a quotient. "A part contributes once" and "unordered" are then facts about the underlying `Set`, honestly recorded as `Set`-level lemmas, **not** claimed as monad idempotency. We therefore do **not** advertise `T` as an idempotent/semilattice monad; it is the bounded-powerset monad, which is all the construction actually uses.

```lean
instance instMonadPkObj (hinf : ℵ₀ ≤ κ) : Monad (PkObj κ) where
  pure x   := ⟨{x}, mk_singleton_lt hinf x⟩
  bind s f := ⟨⋃ x ∈ s.1, (f x).1, Pk_biUnion_lt hinf s f⟩
```

**Corrected cardinality lemma — regularity is required.**

```lean
theorem Pk_biUnion_lt (hreg : κ.IsRegular) {X : Type u}
    (s : PkObj κ X) (f : X → PkObj κ X) :
    Cardinal.mk (↥(⋃ x ∈ s.1, (f x).1)) < κ
```

Proof: `mk_biUnion_le` gives `mk (⋃) ≤ mk s.1 * ⨆_{x ∈ s.1} mk (f x).1`. Here `mk s.1 < κ` and each `mk (f x).1 < κ`. The supremum is indexed by `s.1`, a set of size `< κ`. For a **regular** `κ`, a `<κ`-indexed supremum of cardinals each `< κ` is `< κ` — this is exactly `Cardinal.iSup_lt_of_isRegular` / cofinality (`Ordinal.cof`), and it **fails** for singular `κ` (e.g. `κ = ℵ_ω`, index `ℵ₀`, values `ℵ_n`, sup `= ℵ_ω`). Then `Cardinal.mul_lt_of_lt hreg.2.1` (or `mul_lt_of_lt hinf`) closes the product.

> **Load-bearing hypothesis, corrected.** v1 claimed this was `hinf`-only, mirroring WS2. That was wrong: WS2's `PkRel_comp_le` bounds a *pairwise* composition (a product of two `<κ` cardinals, `mul_lt_of_lt`), which needs only `hinf`. `bind` bounds an **arbitrary `<κ`-indexed union**, whose sup step needs cofinality, i.e. **regularity**. So `_hreg` is consumed here and must be a real hypothesis, not a fidelity ornament. `hinf` remains needed for the singleton/product facts; both are used.

`hinf` is derivable from `hreg` (`hreg.aleph0_le`) once `κ` is infinite; we keep both names for readability and pass `hreg` on the critical path.

### 2.2 Composition without a distributive law (the corrected core)

We do **not** build `λ : P_κ P_κ ⇒ P_κ P_κ`. The v1 candidate `PkMap pure ∘ join` is the collapsing map and fails `lam_unit_F` (`lam (PkMap pure t) = PkMap pure t ≠ pure t` unless `t` is a singleton), and no union self-law is a Mathlib fact — so this whole layer is removed from the critical path.

Instead, define the one-step structure of the *lifted* coalgebra on `T U = P_κ U` **directly**, using only `dest` and `PkMap`. The composition of a `<κ`-family of already-constructed objects should observe, in one step, the **union of the parts' observations**:

```lean
/-- One-step structure of the coalgebra whose corecursion is `alg`.
    A whole `t : P_κ U` unfolds to the bounded union of its parts' unfoldings. -/
def liftStr (hreg : κ.IsRegular) (U : Type u) (d : U → PkObj κ U) :
    PkObj κ U → PkObj κ (PkObj κ U) :=
  fun t => PkMap κ (fun _ => t) (bigUnionStr hreg d t)
```

where `bigUnionStr` is the honest "union of one-step observations,"

```lean
def bigUnionStr (hreg : κ.IsRegular) {U} (d : U → PkObj κ U)
    (t : PkObj κ U) : PkObj κ U :=
  ⟨⋃ x ∈ t.1, (d x).1, Pk_biUnion_lt hreg t d⟩   -- = join (PkMap κ d t)
```

The single algebraic identity we rely on is **`bigUnionStr = join ∘ PkMap dest`**, i.e. plain union-associativity of `PkMap`/`join`, which *is* a Mathlib-tractable fact (`PkMap_comp`, `Set.biUnion` lemmas). There is no unit/multiplication coherence pentagon to import: the correctness of `alg` comes entirely from terminal uniqueness in §2.3, not from monad-of-`T` distributing over `F`.

> This is the crux of the fix: the burden moves from "prove five distributive-law axioms that are actually false for `P_κ`" to "prove one union-associativity equation that is true and `simp`-tractable." The composition semantics ("a whole observes exactly the union of its parts' one-step observations") is fixed *before* any proof and is manifestly non-collapsing.

### 2.3 The induced composition operator `alg` on `νP_κ`

`alg` is the **unique coalgebra morphism** from the lifted coalgebra `⟨P_κ (νPk κ).X, liftStr … dest⟩` into the terminal `νPk κ`, given by `νPk_terminal`:

```lean
def liftedCoalg (hreg : κ.IsRegular) : Coalg κ :=
  ⟨PkObj κ (νPk κ).X, fun t => join (PkMap κ (νPk κ).str t)⟩
  -- structure = bigUnionStr hreg dest, i.e. "union of parts' observations",
  -- retyped through the νPk carrier by corecursion below.

def alg (hreg : κ.IsRegular) : PkObj κ (νPk κ).X → (νPk κ).X :=
  (νPk_terminal κ (liftedCoalg hreg)).choose
```

Its defining square (`choose_spec`) is the honest pentagon — now with the corrected, law-free RHS:

```lean
theorem alg_pentagon (hreg : κ.IsRegular) (t : PkObj κ (νPk κ).X) :
    (νPk κ).str (alg hreg t)
      = PkMap κ (alg hreg) (join (PkMap κ (νPk κ).str t))
```

Read: *the one-step observation of a composite is `alg` applied to the union of the parts' one-step observations.* Uniqueness of `alg` is `hom_unique`; existence used terminality, not a mere fixed point — the crux reuse of WS1/WS2 survives intact.

**Unit and multiplication laws** (statements need the `Monad` instance; proofs need only terminal uniqueness + union-associativity):

```lean
theorem alg_unit (hreg) (x : (νPk κ).X) : alg hreg (pure x) = x
-- pure x = {x}; join (PkMap dest {x}) = dest x; so t ↦ alg(pure x) and id
-- are both coalgebra morphisms νPk → νPk agreeing on structure ⇒ endo_eq_id.

theorem alg_join (hreg) (tt : PkObj κ (PkObj κ (νPk κ).X)) :
    alg hreg (join tt) = alg hreg (PkMap κ (alg hreg) tt)
-- both sides are coalgebra morphisms (liftedCoalg∘join) → νPk; agree by
-- biUnion-associativity of the structure map ⇒ hom_unique.
```

`alg_unit` now holds unconditionally (no dependence on a false `lam_unit_F`), because `pure x = {x}` and the union of a single part's observation is that observation.

### 2.4 Adequacy riders (corrected so they actually hold)

**(A) Part-reflection — now true by construction.**

```lean
theorem reflects_part (hreg) (t : PkObj κ (νPk κ).X) {x} (hx : x ∈ t.1) :
    ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg hreg t)).1
```

Proof: `alg_pentagon` gives `dest (alg t) = PkMap alg (join (PkMap dest t))`. The set `join (PkMap dest t) = ⋃_{y ∈ t} (dest y).1` contains `(dest x).1` as a sub-union since `x ∈ t.1`. Applying `PkMap alg` and using `alg_unit` on the already-`dest`-form members yields `(dest x).1 ⊆ (dest (alg t)).1`. This works **precisely because** `liftStr` is the union-of-observations map; it would have *failed* for v1's collapsing `λ`, which is why (A) is now consistent with §2.2.

**(B) `Ω` fixed point.**

```lean
theorem omega_fix (hreg) (ω : (νPk κ).X) (hω : ((νPk κ).str ω).1 = {ω}) :
    alg hreg (pure ω) = ω
```

Immediate from `alg_unit`. Content: `Ω` from `omega_selfsingleton` is such an `ω`, so self-composition fixes the groundless inhabitant.

**(C) Non-triviality — strengthened to actually discharge T1.**

v1's `∃ t x, alg t ≠ x ∧ x ∈ t.1` was too weak (satisfiable by many non-`Id` maps and by degenerate ones). Replace it with a statement that genuinely excludes the `T = Id` shadow: for the two distinct points `a ≠ b` from `ws2_nondegenerate`, the composite `{a,b}` strictly dominates **both** parts in observable structure.

```lean
theorem alg_nontrivial (hreg) :
    ∃ (a b : (νPk κ).X), a ≠ b ∧
      let t : PkObj κ (νPk κ).X := ⟨{a, b}, mk_pair_lt hreg a b⟩
      ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
      ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
      alg hreg t ≠ a ∧ alg hreg t ≠ b
```

Proof: `a, b, (a≠b)` from `ws2_nondegenerate`. Both `⊆` are `reflects_part`. For `alg t ≠ a`: if `alg t = a` then by `reflects_part` on `b` we'd get `(dest b).1 ⊆ (dest a).1`; combined with `a ≠ b` and behavioural distinctness (`ws2_bisim_behavioural` / `ws2_bisim_eq`: distinct points differ in observation), pick a witness in `(dest b).1 \ (dest a).1` when it exists, else use symmetry — in the degenerate sub-case where `dest a = dest b` as sets, `a = b` by coinduction (`ws2_coinduction`), contradiction. Symmetrically `alg t ≠ b`. This exhibits a composite that is a *new* object dominating its parts, which is exactly the structure an `Id`-shadow cannot produce, discharging **T1** properly.

> If `ws2_bisim_behavioural` does not directly yield a distinguishing member (i.e. distinctness is not one-step observable), then `alg_nontrivial` in this sharp form can fail. That is the **honest F5 checkpoint** for the structural route (see §2.6) — and unlike v1, it is a *provable* union-of-observations question, not a hidden law-existence assumption.

### 2.5 The assembled deliverable (corrected signature)

`hinf`/`hreg` are threaded as explicit fields/parameters — no `‹_›` on a `Prop` hypothesis.

```lean
structure AdequateBialgebra (κ : Cardinal.{u}) (hreg : κ.IsRegular) where
  alg           : PkObj κ (νPk κ).X → (νPk κ).X
  pentagon      : ∀ t, (νPk κ).str (alg t)
                        = PkMap κ alg (join (PkMap κ (νPk κ).str t))
  algUnit       : ∀ x, alg (pure (self := instMonadPkObj hreg.aleph0_le) x) = x
  algJoin       : ∀ tt, alg (join tt) = alg (PkMap κ alg tt)
  reflects_part : ∀ t {x}, x ∈ t.1 → ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg t)).1
  omega_fix     : ∀ ω, ((νPk κ).str ω).1 = {ω} → alg (pure ω) = ω
  nontrivial    : ∃ a b, a ≠ b ∧
                    (let t : PkObj κ (νPk κ).X := ⟨{a,b}, mk_pair_lt hreg a b⟩;
                     ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     alg t ≠ a ∧ alg t ≠ b)

theorem ws3_adequate_bialgebra (hreg : κ.IsRegular) :
    Nonempty (AdequateBialgebra κ hreg)
```

Regularity is now a **used** hypothesis (§2.1, §2.4), so it appears in the type and is genuinely consumed — no "carried but unused" marker. `hinf` is obtained as `hreg.aleph0_le` where the monad instance needs it.

### 2.6 Dependency graph and build order (corrected)

```
Mathlib (QPF, Cofix, Cardinal.iSup_lt_of_isRegular, mul_lt_of_lt, mk_biUnion_le)
   │
ws1: PkMap(_id/_comp/_val), IsTerminalCoalg, hom_unique, endo_eq_id,
     νPk_terminal, lambek, omegaCoalg, omega_selfsingleton
   │
ws2: ws2_nondegenerate, ws2_bisim_eq, ws2_bisim_behavioural, ws2_coinduction,
     mk_singleton_lt, mk_empty_lt   (+ new: mk_pair_lt from mk_singleton_lt)
   │
   ├─ [NEW] Pk_biUnion_lt  ← iSup_lt_of_isRegular + mul_lt_of_lt   (needs hreg)   §2.1
   ├─ [NEW] instMonadPkObj ← Pk_biUnion_lt                                        §2.1
   ├─ [NEW] bigUnionStr / liftedCoalg  ← PkMap, Pk_biUnion_lt                     §2.2
   ├─ [NEW] biUnion-assoc lemma  ← PkMap_comp, Set.biUnion_*   (the ONE identity) §2.2
   ├─ [NEW] alg  ← νPk_terminal (∃! witness)                                      §2.3
   ├─ [NEW] alg_pentagon  ← choose_spec                                           §2.3
   ├─ [NEW] alg_unit, alg_join  ← endo_eq_id / hom_unique + biUnion-assoc         §2.3
   ├─ [NEW] reflects_part, omega_fix  ← alg_pentagon, alg_unit                    §2.4
   ├─ [NEW] alg_nontrivial  ← ws2_nondegenerate, reflects_part, ws2_coinduction   §2.4
   └─ ws3_adequate_bialgebra  (assembles all)                                     §2.5
```

**Critical-path risk (named, corrected).** The critical path no longer contains five distributive-law axioms (which were false for `P_κ`). It contains exactly two decidable checkpoints:

1. **`Pk_biUnion_lt` under regularity** (§2.1). If one instead insists on `hinf`-only, this is *provably impossible* for singular `κ` — a sharp F5 `impossible` for the singular case, resolved by requiring `hreg`. This is not a defect; it is the correct hypothesis accounting.
2. **`alg_nontrivial` sharp form** (§2.4C). If distinct terminal points are not one-step-observably distinct, the strong non-triviality can fail; this is a *provable* statement about `dest`, so failure produces a named obstruction (F5 `impossible` for the structural route), triggering **F6** (annotated functor `PkAnn`) as a separate, labeled workstream.

**What would count as this obligation failing:**
- *Cardinality* — `Pk_biUnion_lt` unprovable ⇒ only for singular `κ`; require regularity (done). No black box.
- *Degenerate composition* — `alg_nontrivial` unprovable ⇒ composition collapses to an `Id`-shadow; F4′ fails at the adequacy layer, report impossibility, go to F6.
- *Coherence forcing `F`/carrier change* — **cannot arise**: there is no distributive-law coherence on this route. `alg` is defined *into* the existing `νPk` by terminality, `T = F = P_κ` is fixed before `alg` is built, and the only algebraic obligation is union-associativity, which is a Mathlib identity. Upstream safety (T2) is structural.

> **Net effect of the corrections.** v1 routed all risk to a five-axiom distributive-law checkpoint that was actually *false* for `P_κ` (so the design would have silently required the smuggled law, or tripped its own gate without saying so). v2 removes that layer entirely, replaces it with one true union-associativity identity plus an honest regularity hypothesis, and makes the only remaining substantive risk (`alg_nontrivial`) a provable observation-level statement. The deliverable is now genuinely self-contained (T3) and its adequacy riders are mutually consistent.
