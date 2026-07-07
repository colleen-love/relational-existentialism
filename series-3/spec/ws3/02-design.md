# WS3 triage → design

## Part 1 — Paper-decidable triage

Each candidate is scored on questions answerable **without doing the proof**, purely from the structure of what is being asked and what WS1/WS2 already deliver.

**Triage questions (each Yes/No/Partial, decidable by inspection):**

- **T1 — Vacuity-proof?** Is the statement false for `T = Id` (i.e. does it exclude the trivial witness)? A "No" means the framing can be satisfied without saying anything.
- **T2 — Upstream-safe?** Does success leave WS1/WS2's discharged results (terminality of `νP_κ`, bisim=identity, weak-pullback) intact, *by construction* rather than by luck?
- **T3 — Self-contained proof surface?** Can the obligation be discharged using only imported WS1/WS2 API + Mathlib, with no new external mathematical black box (no imported "law exists" axiom)?
- **T4 — Failure is informative?** If it fails, does the failure produce a *sharp* named outcome (impossibility proof / explicit obstruction), not a silent `sorry`?
- **T5 — Actually discharges the charter obligation?** Does success entail bidirectional constitution (a real `T`-algebra coherent with observation), as opposed to a shadow of it?

A framing that scores **No on T1 or T5** cannot be the *deliverable* (it is at best scaffolding). A framing that scores **No on T2** is disqualified as a primary route (it can break upstream). **T3** ranks build-feasibility. **T4** is required of whatever route we commit to, because the charter counts impossibility as success only if it is *proved*, not encountered.

### Triage table

| | T1 vacuity-proof | T2 upstream-safe | T3 self-contained | T4 informative failure | T5 discharges obligation | Verdict |
|---|---|---|---|---|---|---|
| **F1** law-first | Partial¹ | **Yes** | **Yes** | **Yes** | Partial² | primary-**construction** |
| **F2** lifting | Partial¹ | **Yes** | **Yes** | **Yes** | Partial² | backup surface for F1 |
| **F3** existence-only | **No** | Yes | Yes | No³ | **No** | rejected (vacuous) |
| **F4** adequate | **Yes** | **Yes** | **Yes**⁴ | **Yes** | **Yes** | **deliverable target** |
| **F5** gating verdict | n/a⁵ | **Yes (retires)** | **Yes** | **Yes** | n/a⁵ | **run first** (scaffold) |
| **F6** carrier-changing | Yes | **No**⁶ | Partial⁷ | Yes | Yes | fallback only |

¹ Excludes `T=Id` only once a non-trivial `T` is fixed; the *schema* admits `Id`.
² Proves a law/algebra exists but not that the algebra is genuine composition (adequacy) — that is exactly F4's extra content.
³ `T=Id` witness means "failure" never arises; uninformative.
⁴ Self-contained **provided** the underlying law/algebra comes from F1; F4 = F1 + adequacy riders, no new black box.
⁵ F5 is a decision procedure, not a deliverable; T1/T5 don't apply.
⁶ Changing `F` can fail to preserve the terminal coalgebra → breaks WS1/WS2 unless a forgetful-preservation theorem is separately earned.
⁷ Needs a new functor `PkAnn` and its own QPF/terminality story — extra imported surface.

### Collapsed decision

The triage forces a **two-layer** answer, not a single framing:

- **Scaffold / gate: F5.** Run the verdict first. It is upstream-safe, self-contained, and its whole purpose is to retire the structural risk ("does building WS3 break WS1/WS2?") *before* construction. Cost: proves nothing constructive alone — hence a gate, not the deliverable.
- **Deliverable: F4, built on F1's law.** F4 is the only route that is simultaneously vacuity-proof (T1), upstream-safe (T2), self-contained (T3), informative on failure (T4), and actually discharges the obligation (T5). Its law/algebra layer *is* F1; F1 is therefore absorbed as F4's substrate, with **F2** held as an alternate proof surface for the law axioms.
- **Fallback: F6**, entered only if F5 returns `impossible` for every candidate `T`.

**Selected candidate: F4 (adequate bialgebra) over an F1 distributive law, gated by F5.**

The rest is the full design of that object.

---

## Part 2 — Full mathematical design

### 2.0 Imported upstream theorems (the BR this design consumes)

From `ws1.lean` / `ws2.lean`, taken as established and axiom-free:

- `Coalg κ`, `PkObj κ X`, `PkMap κ f`, with `PkMap_id`, `PkMap_comp`, `PkMap_val`.
- `IsTerminalCoalg`, `hom_unique`, `endo_eq_id`.
- `νPk κ` and `νPk_terminal κ : IsTerminalCoalg (νPk κ)`.
- `lambek : Function.Bijective (νPk κ).str` — so `dest := (νPk κ).str` is invertible; write `corec := Cofix.corec`.
- `Bisim`, `ws2_bisim_eq`, `diagBisim`, `ws2_coinduction`, `bisim_comp` (⊇, needs `hinf`), `ws2_bisim_behavioural`.
- `mk_singleton_lt`, `mk_empty_lt`, `omegaCoalg`, `emptyCoalg`, and the `Ω`-fact `omega_selfsingleton`.
- `qpfPk : QPF (PkObj κ)` with the `Cofix` universal-property API.

The design adds **no** external mathematical import beyond these + Mathlib's standard three axioms.

### 2.1 Choice of `T` (the composition monad)

The composition of "parts into wholes" over a groundless carrier must be:

- **unordered** (a whole is determined by its parts as a *set*, not a list),
- **idempotent** (a part contributes once),
- **`<κ`-bounded** (a whole has fewer than `κ` immediate parts, matching `P_κ`),
- with a **unit** (the singleton "this object as a one-part whole").

This is exactly the **`<κ`-bounded semilattice monad**, whose functor is *the same* `PkObj κ`. So set

```
T := PkObj κ      -- as a monad: pure x = {x}, join = ⋃ (bounded union)
```

**Why this is the right move.** `T = F` here is not a coincidence to be embarrassed by; it is the content of "relations are objects" (Commitment 2): composition and observation act on the same kind of thing. It also collapses the adequacy question into something checkable, because `T`-union and `P_κ`-branching are the *same* operation, related by a law that is essentially union-flattening.

Monad structure on `PkObj κ`:
```lean
instance : Monad (PkObj κ) where
  pure x := ⟨{x}, mk_singleton_lt hinf x⟩
  bind s f := ⟨⋃ x ∈ s.1, (f x).1, /- <κ: <κ-union of <κ sets, needs hinf -/⟩
```
The bind-bound lemma (`<κ`-indexed union of `<κ` sets is `<κ`) needs **only `hinf`** — it is the `Cardinal.mul_lt_of_lt`/`iSup` argument WS2 already used for `PkRel_comp_le`; regularity is **not** required, matching WS2's hypothesis-accounting correction. This is the one genuinely new upstream-style lemma:

```lean
theorem Pk_biUnion_lt (hinf : ℵ₀ ≤ κ) {X : Type u} (s : PkObj κ X)
    (f : X → PkObj κ X) :
    Cardinal.mk (↥(⋃ x ∈ s.1, (f x).1)) < κ
```
Proof: `mk_biUnion_le` bounds the union by `mk s.1 * ⨆ mk (f x).1`; both factors `< κ`; `Cardinal.mul_lt_of_lt hinf` (and `iSup_lt`, using that the index set is `<κ`) closes it. **This is where `hinf` is load-bearing and regularity is not** — flag it exactly as WS2 flagged the analogous point.

### 2.2 The distributive law `λ : T P_κ ⇒ P_κ T` (F1 layer)

With `T = F = P_κ`, a law `λ_X : P_κ(P_κ X) → P_κ(P_κ X)` is required. The correct, coherence-satisfying choice is the **identity-on-the-double-powerset** law induced by union-commutation — concretely the transpose that turns "a `<κ`-set of `<κ`-sets, read as (composition-of) observations" into "observations of composites":

```
λ_X (𝒮) = { t ∈ P_κ X : t is a transversal/selection realized across 𝒮 }
```
The clean, provably-coherent instantiation is the **"big union then re-singleton" law** matching the semilattice-over-powerset canonical law (Manes–Mulry / Garner): distribute `T` past `P_κ` by
```
λ_X (𝒮) = PkMap κ (pure) (join 𝒮)      -- flatten, then wrap
```
i.e. `λ = P_κ(η^T) ∘ (μ^{P_κ} read as join)`. This has closed-form `PkMap`/`join` expressions, so all four axioms reduce to `PkMap_comp` / `PkMap_id` / union-associativity — `simp`-tractable.

```lean
def lam (hinf : ℵ₀ ≤ κ) {X : Type u} (𝒮 : PkObj κ (PkObj κ X)) : PkObj κ (PkObj κ X) :=
  PkMap κ (pure (self := instMonadPkObj hinf)) (join 𝒮)
```
Law axioms to prove (all as equalities of `PkObj κ (...)`):
```lean
theorem lam_natural   (hinf) {X Y} (f : X → Y) (𝒮) :
  lam hinf (PkMap κ (PkMap κ f) 𝒮) = PkMap κ (PkMap κ f) (lam hinf 𝒮)
theorem lam_unit_T    (hinf) {X} (s : PkObj κ X) : lam hinf (pure s) = PkMap κ pure s
theorem lam_unit_F    (hinf) {X} (t : PkObj κ X) : lam hinf (PkMap κ pure t) = pure t
theorem lam_mult_T    (hinf) {X} (𝒮𝒮) : lam hinf (join 𝒮𝒮) = PkMap κ join (lam hinf (PkMap κ (lam hinf) 𝒮𝒮))
theorem lam_mult_F    (hinf) {X} (𝒮𝒮) : lam hinf (PkMap κ join 𝒮𝒮) = join (PkMap κ (lam hinf) (lam hinf 𝒮𝒮))
```
**Failure detector built in:** if any of these five is *not* a Lean identity, F5's `impossible` branch fires — we exhibit the two witnesses making `lam` ill-defined, giving an **impossibility-proved** outcome for this `T`. This is the F5 gate discharged *inside* the construction.

### 2.3 The induced `T`-algebra on `νP_κ` (Turi–Plotkin, done concretely)

Given `λ`, the canonical `T`-algebra on the final coalgebra is the unique coalgebra morphism from the *lifted* coalgebra into `νP_κ`. Concretely: `T U = P_κ U` carries the coalgebra structure `λ_U ∘ T(dest) : P_κ U → P_κ(P_κ U) → P_κ(P_κ U)`, and

```lean
def alg (hinf : ℵ₀ ≤ κ) : (PkObj κ) (νPk κ).X → (νPk κ).X :=
  (νPk_terminal κ ⟨PkObj κ (νPk κ).X, fun s => lam hinf (PkMap κ (νPk κ).str s)⟩).choose
```
Its defining property (the coalgebra-morphism square) *is* the pentagon:
```lean
theorem alg_pentagon (hinf : ℵ₀ ≤ κ) (t : PkObj κ (νPk κ).X) :
    (νPk κ).str (alg hinf t)
      = PkMap κ (alg hinf) (lam hinf (PkMap κ (νPk κ).str t))
```
— delivered *for free* by the `∃!`-witness of `νPk_terminal`. Uniqueness of `alg` is `hom_unique`. **This is the crux reuse of WS1/WS2: `alg` exists and is unique precisely because we secured *terminality*, not a mere fixed point.**

The `T`-algebra laws (`join`/`pure` compatibility) follow from the law axioms + terminal uniqueness, each via `endo_eq_id`/`hom_unique` (two coalgebra morphisms `T U → U` agreeing ⇒ equal):
```lean
theorem alg_unit (hinf) (x : (νPk κ).X) : alg hinf (pure x) = x        -- via lam_unit_F + endo_eq_id
theorem alg_join (hinf) (tt : PkObj κ (PkObj κ (νPk κ).X)) :
    alg hinf (join tt) = alg hinf (PkMap κ (alg hinf) tt)              -- via lam_mult_* + hom_unique
```

### 2.4 The adequacy riders (F4 content — what makes it non-vacuous)

These are the fields that distinguish a *real* bialgebra from the `T=Id` shadow, and each is now provable because `alg` has the explicit pentagon form.

**(A) Part-reflection.** Composition never loses a part's observable structure:
```lean
theorem reflects_part (hinf) (t : PkObj κ (νPk κ).X) {x} (hx : x ∈ t.1) :
    (νPk κ).str x |>.1 ⊆ ((νPk κ).str (alg hinf t)).1
```
Proof: expand `alg_pentagon`; `lam hinf (PkMap κ dest t)` contains `dest x` as one of the flattened-then-re-wrapped members; `PkMap κ alg` sends it to `dest x` under `alg_unit`. A membership chase on `PkMap_val` + `Set.subset` — no new machinery.

**(B) `Ω` fixed point.** The canonical self-membered object is a fixed point of self-composition:
```lean
theorem omega_fix (hinf) (ω : (νPk κ).X) (hω : ((νPk κ).str ω).1 = {ω}) :
    alg hinf (pure ω) = ω
```
Immediate from `alg_unit`; the content is that `Ω` (from `omega_selfsingleton`) *is* such an `ω`, so composition fixes it — the bialgebra respects the groundless inhabitant.

**(C) Non-triviality (T1 discharge).** `alg` is not constant / not `Id`-shadow:
```lean
theorem alg_nontrivial (hinf) :
    ∃ (t : PkObj κ (νPk κ).X) (x : (νPk κ).X), alg hinf t ≠ x ∧ x ∈ t.1
```
Witness: take the two distinct points `a ≠ b` from `ws2_nondegenerate`; the pair `{a,b}` composes to an object whose structure is `dest a ∪ dest b`, distinct from both `a` and `b` by `reflects_part` + non-degeneracy. This is the field that makes `T=Id` fail the structure, i.e. what T1 demanded.

### 2.5 The assembled deliverable

```lean
structure AdequateBialgebra (κ : Cardinal.{u}) where
  alg           : PkObj κ (νPk κ).X → (νPk κ).X
  pentagon      : ∀ t, (νPk κ).str (alg t) = PkMap κ alg (lam ‹_› (PkMap κ (νPk κ).str t))
  algUnit       : ∀ x, alg (pure x) = x
  algJoin       : ∀ tt, alg (join tt) = alg (PkMap κ alg tt)
  reflects_part : ∀ t {x}, x ∈ t.1 → ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg t)).1
  omega_fix     : ∀ ω, ((νPk κ).str ω).1 = {ω} → alg (pure ω) = ω
  nontrivial    : ∃ t x, alg t ≠ x ∧ x ∈ t.1

theorem ws3_adequate_bialgebra (hinf : ℵ₀ ≤ κ) (_hreg : κ.IsRegular) :
    Nonempty (AdequateBialgebra κ)
```
Regularity `_hreg` carried for charter fidelity, marked unused (per §2.1: only `hinf` is consumed), exactly mirroring `ws2_characterization`.

### 2.6 Dependency graph and build order

```
Mathlib (QPF, Cofix, Cardinal.mul_lt_of_lt, mk_biUnion_le)
   │
ws1: PkMap(_id/_comp), IsTerminalCoalg, hom_unique, endo_eq_id,
     νPk_terminal, lambek, omegaCoalg, omega_selfsingleton
   │
ws2: ws2_nondegenerate, ws2_bisim_eq, mk_singleton/empty_lt
   │
   ├─ [NEW] instMonadPkObj  ←  Pk_biUnion_lt (hinf only)          §2.1
   ├─ [NEW] lam + 5 law axioms  ←  PkMap_comp, join-assoc         §2.2   ⟵ F5 gate lives here
   ├─ [NEW] alg  ←  νPk_terminal (∃! witness)                     §2.3
   ├─ [NEW] alg_unit, alg_join  ←  lam_unit_*/mult_*, hom_unique   §2.3
   ├─ [NEW] reflects_part, omega_fix  ←  alg_pentagon, alg_unit    §2.4
   ├─ [NEW] alg_nontrivial  ←  ws2_nondegenerate, reflects_part    §2.4
   └─ ws3_adequate_bialgebra  (assembles all)                      §2.5
```

**Critical-path risk (named, per T4).** The single point where the whole design can fail is the five law axioms of §2.2. If they hold → everything downstream is terminal-uniqueness bookkeeping and discharges. If one fails → we do **not** patch it silently: we record the failing witness as `ws3_no_law : Nonempty (DistLaw (PkObj κ) κ) → False`, which is the F5 `impossible` verdict and, per the charter, a **success** (impossibility proved), triggering the F6 fallback (annotated functor `PkAnn`) as a separate, clearly-labeled workstream — not a relabeling of this obligation.

**What would count as this obligation failing:**
- *No law* — a §2.2 axiom is not an identity ⇒ impossibility-proved for `T = P_κ` (report, then F6).
- *Degenerate algebra* — `alg` forced constant or `nontrivial` unprovable ⇒ composition collapses; F4 fails at the adequacy layer even though F1/F3 would "succeed" (the reason F3 was rejected in triage).
- *Coherence forces `F`/carrier to change* — cannot arise on this route, because `T = F = P_κ` is fixed *before* `alg` is built and `alg` is defined *into* the existing `νPk`; upstream safety (T2) is structural, not incidental. Any change would surface as a §2.2 axiom failure, i.e. the first bullet — which is why the design routes all risk to one decidable checkpoint.
