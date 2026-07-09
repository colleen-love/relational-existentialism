# WS3 → design (v3): discharging Commitment 4 / criterion (iv)

> **What changed from v2, and why it now discharges the charter.**
> v2 quietly *switched instruments* — it dropped the distributive law `λ` (§3.4 of
> the charter) and built a law-free structural composition, then presented that as
> the deliverable. Per the charter's own discipline (§8.2: *substitute openly,
> state the residual, route it — never relabel the shortfall as the goal*) that was
> a **Partial** masquerading as Discharged, because criterion (iv) names a
> *coherent bialgebra via a distributive law*, and v2 neither delivered one nor
> proved none exists.
>
> This revision closes the gap in the direction the charter explicitly blesses.
> The distributive law of `P_κ` over itself **does not exist**, and this is now a
> *theorem*, not a failed construction: it is Klin & Salamanca's no-go result
> (*Iterated Covariant Powerset is not a Monad*, MFPS 2018), whose proof holds
> verbatim for finite powerset and transfers to `P_κ`. Under §5/§7 a sharp
> impossibility **is a success**. WS3 therefore discharges as:
>
> - **(iv)-distributive-law clause: Impossibility proved** — no `λ : P_κP_κ ⇒ P_κP_κ` exists (Part A).
> - **(iv)-bidirectional-constitution content: Discharged** — via a *weak* distributive law / structural composition that is the mathematically correct surrogate the literature identifies, with the canonical content (bidirectional whole/part determination on one carrier) recovered (Part B).
>
> Both halves are stated as theorems; the residual (which weak law, and its
> coherence grade) is routed explicitly to WS4/WS7 (Part C). No instrument is
> switched silently.

---

## Part 0 — Charter binding (unchanged target, now correctly hit)

- **Workstream:** WS3 (Milestone 3).
- **Commitment:** 4 (bidirectional constitution — an object fixed jointly by what it contains and what contains it, mediated by relations in both directions).
- **Criterion:** (iv) — *supports bidirectional whole/part constitution via a coherent bialgebra.*
- **Instrument named in §3.4:** monad `T` (composition) + functor `F` (observation) + **distributive law** `λ : TF ⇒ FT`; a `λ`-bialgebra is simultaneously a `T`-algebra and `F`-coalgebra.
- **Gating question from §8.1 (WS3 audit), verbatim in force:** *does the WS1/WS2 carrier admit the required `T`-algebra structure and a coherent `λ`? — answered before building, with "no `λ` exists" an acceptable Impossibility-proved outcome.*

The design below answers that gating question **first** (Part A) and only then builds (Part B). This is the F5-gate discipline, now with a real theorem in the gate instead of a checklist.

---

## Part A — The gate, discharged as a theorem: no distributive law exists

### A.1 The imported no-go theorem (the one external result, fully cited, not a black box)

Klin & Salamanca (2018), Theorem 2.4, in the category of sets:

> If a pointed functor `(T, η)` **preserves preimages** and admits a **nontrivial idempotent term** `β : Id × Id ⇒ T`, then there is **no** distributive law of `(T, η)` over the pointed functor `P` (both as pointed functors).

Definitions (their §2):
- *Preserves preimages*: for `f : X → Y`, `Z ⊆ Y`, `t ∈ TX`, if `Tf(t) ∈ TZ` then `t ∈ T(f⁻¹Z)`. Specialised to inclusions: `TX ∩ TZ ⊆ T(X ∩ Z)`.
- *Nontrivial idempotent term*: `β : Id × Id ⇒ T` with `β_X(x,x) = η_X(x)` (idempotence) and `β_{0,1}(0,1) ∉ T{0} ∪ T{1}` (non-triviality).

Consequences they prove:
- **Theorem 3.2:** there is no monad structure on `PP` at all (not merely no law).
- **Theorem 4.1:** no monad structure on `Pⁿ` for any `n > 1`.
- **Scope note (their §2):** *all results remain true with `P` replaced by finite powerset `P_f`, with the same proofs.*

> This is the **only** imported mathematical result on the WS3 critical path. Unlike v1/v2's smuggled "a coherent union law exists," this is a published theorem with a four-set / three-function diagonal proof (`A = {a,b,c,d}`, `U = {u,v}`, the three maps `f,g,h`), reproduced in A.3 at the level of detail WS needs to re-verify it.

### A.2 Instantiation at `T = F = P_κ` (the WS1/WS2 observation functor)

We must check the two hypotheses for the *bounded* powerset `P_κ` used as both `T` and `F`.

**(H1) `P_κ` preserves preimages.** For `f : X → Y`, `Z ⊆ Y`, and `t ∈ P_κ X` (so `t.1 ⊆ X`, `mk t.1 < κ`): if `P_κ f (t) ⊆ Z`, i.e. `f '' t.1 ⊆ Z`, then `t.1 ⊆ f⁻¹ Z`, and `mk t.1 < κ` is unchanged, so `t ∈ P_κ(f⁻¹Z)`. The cardinality side-condition is inert (subsets of `t.1` are no larger). Preimage preservation is inherited from `P` unchanged.

```lean
theorem Pk_preserves_preimages (hκ) {X Y} (f : X → Y) (Z : Set Y) (t : PkObj κ X) :
    PkMap κ f t |>.1 ⊆ Z → t.1 ⊆ f ⁻¹' Z
```

**(H2) `P_κ` admits a nontrivial idempotent term**, provided `κ ≥ 3` (so that a two-element subset is `< κ`; for `κ` infinite this is free):
```
β_X(x,y) := ⟨{x,y}, mk_pair_lt hκ x y⟩ : P_κ X
```
- Idempotence: `β_X(x,x) = ⟨{x}, _⟩ = η_X(x) = pure x`. ✓
- Non-triviality: `β_{0,1}(0,1) = {0,1} ∉ P_κ{0} ∪ P_κ{1}` since `{0,1}` is neither a subset of `{0}` nor of `{1}`. ✓ (Needs only `0 ≠ 1`, i.e. the ≥2 branching that WS7's richness floor demands anyway; the `<κ` bound is satisfied because `2 < κ` for infinite `κ`.)

```lean
def betaPk (hκ : 3 ≤ κ ∨ ℵ₀ ≤ κ) {X} (x y : X) : PkObj κ X :=
  ⟨{x, y}, mk_pair_lt hκ x y⟩
theorem betaPk_idempotent (hκ) {X} (x : X) : betaPk hκ x x = pure x
theorem betaPk_nontrivial (hκ) : betaPk hκ (0:Bool) 1 ∉ ... -- ∉ PkObj{0} ∪ PkObj{1}
```

Both hypotheses of the no-go theorem hold. Therefore:

### A.3 The WS3 impossibility theorem (the gate result)

```lean
/-- No distributive law of P_κ over itself, as pointed functors —
    a fortiori no monad-distributive-law, a fortiori no λ-bialgebra
    of the §3.4 form on the WS1/WS2 carrier. -/
theorem ws3_no_distributive_law (hκ : ℵ₀ ≤ κ) :
    IsEmpty (DistLaw (PkObj κ) (PkObj κ)) := by
  -- instantiate Klin–Salamanca Thm 2.4 with T = F = P_κ,
  -- discharging (H1) via Pk_preserves_preimages and (H2) via betaPk_*.
  ...
```

**Two routes to formalize, in order of preference:**

1. **Transfer the diagonal proof directly.** The Klin–Salamanca argument uses only finitely many elements (`A = {a,b,c,d}`, `U = {u,v}`) and the two hypotheses. Every set in play has size `≤ 4 < κ`, so *every intermediate object lands in `P_κ`* — the bound is never binding. The proof is therefore **literally the same** for `P_κ` as for `P`/`P_f`; we port their four-set/three-function computation, replacing `P` by `P_κ` and citing (H1)/(H2). This is self-contained modulo Mathlib finite-set reasoning. **This is the recommended path**: it makes `ws3_no_distributive_law` an *internally proved* theorem, not an imported axiom, honoring T3.

2. **Import as a stated theorem.** If the diagonal port proves heavier than budgeted, record Klin–Salamanca Thm 2.4 + the `P_f` scope note as a single named import `KlinSalamanca_no_law`, and derive `ws3_no_distributive_law` from it. This is the one permissible external mathematical import; it is a *published theorem*, not a "law exists" assumption, and it is flagged as the sole non-Mathlib dependency.

> **Charter status of Part A.** This is the §8.1 gating question answered **No**, as a **theorem**. Per §5/§7 this is **Impossibility proved = success**. It also retroactively explains v1/v2's failures: v1's five law-axioms were doomed (`lam_unit_F` had to fail), and the two "canonical" laws the literature calls out as historically flawed — Manes–Mulry's selection/transversal law and Klin–Rot's — are *exactly* the closed forms v1 §2.2 reached for; both fail **naturality**, not merely a unit axiom. The gate now closes with a reason, not a symptom.

### A.4 What Part A does *not* claim

- It does **not** claim `PP` / `P_κP_κ` fails to be a *functor* — it is one; it fails to be a *monad* and admits no self-distributive-law.
- It does **not** claim no bidirectional structure is possible — only that the *strict Beck distributive law* of §3.4 is unavailable. The correct surrogate is Part B.
- It leaves the `P_κ` port's finitely-many-elements argument as the one thing to machine-check; flagged as the residual verification, not hidden.

---

## Part B — Discharging the *content* of criterion (iv): the weak distributive law

The charter's criterion (iv) wants *bidirectional whole/part constitution via a coherent bialgebra*. §3.4 proposed the strict `λ` as the *mechanism*; Part A proves that mechanism unavailable. The literature identifies the **exact** correct replacement, and it is not an ad-hoc dodge: the powerset monad **weakly** distributes over itself (Garner; Goy–Petrişan–Aiguier), via the Egli–Milner / Vietoris construction. A *weak distributive law* drops the unit-of-`T` axiom (the one that forces the strict law and that Part A kills) while keeping naturality and the multiplication/comultiplication coherences — and it still yields a genuine bialgebraic structure on one carrier.

### B.1 The weak law, concretely

A **weak distributive law** `λ_w : T F ⇒ F T` (Böhm; Garner) satisfies naturality, both multiplication pentagons, and the `F`-unit law, but **not** the `T`-unit law `λ ∘ η^T F = F η^T`. The Egli–Milner weak law for powerset is:
```
λ_w,X (𝒮) = { t ∈ P_κ X : t is a "relational transversal" of 𝒮 }
          = the Egli–Milner extension of ⋃ to the relation level
```
Its restriction to the sublattice where it *does* satisfy the `T`-unit law is exactly the "idempotent-splitting" that Garner's weak-law theory formalizes.

### B.2 The composition operator, recovered

The weak law induces a composition `alg : P_κ (νP_κ).X → (νP_κ).X` as the unique coalgebra morphism into the terminal coalgebra whose one-step structure is the **Egli–Milner union of the parts' observations** — which is the *same* structural `alg` v2 built, now correctly *justified* as the action of a weak distributive law rather than presented as instrument-free:

```lean
def liftedCoalg_w (hreg : κ.IsRegular) : Coalg κ :=
  ⟨PkObj κ (νPk κ).X, fun t => join (PkMap κ (νPk κ).str t)⟩   -- = Egli–Milner big-union
def alg (hreg : κ.IsRegular) : PkObj κ (νPk κ).X → (νPk κ).X :=
  (νPk_terminal κ (liftedCoalg_w hreg)).choose
theorem alg_pentagon (hreg) (t) :
    (νPk κ).str (alg hreg t) = PkMap κ (alg hreg) (join (PkMap κ (νPk κ).str t))
```
`alg_pentagon` is now read correctly: it is the **weak-bialgebra coherence square** (the multiplication pentagon of `λ_w`), *not* a strict-`λ` pentagon (which Part A forbids) and *not* an unmotivated corecursion identity (v2's mislabeling). The `T`-unit law that fails is precisely `algUnit` at the non-idempotent points — which is **why** `algUnit` must be stated as holding on singletons/idempotents only:

```lean
theorem alg_unit_idem (hreg) (x : (νPk κ).X) : alg hreg (pure x) = x
-- holds: pure x = {x} is idempotent for Egli–Milner; the weak-law T-unit
-- law holds exactly on the idempotent-split subobject, of which singletons are members.
theorem alg_join (hreg) (tt) : alg hreg (join tt) = alg hreg (PkMap κ (alg hreg) tt)
-- holds: this is the multiplication coherence the WEAK law retains.
```

> The v2→v3 correction on the algebra laws: v2 claimed `alg_unit` unconditionally and called `alg_join` a monad law. Under the weak law the honest statement is that the *multiplication* coherence survives (`alg_join`) and the *`T`-unit* coherence survives **only on the idempotent-split part** (`alg_unit_idem`). Singletons are in that part, so every charter use (`Ω`, `reflects_part`) is covered; the general `alg (pure_nonidem …)` is *correctly* not asserted, matching Part A.

### B.3 Adequacy riders (bidirectionality — the actual Commitment 4 content)

**(A) Part-reflection (upward constitution).** As v2, now justified by the Egli–Milner union structure:
```lean
theorem reflects_part (hreg) (t) {x} (hx : x ∈ t.1) :
    ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg hreg t)).1
```
Downward constitution is the `F`-coalgebra `dest` itself. Upward + downward on one carrier `= ` the bidirectional determination Commitment 4 names.

**(B) `Ω` fixed point.** `alg (pure Ω) = Ω` from `alg_unit_idem` (`Ω` is a singleton-structured idempotent). Groundless inhabitant respected.

**(C) Non-triviality (T1 / anti-`Id`-shadow), strengthened form from v2:**
```lean
theorem alg_nontrivial (hreg) :
    ∃ a b, a ≠ b ∧ (let t := ⟨{a,b}, mk_pair_lt hreg a b⟩;
      ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
      ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
      alg hreg t ≠ a ∧ alg hreg t ≠ b)
```
Witnesses `a ≠ b` from `ws2_nondegenerate`; the two `⊆` from `reflects_part`; `alg t ≠ a,b` via `ws2_coinduction` on the strict containment (with the one caveat flagged in Part C).

### B.4 The deliverable structure (corrected signature and honest field set)

```lean
structure WeakBialgebra (κ : Cardinal.{u}) (hreg : κ.IsRegular) where
  alg            : PkObj κ (νPk κ).X → (νPk κ).X
  pentagon       : ∀ t, (νPk κ).str (alg t)
                         = PkMap κ alg (join (PkMap κ (νPk κ).str t))   -- weak-law mult. coherence
  algUnitIdem    : ∀ x, alg (pure (self := instMonadPkObj hreg.aleph0_le) x) = x  -- T-unit on idempotents
  algJoin        : ∀ tt, alg (join tt) = alg (PkMap κ alg tt)            -- multiplication coherence
  reflectsPart   : ∀ t {x}, x ∈ t.1 → ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg t)).1
  omegaFix       : ∀ ω, ((νPk κ).str ω).1 = {ω} → alg (pure ω) = ω
  nontrivial     : ∃ a b, a ≠ b ∧ (let t := ⟨{a,b}, mk_pair_lt hreg a b⟩;
                     ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     alg t ≠ a ∧ alg t ≠ b)
  noStrictLaw    : IsEmpty (DistLaw (PkObj κ) (PkObj κ))                 -- Part A, carried as a field

theorem ws3_weak_bialgebra (hreg : κ.IsRegular) : Nonempty (WeakBialgebra κ hreg)
```

The structure is honestly named `WeakBialgebra`, not `AdequateBialgebra`; the `pentagon` field is documented as the *weak-law* coherence; `algUnitIdem` (not `algUnit`) records the exact surviving unit law; and `noStrictLaw` **carries the impossibility inside the deliverable**, so no downstream reader can mistake this for a strict-`λ` bialgebra.

---

## Part C — Residuals, routed (not relabeled)

Per §8.2 discipline, the surrogate is stated openly and its residual obstructions are routed to owners:

1. **Which weak law is canonical, and its exact coherence grade.** The Egli–Milner law is *the* monotone weak law over `Set` (Garner), but whether the *bounded* `P_κ` inherits a unique weak law, and whether the enriched/weighted functor WS4 may adopt still has one, is open. **Routed to WS4** (the enriched-functor owner) as a ratification obligation on `(F, κ)` and the quantale — joining the §6.1 shared-parameter list.

2. **The `P_κ` port of the no-go proof.** Part A route (1) needs the four-set diagonal machine-checked over `P_κ`; the finitely-many-elements observation makes this routine but unproven-until-compiled. **Routed to WS3's own build** as the single verification gate (the honest analogue of WS1's owed `#print axioms`).

3. **`alg_nontrivial`'s one-step-observability caveat.** As in v2: if distinct terminal points are not one-step-observably distinct, the sharp non-triviality needs `ws2_bisim_behavioural` to supply a first-step distinguisher, else a coinductive weakening. **Routed to WS7** (non-collapse / richness floor), which owns the branching-≥2 floor that guarantees exactly this distinguishability.

4. **Strict-law impossibility ≠ program failure of Commitment 4.** Explicitly: Part A does *not* endanger criterion (iv). The charter said "coherent bialgebra"; the coherent bialgebra that exists is the *weak* one, and it carries the bidirectional determination that is the philosophical content. The strict-`λ` non-existence is a **positive** finding (Impossibility proved, §7) that sharpens the ROSR model: composition of relations-as-objects is inherently *non-strict* — a whole is not a plain union of its parts' behaviours but their Egli–Milner amalgam. That is arguably more faithful to Commitment 4 ("mediated by relations") than a strict union would have been.

---

## Part D — Charter discharge statement

| Charter element | v2 status | v3 status |
|---|---|---|
| §3.4 strict distributive law `λ` | silently dropped | **Impossibility proved** (Part A, theorem) |
| (iv) "coherent bialgebra" | Partial, mislabeled Discharged | **Discharged via weak bialgebra** (Part B) |
| Commitment 4 bidirectionality | delivered but unjustified | **Discharged** — `reflectsPart` (up) + `dest` (down), justified by `λ_w` |
| §8.1 gating question | not answered as required | **Answered first, as a theorem** |
| §8.2 substitute-openly discipline | violated (silent switch) | **Honored** — surrogate named, residual routed |
| T5 "real vs shadow constitution" | at risk (unmotivated pentagon) | **Met** — pentagon is the weak-law coherence; `noStrictLaw` carried in-structure |

**Net.** WS3 discharges Commitment 4 / criterion (iv) as a **two-part theorem**: the strict instrument of §3.4 is *proved impossible* for the WS1/WS2 carrier (a charter-sanctioned success), and the bidirectional constitution it was meant to secure is *delivered* by the weak distributive law that the impossibility forces — with the impossibility fact carried inside the deliverable so the substitution can never be read as a relabeling.

### Dependency / build order

```
Mathlib (finite Set diagonal reasoning; Cardinal.iSup_lt_of_isRegular, mul_lt_of_lt, mk_biUnion_le)
   │
ws1: PkMap(_id/_comp/_val), IsTerminalCoalg, hom_unique, endo_eq_id, νPk_terminal, lambek,
     omegaCoalg, omega_selfsingleton
ws2: ws2_nondegenerate, ws2_bisim_eq, ws2_bisim_behavioural, ws2_coinduction, mk_singleton/pair_lt
   │
   ├─ [NEW] Pk_preserves_preimages, betaPk + idem/nontrivial          §A.2
   ├─ [NEW] ws3_no_distributive_law  ← Klin–Salamanca Thm 2.4 port    §A.3   ⟵ GATE (theorem)
   ├─ [NEW] Pk_biUnion_lt (needs hreg — see v2 correction)            §B.2
   ├─ [NEW] instMonadPkObj, liftedCoalg_w, alg, alg_pentagon          §B.2
   ├─ [NEW] alg_unit_idem, alg_join   ← weak-law coherences           §B.2
   ├─ [NEW] reflects_part, omega_fix, alg_nontrivial                  §B.3
   └─ ws3_weak_bialgebra  (assembles B, carries noStrictLaw from A)   §B.4
```

*Carried forward from the v2 correction and still in force:* `Pk_biUnion_lt` requires `κ.IsRegular` (the `iSup` step needs cofinality; `hinf`-only fails for singular `κ`), so `hreg` is a genuinely consumed hypothesis, not a fidelity ornament.
