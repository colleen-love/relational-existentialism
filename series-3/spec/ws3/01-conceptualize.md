# WS3 — Bidirectional constitution via bialgebra

## The object at stake

WS3 must equip the groundless carrier with a **second** algebraic structure coherent with the coalgebraic one it already carries. Concretely: WS1/WS2 delivered a terminal `P_κ`-coalgebra `νP_κ` (carrier `U`, structure map `dest : U ≅ P_κ U`, an iso by Lambek). WS3 must additionally exhibit a composition monad `T`, a distributive law `λ : T P_κ ⇒ P_κ T`, and show that `U` (or some carrier jointly determined) is a **λ-bialgebra**: simultaneously a `T`-algebra `a : T U → U` and the `P_κ`-coalgebra `dest : U → P_κ U`, with the pentagon

```
    T U  --a-->  U  --dest-->  P_κ U
     |                            ↑
   T dest                      P_κ a
     ↓                            |
   T P_κ U  --λ_U-->  P_κ T U ---/
```

commuting.

## Why this is non-trivial (the three independent obstructions)

1. **`λ` need not exist.** A distributive law `T P_κ ⇒ P_κ T` is extra structure, not derivable from `T` and `P_κ` separately. For `T` = free monad of a signature, laws exist generically; for `T` = a *quotiented* composition monad (e.g. one whose algebras are semilattices, so that "union of parts" is idempotent/commutative) distributing over powerset, existence becomes a genuine coherence question, and there are known families of `(T,F)` with **no** law (Plotkin's counterexamples; the impossibility results of Klin–Salamanca and Zwart–Marsden on monad-over-monad distribution). This is the standing "distributive-law existence" risk.

2. **The final coalgebra need not carry the required `T`-algebra.** `νP_κ` is *final* for `P_κ`. Finality gives, via a law `λ`, a canonical `T`-algebra on `νF` (the "λ-bialgebra on the final coalgebra" of Turi–Plotkin / Bartels). But whether that algebra is the *intended* composition (e.g. models set-theoretic union of hereditarily-`<κ` sets, is associative/idempotent, respects `Ω`) is a separate adequacy claim. The carrier that is final for observation may not be the carrier that is free/initial for composition — Lambek's lemma cuts both ways: an object cannot be both a nontrivial initial `T`-algebra and final `F`-coalgebra for the *same* endofunctor, and even for distinct `T,F` the coincidence is a theorem to earn.

3. **Coherence can force `F` or the carrier to change.** If no law exists for the `(T, P_κ)` WS1/WS2 fixed, the repair is to move to a different observation functor or a different carrier — which *invalidates upstream discharged results*. This is the highest structural risk: WS3 is the workstream most able to retroactively break WS1/WS2.

**Success** = a single carrier with both structures and the pentagon proved. **Failure modes:** (a) no `λ` exists for the desired `(T,F)` — an *impossibility result*, which is a success under the charter's negative-result criterion, not a hidden defeat; (b) a `λ` exists but the induced `T`-algebra is degenerate/inadequate (collapses composition, or forces `U` to a point); (c) coherence is only achievable by changing `F`/carrier, breaking WS1/WS2.

---

## Ambient theory common to all framings

- **Encoding of AFA:** coalgebraic, as in WS1/WS2 — no set-theoretic AFA axiom imported. `νP_κ` is `Cofix (PkObj κ)` with `dest`, terminal by `νPk_terminal`.
- **`F` = `PkObj κ`** (`P_κ`), the bounded powerset QPF, inherited unchanged from WS2 unless a framing explicitly forks it.
- **Base:** Lean 4 + Mathlib, universe-polymorphic in `κ : Cardinal.{u}`, `hinf : ℵ₀ ≤ κ` available; regularity `_hreg` carried for fidelity but expected unused (per WS2's accounting).
- **Everything must remain axiom-free** beyond Mathlib's `propext`/`Classical.choice`/`Quot.sound`.

I give framings from most conservative (least commitment, most likely to discharge) to most ambitious.

---

## Framing 1 — Law-first, abstract distributive law (Turi–Plotkin canonical)

**Obligation cashed out as:** exhibit a monad `T` and a natural transformation `λ : T ∘ P_κ ⇒ P_κ ∘ T` satisfying the four distributive-law axioms (unit-left, unit-right, mult-left, mult-right), then invoke the general theorem that a law lifts `P_κ` to `T`-algebras and induces a canonical `T`-algebra on `νP_κ`.

**Strategy:** Take `T` = free semilattice monad (finite/`<κ` unordered composition with idempotent commutative union). Define `λ` on generators by the standard "union distributes into the branching" clause. Prove the four coherence squares by `PkMap` calculation (reuse `PkMap_comp`, `PkMap_id`). Then define the bialgebra algebra `a := (P_κ)`-anamorphism-free route: `a : T U → U` as the unique coalgebra morphism from `(T U, λ_U ∘ T dest)` into the terminal `U`.

**Lean signature:**
```lean
structure DistLaw (T : Type u → Type u) [Monad T] (κ : Cardinal.{u}) where
  lam        : ∀ {X}, T (PkObj κ X) → PkObj κ (T X)
  natural    : ∀ {X Y} (f : X → Y) (t : T (PkObj κ X)),
                 lam (Functor.map (PkMap κ f) t) = PkMap κ (Functor.map f) (lam t)
  unit_left  : ∀ {X} (s : PkObj κ X), lam (pure s) = PkMap κ pure s
  unit_right : ∀ {X} (t : T X), lam (Functor.map (fun x => (⟨{x}, mk_singleton_lt ‹_› x⟩)) t)
                 = pure t            -- schematic; exact form fixed at build time
  mult_left  : ∀ {X} (tt : T (T (PkObj κ X))), lam (joinT tt) = PkMap κ joinT (lam (Functor.map lam tt))
  mult_right : ∀ {X} (t : T (T (PkObj κ X))), lam (Functor.map joinP t) = joinP (lam (Functor.map lam t))

theorem ws3_distlaw_exists (hinf : ℵ₀ ≤ κ) :
    ∃ (T : Type u → Type u) (_ : Monad T), Nonempty (DistLaw T κ)
```
and the induced bialgebra:
```lean
theorem ws3_bialgebra_on_final (hinf : ℵ₀ ≤ κ) (D : DistLaw T κ) :
    ∃ a : T (νPk κ).X → (νPk κ).X,
      ∀ t, (νPk κ).str (a t) = D.lam (Functor.map (νPk κ).str t) |> PkMap κ a
```
(pentagon stated as the commuting equation on `dest ∘ a`).

**Success:** all four axioms `rfl`/`simp`-discharged; `a` exists and is unique by `νPk_terminal`.
**Failure:** one of `mult_left`/`mult_right` fails to typecheck as an identity — signals *no law of this shape*, i.e. impossibility for the free-semilattice `T`. **Trade-off:** cleanest, reuses WS2 machinery wholesale, but commits to a specific `T` whose adequacy (that `a` is *real* composition) is unproven here.

---

## Framing 2 — Bialgebra as a coalgebra of a lifted functor (Bartels/lifting form)

**Obligation cashed out as:** rather than proving `λ`'s axioms directly, show `P_κ` **lifts** to the Eilenberg–Moore category `Alg T`, i.e. there is an endofunctor `P̂_κ` on `T`-algebras with forgetful-commuting, and that `νP_κ` underlies the terminal `P̂_κ`-coalgebra.

**Lean signature:**
```lean
structure Lifting (T : Type u → Type u) [Monad T] (κ : Cardinal.{u}) where
  onAlg   : {A : Type u} → (T A → A) → (T (PkObj κ A) → PkObj κ A)
  commutes: ∀ {A} (alg : T A → A) (t : T (PkObj κ A)),
              -- forgetful ∘ P̂ = P_κ ∘ forgetful
              True  -- placeholder for the square; concretized at build
theorem ws3_lifting_iff_distlaw (hinf : ℵ₀ ≤ κ) :
    (∃ D : DistLaw T κ, True) ↔ Nonempty (Lifting T κ)
```
**Strategy:** prove the standard bijection law ↔ lifting (Johnstone/Turi–Plotkin), then work on whichever side is easier to discharge in Lean. **Trade-off:** the equivalence itself is reusable and de-risks Framing 1 by giving a second attack surface; but it proves *no more* than Framing 1 about adequacy. **Failure:** neither side inhabitable → same impossibility.

---

## Framing 3 — Bialgebra structure map bundled, existence only (minimal deliverable)

**Obligation cashed out as:** the weakest thing worth calling success — a carrier with *both* maps and the pentagon, existence-only, no claim that `T` is "the" composition.

**Lean signature:**
```lean
structure Bialgebra (κ : Cardinal.{u}) (T : Type u → Type u) [Monad T] where
  carrier : Coalg κ
  alg     : T carrier.X → carrier.X
  algHom  : ∀ (t : T (T carrier.X)), alg (joinT t) = alg (Functor.map alg t)   -- T-algebra laws
  algUnit : ∀ x, alg (pure x) = x
  pentagon: ∀ t : T carrier.X,
              carrier.str (alg t) = PkMap κ alg (lam (Functor.map carrier.str t))

theorem ws3_bialgebra_exists (hinf : ℵ₀ ≤ κ) :
    ∃ (T : Type u → Type u) (_ : Monad T), Nonempty (Bialgebra κ T)
```
**Strategy:** instantiate `T` minimally (even `T = Id` gives a trivial law — a *sanity floor*, not the deliverable), then upgrade `T` to the smallest monad that makes the bialgebra non-trivial. **Trade-off:** almost certainly dischargeable, but risks being vacuous (`T = Id` satisfies it) — must be paired with a non-degeneracy rider (below) to mean anything.

---

## Framing 4 — Adequacy-carrying bialgebra (the honest target)

**Obligation cashed out as:** Framing 3 **plus** an adequacy predicate forcing `alg` to model genuine downward/upward constitution: `alg` restricted to singletons is identity (unit), `alg` of a union-of-parts recovers containment (`str (alg t) ⊇` the parts' structures), and `Ω` is a fixed point of self-composition.

**Lean signature (adds to `Bialgebra`):**
```lean
structure AdequateBialgebra (κ : Cardinal.{u}) (T : Type u → Type u) [Monad T]
    extends Bialgebra κ T where
  reflects_part : ∀ (t : T carrier.X) (x : carrier.X),
                    memberOf x t → (carrier.str x).1 ⊆ (carrier.str (alg t)).1
  omega_fix     : ∀ (ω : carrier.X), (carrier.str ω).1 = {ω} →
                    alg (pure ω) = ω
  nontrivial    : ∃ a b : carrier.X, a ≠ b ∧ alg (pure a) ≠ alg (pure b)

theorem ws3_adequate_bialgebra (hinf : ℵ₀ ≤ κ) :
    ∃ (T : Type u → Type u) (_ : Monad T), Nonempty (AdequateBialgebra κ T)
```
**Success:** all fields inhabited for a `T` that is *not* `Id`. **Failure:** `reflects_part` and `pentagon` provably incompatible (composition cannot both be a `T`-algebra and respect observation) → **impossibility proved**, the charter-sanctioned negative result. **Trade-off:** this is the framing that actually discharges the charter obligation rather than a shadow of it, but it is the one most likely to expose obstruction 2.

---

## Framing 5 — Gating question first (fail-fast / no-go detector)

**Obligation cashed out as:** *before* building anything on the WS1/WS2 carrier, decide the yes/no question "does `νP_κ` admit the required `T`-algebra + coherent `λ`?" as a decidable disjunction.

**Lean signature:**
```lean
inductive WS3Verdict (κ : Cardinal.{u}) (T : Type u → Type u) [Monad T]
  | discharged (b : Bialgebra κ T)
  | impossible (h : (Nonempty (DistLaw T κ)) → False)

theorem ws3_verdict (hinf : ℵ₀ ≤ κ) (T : Type u → Type u) [Monad T] :
    Nonempty (WS3Verdict κ T)
```
**Strategy:** for a fixed candidate `T`, either construct the law or derive `False` from its four axioms (Klin–Salamanca-style: exhibit two elements whose `λ`-image is forced to be both distinct and equal). **Trade-off:** cheapest way to *retire the structural risk to WS1/WS2* — it answers "will WS3 break upstream?" before committing — but proves nothing constructive if the verdict is `impossible`. This is the framing to run **first** operationally.

---

## Framing 6 — Carrier-changing (bialgebra of a *cofree* comonad / different `F`)

**Obligation cashed out as:** admit that the WS1/WS2 `F = P_κ` may not support composition, and instead seek the bialgebra over a **modified** observation functor `F' = P_κ(- ) × M` (annotating each object with a composition-monoid label `M`), building `λ' : T F' ⇒ F' T`.

**Lean signature:**
```lean
def PkAnn (κ : Cardinal.{u}) (M : Type u) (X : Type u) : Type u := PkObj κ X × M

theorem ws3_bialgebra_modified (hinf : ℵ₀ ≤ κ) :
    ∃ (M : Type u) (T : Type u → Type u) (_ : Monad T),
      Nonempty (Bialgebra' κ M T)          -- Bialgebra over PkAnn κ M
      ∧ (∀ X, (PkAnn κ M X) → PkObj κ X)   -- forgetful to P_κ, so WS1/WS2 recovered
```
**Success:** bialgebra exists over `F'` **and** the forgetful map recovers the WS1/WS2 carrier up to bisimulation, so upstream is *not* invalidated — only extended.
**Failure:** the forgetful functor fails to preserve the terminal coalgebra → WS1/WS2 genuinely broken → must be reported as such, not hidden. **Trade-off:** the escape hatch when Framing 5 returns `impossible`; buys existence at the cost of a heavier functor and a new adequacy burden (that the annotation `M` *is* composition, not decoration).

---

## Cross-cutting trade-off summary

| Framing | Likelihood of discharge | What it proves if it succeeds | Risk to WS1/WS2 | Vacuity risk |
|---|---|---|---|---|
| 1 Law-first | medium | law + induced algebra | none | low |
| 2 Lifting | medium | law-equiv, 2nd attack surface | none | low |
| 3 Existence-only | high | *a* bialgebra exists | none | **high** (`T=Id`) |
| 4 Adequate | low–medium | the real obligation | none | none |
| 5 Gating verdict | high | yes/no + no-go detection | **retires** it | n/a |
| 6 Carrier-changing | medium | existence over `F'` | **potentially breaks** | medium |

**Recommended order of attack:** run **5** to get a verdict for the intended `T`; if `discharged`, pursue **1**(→**2** as backup) and then strengthen to **4** for the honest deliverable; only if **5** returns `impossible` fall to **6**, and if **6** also fails, report **impossibility proved** — a valid terminal outcome, not a defeat.

**The single gating question that dominates all framings:** *does the final `P_κ`-coalgebra admit a `T`-algebra for a composition monad `T` together with a coherent `λ`, without forcing a change to `F` or the carrier?* Answer it (Framing 5) before building on the WS1 carrier.
