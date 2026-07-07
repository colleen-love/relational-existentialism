# WS1 Design Document: The Groundless Carrier
## C1 (core) + C2 (solution lemma) as reusable BR-level infrastructure

---

## 0. Scope and reading guide

This document expands the recommended spine — **C1** proving existence/identity of the carrier, **C2** deriving the solution lemma as the working form of AFA — into a full proof architecture: what must be defined, in what order, which lemmas discharge which failure mode, and which upstream theorems (category-theoretic and set-theoretic) are being imported as black boxes versus which need local reproof because Mathlib's version doesn't quite fit.

The design is organized as a dependency DAG, not a linear script, because several branches (accessibility of `P_κ`, the coalgebra category's completeness, the anamorphism machinery) can be developed in parallel before they meet at the final theorem.

---

## 1. Fixing the ambient objects

### 1.1 The functor

Everything downstream depends on a single choice: the **κ-bounded powerset functor**.

```
Definition (PkFunctor).
  Fix κ : Cardinal, regular.
  P_κ : Type u ⥤ Type u
  P_κ.obj X  := {s : Set X // Cardinal.mk s < κ}
  P_κ.map f  := fun ⟨s, hs⟩ => ⟨f '' s, image_card_lt hs⟩
```

Two structural facts about `P_κ` must be established *before* anything about the carrier, because they are the load-bearing beams of the whole existence argument:

**Lemma 1.1 (functoriality).** `P_κ` respects identity and composition. Routine, but `image_card_lt` (the image of a set of size `< κ` under any function has size `< κ`) needs its own name since it's invoked constantly.

**Lemma 1.2 (κ-accessibility of `P_κ`).** `P_κ` preserves `κ`-filtered colimits. This is the crux fact enabling the terminal-sequence theorem. Proof: a `κ`-filtered colimit of sets is computed as a set-quotient of the disjoint union; a subset of size `< κ` factors through some stage of the diagram because `κ` is regular (a `< κ`-indexed family, each landing in the colimit, has all its "supports" bounded, and a `κ`-filtered diagram absorbs any `< κ` many indices into one object). This is exactly where regularity of `κ` is *used*, not just assumed for flavor — flag this clearly, since it is the one step where a non-regular choice of `κ` breaks the entire argument rather than just weakening it.

**Dependency flag:** Mathlib has general accessible-functor infrastructure (`CategoryTheory.Presentable` line of work) but likely nothing specialized to bounded powerset. Lemma 1.2 is probably a genuine new proof, not a lookup.

### 1.2 The category of coalgebras

```
Definition (Coalg F) := CategoryTheory.Coalgebra F
  -- objects: (X : Type u, α : X → F.obj X)
  -- morphisms: f : X → Y commuting with structure maps
```

**Lemma 1.3.** `Coalg (P_κ)` has a terminal object iff `P_κ` has a final coalgebra in the classical sense; this is definitional, but stating it lets every subsequent proof talk about *terminality* (a categorical universal property with existing Mathlib API: `IsTerminal`, uniqueness up to unique iso) rather than reinventing "final coalgebra" vocabulary.

---

## 2. Existence of the carrier: the terminal-sequence route

This is the technical heart of C1, corresponding to failure mode (i) in the source document — non-existence.

### 2.1 The terminal sequence

```
Definition (finalSeq).
  finalSeq F : Ordinal → Type u  (as a functor out of Ord^op, i.e. an inverse system)
  finalSeq F 0       := PUnit
  finalSeq F (α + 1) := F.obj (finalSeq F α)
  finalSeq F λ       := lim_{α < λ} (finalSeq F α)   -- λ limit ordinal, inverse limit
```

Connecting maps `finalSeq F β → finalSeq F α` for `α ≤ β` built by transfinite recursion simultaneously with the sequence.

**Upstream import needed:** existence of inverse limits of the required shape in `Type u`. This is *not* a coalgebra-specific fact — it's ordinary limits in `Type u`, which Mathlib has (`Type u` is complete). What must be checked locally is that the limit at stage `λ` computed this way agrees with the categorical limit of the diagram restricted to `α < λ`, which is just unwinding definitions once, not a new theorem.

### 2.2 Stabilization

**Theorem 2.1 (Worrell / Adámek–Koubek stabilization, imported as a black box with local restatement).**
If `F` preserves `κ`-filtered colimits (Lemma 1.2) and is bounded by `κ` (which `P_κ` is, tautologically, by construction — every value has cardinality `< κ`), then the terminal sequence `finalSeq F` stabilizes at some ordinal `α ≤ κ`: the connecting map `finalSeq F (α+1) → finalSeq F α` is an isomorphism.

This is the single largest external dependency in the whole design. It should be imported as a *named hypothesis* first:

```lean
axiom stabilization_theorem
    (F : Type u ⥤ Type u) (κ : Cardinal) (hκ : κ.IsRegular)
    (hacc : PreservesFilteredColimitsOfSize κ F) (hbdd : BoundedBy F κ) :
    ∃ α : Ordinal, α ≤ κ.ord ∧ IsIso (finalSeq.connectingMap F (α+1) α)
```
with a TODO to replace the axiom with an actual formalized proof (this is genuinely nontrivial ordinal-induction combinatorics — likely the single most expensive sub-formalization in WS1, and should be budgeted as such rather than assumed cheap).

**Corollary 2.2.** Setting `U := finalSeq F α` for the stabilizing `α`, the structure map `U → F.obj U` (inverse of the iso from 2.1) makes `U` a coalgebra, and it is **terminal** in `Coalg F` — this direction (stabilized limit ⇒ terminal coalgebra, not just a fixed point) needs its own short argument: any coalgebra `(X, ξ)` maps into `finalSeq F α` by transfinite recursion along the sequence (the unique cone map into the limit, built stage by stage using `ξ` and functoriality), and uniqueness of this cone map is where terminality — not mere existence of *a* fixed point — comes from.

This discharges **failure mode (i)** for C1: existence is not assumed, it's derived from regularity of `κ` plus the general shape theorem, with the one external black box clearly labeled.

### 2.3 Lambek's lemma

**Lemma 2.3 (Lambek, essentially free once terminality is in hand).** If `U` is terminal in `Coalg F`, its structure map `struct : U → F.obj U` is an iso.

*Proof sketch:* `F.obj U` carries a coalgebra structure `F.map struct : F.obj U → F.obj (F.obj U)`. By terminality there's a unique coalgebra map `g : F.obj U → U`. Then `g ∘ struct` and `struct ∘ g` are both coalgebra endomorphisms of the relevant objects; terminal-object endomorphisms are identities by the uniqueness half of the universal property. Standard, but write it out fully since it's invoked as the `struct` field of `GroundlessCarrier` directly.

This gives the **Lambek iso** field of the target structure with no further axioms.

---

## 3. Identity: bisimulation = equality

This discharges **failure mode (ii)** (collapse) and is the other half of what "canonical identity criterion" means.

### 3.1 Bisimulation, defined coalgebraically

```
Definition (Bisim F X).
  A relation R : X → X → Prop is an F-bisimulation if there exists
  a coalgebra structure on {p : X × X // R p.1 p.2} making both
  projections coalgebra morphisms into (X, ξ).

Definition (bisimEquiv) := the union of all bisimulations (the *greatest* one) — 
  needs: bisimulations are closed under union, so the union of all of them
  is again a bisimulation (routine, but state explicitly — this is where
  "greatest bisimulation exists" actually gets proved, it doesn't come for free).
```

**Lemma 3.1.** `bisimEquiv` is itself an equivalence relation (reflexive: diagonal is a bisimulation; symmetric: swap is a bisimulation; transitive: relation-composition of two bisimulations is a bisimulation, using that `F` preserves the relevant pullback-like structure — for `P_κ` specifically this reduces to a set-image argument).

### 3.2 Terminal ⇒ bisimilarity is equality

**Theorem 3.2 (the actual content of `bisim_eq`).** In the terminal coalgebra `U`, `bisimEquiv = (· = ·)`.

*Proof:* `(⊇)` is Lemma 3.1's reflexivity. `(⊆)`: suppose `R` is a bisimulation on `U`. The subobject `{p // R p.1 p.2} ↪ U × U` carries a coalgebra structure with both projections as coalgebra morphisms. By terminality, both projections equal the *unique* map into `U`, hence agree — so `R p.1 p.2 → p.1 = p.2`.

This is where terminality is doing *all* the work, and it's worth stating as its own named theorem since C2 and later workstreams cite "bisimilarity is equality" far more often than they cite terminality directly.

**This directly rules out failure mode (ii):** collapse to a point would require a bisimulation relating *every* pair, and by 3.2 that would force `U` to have at most one element — which is refuted separately by:

### 3.3 Non-degeneracy (≥ 2 elements)

Needs an actual witness. Take two coalgebras with provably non-bisimilar roots:
- `A`: single-node graph with the empty relation (`a ↦ ∅`).
- `B`: single-node graph looping to itself (`b ↦ {b}`).

Map each into `U` via the unique coalgebra morphism (terminality), get `image(a), image(b) : U`. If these were bisimilar in `U`, pulling back along the two morphisms would exhibit `A` and `B` themselves as bisimilar as coalgebras (bisimilarity reflects along coalgebra morphisms into a common terminal object — a short lemma, "bisimulation pullback," worth stating once), contradicting a direct check that `a ↦ ∅` and `b ↦ {b}` cannot be related by any bisimulation (an `∅`-rooted node can only be related to another `∅`-rooted node, by unfolding the bisimulation condition one step). Hence `image(a) ≠ image(b)`.

### 3.4 Surjectivity of `struct` (no atom leakage — failure mode iii)

`struct : U ≅ P_κ.obj U` is already an iso by Lambek (§2.3), so surjectivity is automatic, *not* a separate proof — this is worth flagging explicitly as a place where C1's architecture is stronger than it looks: fixing the iso in `GroundlessCarrier` already forecloses failure mode (iii) as a corollary of Lambek, with zero extra work. Record this as a one-line remark rather than a new lemma, so nobody in later workstreams goes looking for a nonexistent separate surjectivity proof.

---

## 4. Constructing `Ω`

```
Definition (omegaCoalg) : Coalg P_κ on carrier `PUnit`,
  structure map `∗ ↦ ⟨{∗}, (card {∗} = 1 < κ since κ regular ⇒ κ ≥ ℵ₀ > 1)⟩`

Definition (Ω) := (the unique coalgebra morphism omegaCoalg → U) applied to `∗`
```

**Theorem 4.1 (`omega_selfsingleton`).** `struct Ω = ⟨{Ω}, _⟩`.

*Proof:* Let `h : PUnit → U` be the unique coalgebra morphism. Coalgebra-morphism-ness means `struct (h ∗) = P_κ.map h (⟨{∗}, _⟩) = ⟨h '' {∗}, _⟩ = ⟨{h ∗}, _⟩`. Substitute `Ω := h ∗`.

This is a two-line proof *given* the terminal coalgebra machinery — the entire weight sits upstream in §2–3, which is the intended shape: `Ω`'s existence should feel almost free once finality is secured, since "define by unique coalgebra morphism out of the obvious one-node self-loop" is the generic recipe for *any* self-referential definition, not a bespoke trick for `Ω` alone. This generic recipe is exactly what gets extracted and reused in C2.

---

## 5. Assembling `GroundlessCarrier` (C1's target theorem)

```lean
theorem ws1_C1 (hκ : κ.IsRegular) : Nonempty (GroundlessCarrier (κ := κ)) := by
  obtain ⟨α, hα, hiso⟩ := stabilization_theorem PkFunctor κ hκ (accessibility_lemma hκ) rfl
  let U := finalSeq PkFunctor α
  exact ⟨{ U := U
         , final := terminality_of_stabilized_limit hiso   -- §2.2 Corollary 2.2
         , struct := lambek_iso final                       -- §2.3
         , bisim_eq := bisim_eq_of_terminal final            -- §3.2
         , omega := omega_def final                          -- §4
         , omega_selfsingleton := omega_thm final             -- §4.1
         }⟩
```

Non-degeneracy (§3.3) is *not* a field of `GroundlessCarrier` as given in the source spec — flag this as a gap: the structure as specified doesn't force non-triviality, only bisim_eq and the specific Ω-witness. Recommend adding a `nondegenerate : ∃ a b : U, a ≠ b` field, discharged by §3.3, so that `GroundlessCarrier` can't be vacuously satisfied by a one-point coalgebra with a self-looping "Ω" that's also everything else.

---

## 6. C2: the Solution Lemma, built on top of C1

C2 is where the payoff of having gone through *terminality* (rather than some weaker fixed-point statement) shows up, because uniqueness of solutions is uniqueness of the cone map, verbatim reused from §2.2.

### 6.1 Systems as coalgebras on `I ⊕ U`

Given `e : I → P_κ.obj (I ⊕ U)`, build a coalgebra structure on `I ⊕ U`:

```
Definition (systemCoalg e).
  carrier := I ⊕ U
  structMap : I ⊕ U → P_κ.obj (I ⊕ U)
    | inl i => P_κ.map (id ⊕ ...) applied to (e i)      -- reindex e i's targets into I ⊕ U (already there)
    | inr u => (id ⊕ id) applied to struct u             -- U's own coalgebra structure, pushed along inr
```

The `inr` branch needs `P_κ.obj U → P_κ.obj (I ⊕ U)` via `P_κ.map Sum.inr` composed with the existing `struct : U → P_κ.obj U` — routine functoriality, but state it as its own definitional step since getting the two branches of this coalgebra to typecheck consistently is the fiddly part of the whole construction.

**Lemma 6.1.** `systemCoalg e` is a well-defined `P_κ`-coalgebra (the two branches agree on typing, and boundedness `< κ` is preserved — inherited from `e i`'s own bound and from `U`'s own `struct`).

### 6.2 Extracting the solution

By terminality of `U` (§2.2), there is a **unique** coalgebra morphism `h : I ⊕ U → U` from `systemCoalg e`. Define `sol := h ∘ inl : I → U`.

**Theorem 6.2 (existence half of `ws1_C2_solutionLemma`).** `sol` satisfies the defining equation: `struct (sol i) = (Sum.elim sol id) '' (e i).val`.

*Proof:* Coalgebra-morphism-ness of `h` gives `struct (h (inl i)) = P_κ.map h (structMap (inl i)) = P_κ.map h (e i, reindexed)`. Unwind: `P_κ.map h` applied to a subset of `I ⊕ U` reindexed via inclusion is exactly `image (Sum.elim sol id)` of `e i`'s underlying set, using `h ∘ inl = sol` and `h ∘ inr = id` (the latter because the restriction of `h` to the `U`-summand must be a coalgebra endomorphism of the terminal object composed appropriately, forcing it to be the identity by the same terminal-endomorphism argument as Lambek's lemma in §2.3 — worth citing that lemma again rather than reproving).

**Theorem 6.3 (uniqueness half).** If `sol'` also satisfies the equation, then `Sum.elim sol' id` is a coalgebra morphism `systemCoalg e → U`, and by *terminality* there is only one such morphism, namely `h`; hence `sol' = h ∘ inl = sol`.

This is the cleanest illustration of why C1 had to deliver *terminality* and not merely "a fixed point exists": uniqueness in C2 is a direct corollary of uniqueness in the universal property, with no extra combinatorial argument needed. If C1 only produced *a* coalgebra `U` with `struct` merely an isomorphism (Lambek can hold for non-terminal fixed points too, in general categories — though not for `P_κ` on `Type u` specifically, this is worth flagging as a reason the design insists on the stronger statement) uniqueness would need a wholly separate proof, likely by a bisimulation argument identifying any two candidate solutions — strictly more work, and exactly the kind of hidden cost the "identity vs existence" tension in the cross-cutting trade-offs section is pointing at.

### 6.3 Recovering `Ω` as a special case

Set `I := Unit`, `e := fun _ => ⟨{Sum.inl ()}, _⟩`. Then `systemCoalg e` restricted to behavior at `()` reproduces exactly `omegaCoalg` from §4 up to relabeling, and `sol ()` satisfies `struct (sol ()) = {sol ()}`, i.e. `sol () = Ω` by uniqueness (§6.3 applied to the witness already constructed in §4, or conversely — either can serve as the "base case" and the other as a corollary; recommend keeping §4's direct construction as primary since it's needed before C2 is available, and citing it here to confirm consistency rather than re-deriving `Ω` from scratch).

This closes the loop the source document flags explicitly ("specializing `I = Unit`... recovers `Ω = {Ω}`") and gives a consistency check for free: two independent routes to `Ω` (direct anamorphism in §4, and instantiation of the general solution lemma in §6) must agree, and proving they agree is a good regression test once both are formalized.

---

## 7. Dependency graph summary

```
Lemma 1.1 (functoriality)
Lemma 1.2 (κ-accessibility) ──┐
                              ├──▶ Theorem 2.1 (stabilization) ─▶ Corollary 2.2 (terminality)
[stabilization_theorem, EXTERNAL] ┘                                    │
                                                                        ├─▶ Lemma 2.3 (Lambek iso)
                                                                        │        │
                                                                        │        ▼
                                                                        │   §3.4 surjectivity (free)
                                                                        │
                                                                        ├─▶ Lemma 3.1 (bisim is equiv. rel.)
                                                                        │        │
                                                                        │        ▼
                                                                        ├─▶ Theorem 3.2 (bisim = eq)
                                                                        │        │
                                                                        │        ▼
                                                                        │   §3.3 non-degeneracy
                                                                        │
                                                                        ├─▶ §4 Ω construction ─▶ Theorem 4.1
                                                                        │
                                                                        ▼
                                                              ws1_C1 (assembled)
                                                                        │
                                                                        ▼
                                                        §6.1–6.2 systemCoalg + uniqueness
                                                                        │
                                                                        ▼
                                                        ws1_C2_solutionLemma
                                                                        │
                                                                        ▼
                                                          §6.3 Ω-consistency check
```

**External imports, ranked by risk:**
1. **`stabilization_theorem`** (§2.1, Theorem 2.1) — highest risk; likely not in Mathlib in this generality, genuinely nontrivial ordinal induction, should be scoped as its own sub-effort rather than assumed available.
2. Completeness of `Type u` for computing the limit stage of the terminal sequence (§2.1) — should already be in Mathlib, low risk.
3. General terminal-object uniqueness API (`IsTerminal`, used repeatedly in §2.2, §3.2, §6.3) — standard Mathlib category theory, low risk.
4. Cardinal arithmetic for regular cardinals (`κ`-filtered colimits absorb `< κ`-indexed data) — partially in Mathlib's cardinal file, but the filtered-colimit-specific packaging (Lemma 1.2) likely needs local glue code.

---

## 8. What this design leaves open for later workstreams

- The concrete value of `κ` is left schematic throughout, per the source document's mandate; every theorem above is stated "for `κ` regular," deferring the Goldilocks choice to WS7 as instructed.
- `GroundlessCarrier` as specified is missing a non-degeneracy field; §3.3 supplies the proof but the structure itself should be patched — this should be raised as an amendment before other workstreams start citing the structure.
- C3 (graph/decoration) and C6 (explicit final-sequence) are not built here but are compatible cross-checks: C6's finalSeq machinery is in fact *reused directly* in this design (§2.1), so formalizing C6 fully is nearly free once C1 is done — worth noting as an efficient next step rather than genuinely independent validation.
