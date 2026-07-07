# WS1 Design Document: The Groundless Carrier (Revision 2)
## C1 (core) + C2 (solution lemma) as reusable BR-level infrastructure

> **Revision note.** This revision resolves issues flagged in review: (1) a
> mistyped/over-stated map in the `systemCoalg` construction (§6.1), (2) an
> underspecified external axiom whose exact quantifiers matter (§2.2),
> (3) an uniqueness argument in Corollary 2.2 that was under-costed relative
> to its real difficulty (§2.2), (4) an unproved-but-load-bearing
> weak-pullback fact for `P_κ`, now a named lemma (§3.1a), (5) a compressed
> non-degeneracy argument, now spelled out (§3.3), (6) a standing hypothesis
> (`κ` infinite) that was derived implicitly instead of assumed globally
> (§1.1), and (7) the `Ω`-consistency check in §6.3, which needed its own
> gluing lemma rather than being called "either direction, free." Changes
> are marked **[REVISED]** or **[NEW]** inline; unaffected material is
> unchanged from the original design.

---

## 0. Scope and reading guide

This document expands the recommended spine — **C1** proving existence/identity of the carrier, **C2** deriving the solution lemma as the working form of AFA — into a full proof architecture: what must be defined, in what order, which lemmas discharge which failure mode, and which upstream theorems (category-theoretic and set-theoretic) are being imported as black boxes versus which need local reproof because Mathlib's version doesn't quite fit.

The design is organized as a dependency DAG, not a linear script, because several branches (accessibility of `P_κ`, the coalgebra category's completeness, the anamorphism machinery) can be developed in parallel before they meet at the final theorem.

**[NEW] Standing hypothesis, fixed once and used everywhere.** Throughout, `κ` denotes an **infinite regular cardinal**: `κ.IsRegular ∧ κ ≥ ℵ₀`. This is stated once here, as a hypothesis on `PkFunctor` itself (§1.1), rather than being derived ad hoc at the point of first use. (The original draft derived `κ ≥ ℵ₀` implicitly inside the proof of Theorem 4.1, from regularity alone — see the note at the end of §1.1 for why regularity alone does not suffice and infiniteness must be assumed directly.)

---

## 1. Fixing the ambient objects

### 1.1 The functor

Everything downstream depends on a single choice: the **κ-bounded powerset functor**.

```
Definition (PkFunctor).
  Fix κ : Cardinal.
  Hypothesis hκ_reg : κ.IsRegular
  Hypothesis hκ_inf : κ.IsInfinite         -- [NEW] see note below
  P_κ : Type u ⥤ Type u
  P_κ.obj X  := {s : Set X // Cardinal.mk s < κ}
  P_κ.map f  := fun ⟨s, hs⟩ => ⟨f '' s, image_card_lt hs⟩
```

**[NEW] Note on `hκ_inf`.** Some formalizations of `IsRegular` in Mathlib are stated so as to be satisfiable (vacuously or not) by small finite cardinals, depending on convention. If `κ` were finite, `P_κ.obj X` would either collapse to a degenerate structure (e.g. only allowing the empty set, if `κ ≤ 1`) or otherwise fail to support the constructions in §4 and §6, which need singleton sets and small unions to have cardinality `< κ`. Rather than re-derive `κ ≥ ℵ₀` at the one point it happens to be needed (as the original draft did inside Theorem 4.1's proof, citing regularity as the reason), we assume it globally as `hκ_inf`, alongside `hκ_reg`, as a hypothesis carried by every downstream definition and theorem. This makes every later "since `κ` is regular, `n < κ`" step for finite `n` a direct consequence of `hκ_inf` (finite `< ℵ₀ ≤ κ`), not a regularity argument at all — regularity is reserved for its actual job, Lemma 1.2.

Two structural facts about `P_κ` must be established *before* anything about the carrier, because they are the load-bearing beams of the whole existence argument:

**Lemma 1.1 (functoriality).** `P_κ` respects identity and composition. Routine, but `image_card_lt` (the image of a set of size `< κ` under any function has size `< κ`) needs its own name since it's invoked constantly.

**Lemma 1.2 (κ-accessibility of `P_κ`).** `P_κ` preserves `κ`-filtered colimits.

**[REVISED] Proof, unbundled into its three separate components** (the original phrasing bundled these together; a formalizer needs each as a distinct fact about `κ`-filtered diagrams, since they correspond to different pieces of Mathlib's filtered-category API and are proved by different means):

Let `D : J ⥤ Type u` be a `κ`-filtered diagram with colimit `(C, ι)`, and let `s ⊆ C` with `Cardinal.mk s < κ`.

- **(a) Local representatives.** Every element `c ∈ s` has *some* representative: some stage `j : J` and `x_j ∈ D.obj j` with `ι_j x_j = c`. (This uses only that `C` is computed as a colimit — a quotient of the disjoint union — and needs no filteredness or regularity; it is the "every element of a colimit comes from some stage" fact, standard for colimits of sets.)
- **(b) Bounding the index set of stages needed.** The map `c ↦ (a choice of stage j_c)` from `s` to `J`'s object set has image of size `≤ Cardinal.mk s < κ`. **This is exactly where regularity of `κ` is used, and only here**: a `κ`-filtered category has the property that any subset of its objects of size `< κ` has an upper bound (a single object that every member of the subset maps into), and this upper-bound property is *equivalent to* `κ`-filteredness for the index category — it is not an extra assumption, it is what `κ`-filtered means, but it is regularity of `κ` that guarantees a `< κ`-sized family of "supports," one per element of `s`, is itself a `< κ`-sized subset of `J`'s objects that the filtered structure can then bound. (If `κ` were singular, a `< κ`-sized union of smaller bounded pieces need not itself be `< κ`, and the argument breaks at exactly this step — this is the "one step where a non-regular choice of `κ` breaks the entire argument rather than just weakening it," as flagged in the original draft, now localized precisely to step (b) rather than to the lemma as a whole.)
- **(c) Producing a single common stage.** By `κ`-filteredness of `J` (using the upper bound from (b)), there is a single object `j⋆ : J` and a cocone map from every `j_c` (for `c ∈ s`) into `j⋆`. Composing each element's representative along these cocone maps produces a single `x ∈ D.obj j⋆` — more precisely a `< κ`-sized *subset* of `D.obj j⋆` (one point per element of `s`) whose image under `ι_{j⋆}` is exactly `s`. This is the "factors through some stage" conclusion.

Steps (a)–(c) together give: `s` is the image under `ι_{j⋆}` of a `< κ`-sized subset of `D.obj j⋆`, which is precisely the statement that `P_κ.obj C` is the filtered colimit of `P_κ.obj (D.obj j)`, i.e. `P_κ` preserves this colimit.

**Dependency flag:** Mathlib has general accessible-functor infrastructure (`CategoryTheory.Presentable` line of work) but likely nothing specialized to bounded powerset. Lemma 1.2 is probably a genuine new proof, not a lookup — and per the unbundling above, step (b)/(c) (the filtered-category upper-bound property for `< κ`-sized subsets) is the specific sub-fact worth checking against Mathlib's `IsCardinalFiltered` API (if present) before reproving from scratch.

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

**[REVISED] Pin the exact statement before building on it.** The original draft stated this axiom informally and flagged it as high-risk without specifying which of several nonequivalent textbook formulations was intended. Before any downstream formalization proceeds, the statement below should be checked line-by-line against a specific citable source (e.g. Worrell, *"On the final sequence of a finitary set functor"*, and its κ-ary generalization surveyed in Adámek–Milius–Moss's coalgebra text) — in particular the exact bound on the stabilization ordinal, since different sources give `α ≤ κ`, `α ≤ κ⁺`, or a bound stated via the accessibility rank of `F` rather than `κ` directly, and these are *not* interchangeable substitutions in the proof below.

The version we adopt, stated as precisely as we can make it prior to that check:

```lean
axiom stabilization_theorem
    (F : Type u ⥤ Type u) (κ : Cardinal) (hκ : κ.IsRegular) (hκ_inf : κ.IsInfinite)
    (hacc : PreservesFilteredColimitsOfSize κ F)
    (hbdd : ∀ X, ∀ y : F.obj X, ∃ s : Set X, Cardinal.mk s < κ ∧ y ∈ F.map (Subtype.val) '' (F.obj s ...)) :
      -- hbdd formalizes "F is bounded by κ": every element of F.obj X is supported
      -- on a subset of X of size < κ. For P_κ this holds tautologically by
      -- construction (every value has cardinality < κ), but the hypothesis is
      -- stated generally here so the theorem can be reused for other functors
      -- in later workstreams (flagged in §8).
    ∃ α : Ordinal, α ≤ κ.ord ∧ IsIso (finalSeq.connectingMap F (α+1) α)
```

with a TODO to replace the axiom with an actual formalized proof (this is genuinely nontrivial ordinal-induction combinatorics — likely the single most expensive sub-formalization in WS1, and should be budgeted as such rather than assumed cheap). **[REVISED]** Given the bound-pinning concern above, the TODO is upgraded to a two-step task: (i) fix the precise statement against a written source *before* any Lean work begins on it, since a wrong bound here would let everything downstream typecheck against a false external fact without any local proof ever catching the error; (ii) only then attempt the formalization.

**Corollary 2.2.** Setting `U := finalSeq F α` for the stabilizing `α`, the structure map `U → F.obj U` (inverse of the iso from 2.1) makes `U` a coalgebra, and it is **terminal** in `Coalg F`.

**[REVISED] Uniqueness argument, expanded — this is re-ranked as comparable risk to Theorem 2.1, not a free corollary.** The original draft called the direction "stabilized limit ⇒ terminal coalgebra" a "short argument." On inspection it is short *conceptually* (any coalgebra `(X, ξ)` maps into `finalSeq F α` by transfinite recursion, and the cone map is unique) but the formalization has the same shape of difficulty as Theorem 2.1 itself: both are transfinite inductions whose correctness depends on carrying a uniqueness invariant through limit stages, not just successor stages. Spelled out:

*Existence of the cone map* `h : X → finalSeq F α`, by transfinite recursion on `β ≤ α`, building `h_β : X → finalSeq F β` simultaneously with a proof that each `h_β` commutes with the connecting maps:
- `h_0 : X → PUnit` is the unique map to a point.
- `h_{β+1} : X → F.obj (finalSeq F β) := F.map h_β ∘ ξ` (using the coalgebra structure `ξ : X → F.obj X`).
- At a limit stage `λ`, `h_λ : X → lim_{β<λ} finalSeq F β` is the map into the limit induced by the compatible family `(h_β)_{β<λ}` — compatible because each earlier stage's commuting-square proof was carried along in the recursion.

*Uniqueness of the cone map*, which is the part actually needed for **terminality** (not just "a fixed point exists," which existence alone would give): suppose `h, h' : X → finalSeq F α` both commute with structure maps at every stage. We must show `h = h'` by transfinite induction on `β ≤ α`, proving `h_β = h'_β` (the restrictions/projections to stage `β`) simultaneously:
- Base case `β = 0`: both maps into `PUnit` are equal trivially.
- Successor case: given `h_β = h'_β`, the defining equation `h_{β+1} = F.map h_β ∘ ξ = F.map h'_β ∘ ξ = h'_{β+1}` follows by congruence — this step *is* genuinely short, using only functoriality of `F`.
- **Limit case, the step that actually carries the weight**: given `h_β = h'_β` for all `β < λ`, conclude `h_λ = h'_λ`. This requires the universal property of the limit at stage `λ` (two maps into a limit are equal iff they agree after composing with every projection), which is exactly Mathlib's `Limits.IsLimit` uniqueness API applied at each limit ordinal in the transfinite recursion — meaning this is not a single invocation but a use of the limit's uniqueness property *once per limit ordinal below `α`*, packaged inside an outer transfinite induction. This is the same order of difficulty as the stabilization theorem's own ordinal bookkeeping, and should be budgeted accordingly rather than treated as free once Theorem 2.1 is in hand.

This discharges **failure mode (i)** for C1: existence is not assumed, it's derived from regularity of `κ` plus the general shape theorem, with the one external black box clearly labeled — and its companion uniqueness argument now flagged at comparable cost rather than bundled in as an afterthought.

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

**[NEW] Lemma 3.1a (`P_κ` preserves weak pullbacks).** For any pair of functions `f : X → Z`, `g : Y → Z`, the canonical comparison map
```
P_κ.obj (weak pullback of f, g) → weak pullback of (P_κ.map f, P_κ.map g)
```
is surjective (this is what "preserves weak pullbacks" means: the functor need not send the pullback *square* to a pullback square on the nose, only surjectively onto the pulled-back pairs).

*Proof.* Concretely, a weak pullback of `f, g` at the level of sets is `{(x,y) : X × Y // f x = g y}`, and its image in `X × Y` under the evident inclusion. Given `s ∈ P_κ.obj X` and `t ∈ P_κ.obj Y` with `P_κ.map f s = P_κ.map g t` (i.e. `f '' s = g '' t` as elements of `P_κ.obj Z`, so as sets), we must exhibit `r ∈ P_κ.obj (weak pullback X Y)` mapping to `(s, t)`. Since `f '' s = g '' t`, every `z` in this common image has a preimage `x_z ∈ s` and a preimage `y_z ∈ t`; choosing one pair `(x_z, y_z)` per `z` (a choice over a set of size `< κ`, so the resulting set of pairs has size `< κ` by the same cardinality bookkeeping as `image_card_lt`) gives a set `r` of pairs `(x_z, y_z)` with `f x_z = g y_z`, whose first-coordinate image is `s` (every element of `s` appears as some `x_z` by construction, since we chose one such `x_z ∈ s` for every `z` in the common image, and that common image equals `f '' s`) and whose second-coordinate image is `t` similarly. Hence `r` witnesses the weak pullback property, and `Cardinal.mk r < κ` since `r` is indexed by (a subset of) the common image, itself of size `< κ` as a subset of `s`'s image. ∎

**Why this is needed, made explicit (this was a parenthetical in the original draft):** Lemma 3.1's transitivity clause — "relation-composition of two bisimulations is a bisimulation" — is exactly an instance of weak-pullback preservation: given bisimulations `R` (on `X, Y`) and `S` (on `Y, Z`) exhibited by coalgebra structures on their graphs with projections `p_1, p_2` and `q_1, q_2` respectively, the relational composite `R ; S` is witnessed by taking a weak pullback of `p_2 : Graph(R) → Y` against `q_1 : Graph(S) → Y`, and Lemma 3.1a is precisely what supplies a coalgebra structure on (a `< κ`-bounded model of) that weak pullback making the two outer projections coalgebra morphisms. Without Lemma 3.1a stated and proved on its own, Lemma 3.1's transitivity claim is unjustified for a functor chosen without this property — it is not automatic for general `F`, and is worth its own line in the dependency table (§7) rather than living inside a proof aside.

**Lemma 3.1** (transitivity now cites 3.1a directly). `bisimEquiv` is itself an equivalence relation (reflexive: diagonal is a bisimulation; symmetric: swap is a bisimulation; transitive: relation-composition of two bisimulations is a bisimulation, **by Lemma 3.1a** applied to the two witnessing coalgebra structures as above).

### 3.2 Terminal ⇒ bisimilarity is equality

**Theorem 3.2 (the actual content of `bisim_eq`).** In the terminal coalgebra `U`, `bisimEquiv = (· = ·)`.

*Proof:* `(⊇)` is Lemma 3.1's reflexivity. `(⊆)`: suppose `R` is a bisimulation on `U`. The subobject `{p // R p.1 p.2} ↪ U × U` carries a coalgebra structure with both projections as coalgebra morphisms. By terminality, both projections equal the *unique* map into `U`, hence agree — so `R p.1 p.2 → p.1 = p.2`.

This is where terminality is doing *all* the work, and it's worth stating as its own named theorem since C2 and later workstreams cite "bisimilarity is equality" far more often than they cite terminality directly.

**This directly rules out failure mode (ii):** collapse to a point would require a bisimulation relating *every* pair, and by 3.2 that would force `U` to have at most one element — which is refuted separately by:

### 3.3 Non-degeneracy (≥ 2 elements)

Needs an actual witness. Take two coalgebras with provably non-bisimilar roots:
- `A`: single-node graph with the empty relation (`a ↦ ∅`).
- `B`: single-node graph looping to itself (`b ↦ {b}`).

Map each into `U` via the unique coalgebra morphism (terminality), get `image(a), image(b) : U`. If these were bisimilar in `U`, pulling back along the two morphisms would exhibit `A` and `B` themselves as bisimilar as coalgebras (bisimilarity reflects along coalgebra morphisms into a common terminal object — a short lemma, "bisimulation pullback," worth stating once), contradicting a direct check that `a ↦ ∅` and `b ↦ {b}` cannot be related by any bisimulation.

**[REVISED] The direct check, spelled out in full (the original draft compressed this to "by unfolding the bisimulation condition one step," which elides a real argument):**

*Claim:* no bisimulation `R : A × B → Prop` (equivalently, no bisimulation on `A ⊕ B` relating `a` and `b`) can hold `R a b`.

*Proof.* Suppose toward contradiction that `R` is a bisimulation with `R a b`, witnessed by a coalgebra structure `ζ` on `Graph(R) := {p : A × B // R p.1 p.2}` making both projections `π_A, π_B` coalgebra morphisms. Since `R a b` holds, `(a,b) ∈ Graph(R)`, so `ζ (a,b) ∈ P_κ.obj (Graph(R))` is some `< κ`-sized set of pairs, say `w`. Coalgebra-morphism-ness of `π_A` gives
```
struct_A a = P_κ.map π_A (ζ (a,b)) = π_A '' w.
```
But `struct_A a = ∅` by definition of `A`, so `π_A '' w = ∅`, which (since image of a set is empty iff the set itself is empty) forces `w = ∅`. Now apply coalgebra-morphism-ness of `π_B`:
```
struct_B b = P_κ.map π_B (ζ (a,b)) = π_B '' w = π_B '' ∅ = ∅.
```
But `struct_B b = {b} ≠ ∅` by definition of `B` (this uses `hκ_inf`: a singleton has cardinality `1 < κ`, so `{b}` is a genuine, non-vacuous element of `P_κ.obj B`, hence `struct_B b ≠ ∅` as elements of `P_κ.obj B`, i.e. as *sets* — `{b} ≠ ∅`). Contradiction. Hence no such `R` exists, i.e. `a` and `b` are not bisimilar in `A ⊕ B`. ∎

This is the fact needed to conclude, via the bisimulation-pullback lemma, that `image(a) ≠ image(b)` in `U` — establishing `GroundlessCarrier`'s intended non-degeneracy.

### 3.4 Surjectivity of `struct` (no atom leakage — failure mode iii)

`struct : U ≅ P_κ.obj U` is already an iso by Lambek (§2.3), so surjectivity is automatic, *not* a separate proof — this is worth flagging explicitly as a place where C1's architecture is stronger than it looks: fixing the iso in `GroundlessCarrier` already forecloses failure mode (iii) as a corollary of Lambek, with zero extra work. Record this as a one-line remark rather than a new lemma, so nobody in later workstreams goes looking for a nonexistent separate surjectivity proof.

---

## 4. Constructing `Ω`

```
Definition (omegaCoalg) : Coalg P_κ on carrier `PUnit`,
  structure map `∗ ↦ ⟨{∗}, (card {∗} = 1 < κ since hκ_inf)⟩`
```

**[REVISED]** The cardinality bound `{∗}` has size `1 < κ` is now justified directly by the standing hypothesis `hκ_inf` (κ infinite), per §1.1's note, rather than derived from regularity at this point of use.

```
Definition (Ω) := (the unique coalgebra morphism omegaCoalg → U) applied to `∗`
```

**Theorem 4.1 (`omega_selfsingleton`).** `struct Ω = ⟨{Ω}, _⟩`.

*Proof:* Let `h : PUnit → U` be the unique coalgebra morphism. Coalgebra-morphism-ness means `struct (h ∗) = P_κ.map h (⟨{∗}, _⟩) = ⟨h '' {∗}, _⟩ = ⟨{h ∗}, _⟩`. Substitute `Ω := h ∗`.

This is a two-line proof *given* the terminal coalgebra machinery — the entire weight sits upstream in §2–3, which is the intended shape: `Ω`'s existence should feel almost free once finality is secured, since "define by unique coalgebra morphism out of the obvious one-node self-loop" is the generic recipe for *any* self-referential definition, not a bespoke trick for `Ω` alone. This generic recipe is exactly what gets extracted and reused in C2.

---

## 5. Assembling `GroundlessCarrier` (C1's target theorem)

```lean
theorem ws1_C1 (hκ_reg : κ.IsRegular) (hκ_inf : κ.IsInfinite) :
    Nonempty (GroundlessCarrier (κ := κ)) := by
  obtain ⟨α, hα, hiso⟩ := stabilization_theorem PkFunctor κ hκ_reg hκ_inf (accessibility_lemma hκ_reg hκ_inf) hbdd_tautological
  let U := finalSeq PkFunctor α
  exact ⟨{ U := U
         , final := terminality_of_stabilized_limit hiso   -- §2.2 Corollary 2.2
         , struct := lambek_iso final                       -- §2.3
         , bisim_eq := bisim_eq_of_terminal final            -- §3.2
         , nondegenerate := nondegenerate_of_terminal final  -- §3.3, [NEW] field
         , omega := omega_def final                          -- §4
         , omega_selfsingleton := omega_thm final             -- §4.1
         }⟩
```

**[REVISED]** `GroundlessCarrier` now carries a `nondegenerate : ∃ a b : U, a ≠ b` field directly (see below), discharged by §3.3, rather than being left as an unenforced gap noted only in the closing "open issues" section. The original draft flagged this as something to "recommend adding... before other workstreams start citing the structure" — this revision makes that patch part of the structure as assembled here, so no downstream workstream can cite `GroundlessCarrier` before the amendment lands.

```lean
structure GroundlessCarrier (κ : Cardinal) where
  U : Type u
  final : IsTerminal (Coalg.mk U struct)
  struct : U ≃ P_κ.obj U
  bisim_eq : ∀ (R : U → U → Prop), Bisim P_κ R → ∀ x y, R x y → x = y
  nondegenerate : ∃ a b : U, a ≠ b          -- [NEW]
  omega : U
  omega_selfsingleton : struct omega = ⟨{omega}, _⟩
```

---

## 6. C2: the Solution Lemma, built on top of C1

C2 is where the payoff of having gone through *terminality* (rather than some weaker fixed-point statement) shows up, because uniqueness of solutions is uniqueness of the cone map, verbatim reused from §2.2.

### 6.1 Systems as coalgebras on `I ⊕ U`

Given `e : I → P_κ.obj (I ⊕ U)`, build a coalgebra structure on `I ⊕ U`:

**[REVISED]** The original draft's `structMap` clause for the `inl` branch read `P_κ.map (id ⊕ ...) applied to (e i)`, suggesting a nontrivial reindexing map was being applied. Since `e i : P_κ.obj (I ⊕ U)` **already**, no such map is needed or well-typed as a separate step — the `inl` branch is definitionally just `e i`. This is corrected below.

```
Definition (systemCoalg e).
  carrier := I ⊕ U
  structMap : I ⊕ U → P_κ.obj (I ⊕ U)
    | inl i => e i                                        -- [REVISED] direct; e i is already
                                                            -- valued in P_κ.obj (I ⊕ U), no
                                                            -- reindexing map exists or is needed
    | inr u => P_κ.map Sum.inr (struct u)                  -- push U's own coalgebra structure
                                                            -- along inr : U → I ⊕ U
```

The `inr` branch uses `P_κ.obj U → P_κ.obj (I ⊕ U)` via `P_κ.map Sum.inr` composed with the existing `struct : U → P_κ.obj U` — routine functoriality, but stated as its own definitional step since getting the two branches of this coalgebra to typecheck consistently is the fiddly part of the whole construction. With the `inl` branch corrected to `structMap ∘ inl = e` (an equation, not an application of some further map), the two branches now visibly agree in type: both produce elements of `P_κ.obj (I ⊕ U)`, the first directly by hypothesis on `e`, the second by `P_κ.map Sum.inr` applied to `struct u : P_κ.obj U`.

**Lemma 6.1.** `systemCoalg e` is a well-defined `P_κ`-coalgebra (the two branches agree on typing — now immediate from the corrected definition above — and boundedness `< κ` is preserved: inherited from `e i`'s own bound in the `inl` case, and from `image_card_lt` applied to `struct u`'s bound in the `inr` case).

### 6.2 Extracting the solution

By terminality of `U` (§2.2), there is a **unique** coalgebra morphism `h : I ⊕ U → U` from `systemCoalg e`. Define `sol := h ∘ inl : I → U`.

**[NEW] Lemma 6.1a (`inr` is a coalgebra morphism, and consequently `h ∘ inr = id`).** Before stating Theorem 6.2, we isolate the fact the original draft compressed into a single parenthetical ("the latter because... forcing it to be the identity by the same terminal-endomorphism argument as Lambek's lemma") into its own two-part lemma, since it is used explicitly in the proof below.

*Part 1: `inr : U → I ⊕ U` is a coalgebra morphism* `(U, struct) → (I ⊕ U, systemCoalg e)`. This is exactly the defining equation of the `inr` branch of `structMap` above: `structMap ∘ inr = P_κ.map Sum.inr ∘ struct`, which is precisely the naturality square required for `inr` to be a coalgebra morphism.

*Part 2: hence `h ∘ inr : U → U` is a coalgebra endomorphism of `(U, struct)`* (composite of coalgebra morphisms `inr` then `h` is a coalgebra morphism, and its source and target both equal `(U, struct)`). By terminality of `(U, struct)` in `Coalg P_κ`, the **unique** coalgebra endomorphism of the terminal object is the identity (this is the identical terminal-endomorphism-uniqueness fact used in Lambek's lemma, §2.3 — cited here rather than reproved). Hence `h ∘ inr = id`.

**Theorem 6.2 (existence half of `ws1_C2_solutionLemma`).** `sol` satisfies the defining equation: `struct (sol i) = (Sum.elim sol id) '' (e i).val`.

*Proof:* Coalgebra-morphism-ness of `h` gives
```
struct (h (inl i)) = P_κ.map h (structMap (inl i)) = P_κ.map h (e i) = h '' (e i).val.
```
(This uses the corrected `inl` branch directly — `structMap (inl i) = e i`, no intermediate reindexing map to unwind.) It remains to identify `h '' (e i).val` with `(Sum.elim sol id) '' (e i).val`, i.e. to show `h` and `Sum.elim sol id` agree pointwise on `(I ⊕ U)`. On `inl`-values: `h (inl i') = sol i'` by definition of `sol`. On `inr`-values: `h (inr u) = u` by Lemma 6.1a Part 2. So `h = Sum.elim sol id` as functions on `I ⊕ U`, giving the claimed equation.

**Theorem 6.3 (uniqueness half).** If `sol'` also satisfies the equation, then `Sum.elim sol' id` is a coalgebra morphism `systemCoalg e → U`, and by *terminality* there is only one such morphism, namely `h`; hence `sol' = h ∘ inl = sol`.

This is the cleanest illustration of why C1 had to deliver *terminality* and not merely "a fixed point exists": uniqueness in C2 is a direct corollary of uniqueness in the universal property, with no extra combinatorial argument needed. If C1 only produced *a* coalgebra `U` with `struct` merely an isomorphism (Lambek can hold for non-terminal fixed points too, in general categories — though not for `P_κ` on `Type u` specifically, this is worth flagging as a reason the design insists on the stronger statement) uniqueness would need a wholly separate proof, likely by a bisimulation argument identifying any two candidate solutions — strictly more work, and exactly the kind of hidden cost the "identity vs existence" tension in the cross-cutting trade-offs section is pointing at.

### 6.3 Recovering `Ω` as a special case

Set `I := Unit`, `e := fun _ => ⟨{Sum.inl ()}, _⟩`. Then `systemCoalg e` restricted to behavior at `()` reproduces exactly `omegaCoalg` from §4 up to relabeling.

**[REVISED] The consistency check, given as an actual gluing lemma rather than "either can serve as base case."** The original draft treated the agreement `sol () = Ω` as something either construction could serve to derive the other from, interchangeably. On inspection this needs an explicit argument, because `omegaCoalg`'s anamorphism target is a direct map `PUnit → U` out of a coalgebra *on `PUnit`*, whereas `sol` is extracted from a map `Unit ⊕ U → U` out of a coalgebra on the sum type `Unit ⊕ U` — these are morphisms with different sources, and "the same `Ω`" requires relating them explicitly.

**Lemma 6.4 (Ω-consistency).** `sol () = Ω` (with `sol` from §6.2 applied to this specific `I, e`, and `Ω` from §4).

*Proof.* Let `h : Unit ⊕ U → U` be the unique coalgebra morphism from `systemCoalg e` (§6.2), and let `h_Ω : PUnit → U` be the unique coalgebra morphism from `omegaCoalg` (§4), so `Ω = h_Ω ∗` by definition. Consider the composite
```
k := h ∘ inl : PUnit → U
```
(identifying `Unit ≅ PUnit`). We claim `k` is *itself* a coalgebra morphism `omegaCoalg → U`: by Theorem 6.2's proof pattern applied to this specific `e`, `struct (h (inl ())) = h '' (e ()).val = h '' {inl ()} = {h (inl ())} = {k ()}`, which is exactly the naturality square required of a coalgebra morphism `omegaCoalg → (U, struct)` (since `omegaCoalg`'s structure map sends `∗ ↦ {∗}`, and we need `struct (k ∗) = P_κ.map k {∗} = {k ∗}`, which is what was just shown). By **terminality of `U` in `Coalg P_κ`**, there is a *unique* coalgebra morphism `omegaCoalg → U`; since both `k` and `h_Ω` are coalgebra morphisms `omegaCoalg → U`, uniqueness forces `k = h_Ω`, hence `k ∗ = h_Ω ∗`, i.e. `sol () = h (inl ()) = k ∗ = h_Ω ∗ = Ω`. ∎

This closes the loop the source document flags explicitly ("specializing `I = Unit`... recovers `Ω = {Ω}`") with an actual proof rather than an assertion of interchangeability, and gives a genuine regression test once both constructions are formalized: Lemma 6.4 is the statement to check, and it is *not* free — it uses terminality's uniqueness clause exactly once, applied to the pair `(k, h_Ω)`.

---

## 7. Dependency graph summary

```
Lemma 1.1 (functoriality)
Lemma 1.2 (κ-accessibility, steps a/b/c) ──┐
                              ├──▶ Theorem 2.1 (stabilization, PINNED statement) ─▶ Corollary 2.2 (terminality,
[stabilization_theorem, EXTERNAL,          │                                        existence + uniqueness,
 exact bound to be checked against source] ┘                                        BOTH costed as high-risk)
                                                                        │
                                                                        ├─▶ Lemma 2.3 (Lambek iso)
                                                                        │        │
                                                                        │        ▼
                                                                        │   §3.4 surjectivity (free)
                                                                        │
                                                Lemma 3.1a (P_κ preserves weak pullbacks) [NEW]
                                                                        │
                                                                        ├─▶ Lemma 3.1 (bisim is equiv. rel.,
                                                                        │        transitivity cites 3.1a)
                                                                        │        │
                                                                        │        ▼
                                                                        ├─▶ Theorem 3.2 (bisim = eq)
                                                                        │        │
                                                                        │        ▼
                                                                        ├─▶ §3.3 non-degeneracy (full unfolding)
                                                                        │        │
                                                                        │        ▼
                                                                        │   nondegenerate FIELD of GroundlessCarrier
                                                                        │
                                                                        ├─▶ §4 Ω construction ─▶ Theorem 4.1
                                                                        │
                                                                        ▼
                                                              ws1_C1 (assembled, with nondegenerate field)
                                                                        │
                                                                        ▼
                                            §6.1 systemCoalg (corrected inl branch)
                                                    + Lemma 6.1a (inr is coalgebra morphism, h∘inr = id)
                                                                        │
                                                                        ▼
                                                        §6.1–6.2 systemCoalg + uniqueness
                                                                        │
                                                                        ▼
                                                        ws1_C2_solutionLemma
                                                                        │
                                                                        ▼
                                              Lemma 6.4 Ω-consistency (explicit gluing proof, not free)
```

**External imports, ranked by risk. [REVISED ranking — Corollary 2.2's uniqueness clause is promoted to the same tier as Theorem 2.1 itself, and Lemma 3.1a is added as a newly-named dependency.]**
1. **`stabilization_theorem`** (§2.1, Theorem 2.1) — highest risk; likely not in Mathlib in this generality, genuinely nontrivial ordinal induction. **Before formalization, its exact statement (in particular the stabilization bound `α ≤ κ.ord` vs. alternatives) must be checked against a specific citable source**, since the axiom's precise quantifiers are load-bearing for everything downstream and a subtly wrong bound would not be caught by any local proof.
2. **Corollary 2.2's uniqueness-of-cone-map argument** (§2.2) — **[REVISED] promoted from "short argument" to comparable risk with item 1.** The limit-stage case of the transfinite induction invokes the limit's universal property once per limit ordinal below the stabilization ordinal, nested inside an outer transfinite induction; this is genuine ordinal-induction work, not a corollary that comes for free once Theorem 2.1 is available.
3. **Lemma 3.1a (`P_κ` preserves weak pullbacks)** — **[NEW]** previously an unstated parenthetical inside Lemma 3.1's proof; now a named lemma in its own right, needed for transitivity of bisimilarity. Moderate risk: the proof given above is elementary (a choice argument over a `< κ`-sized index set) but should be checked carefully for the `Cardinal.mk` bookkeeping, similar in flavor to `image_card_lt`.
4. Completeness of `Type u` for computing the limit stage of the terminal sequence (§2.1) — should already be in Mathlib, low risk.
5. General terminal-object uniqueness API (`IsTerminal`, used repeatedly in §2.2, §3.2, §6.1a, §6.3) — standard Mathlib category theory, low risk.
6. Cardinal arithmetic for regular cardinals (`κ`-filtered colimits absorb `< κ`-indexed data) — partially in Mathlib's cardinal file, but the filtered-colimit-specific packaging (Lemma 1.2, step b/c) likely needs local glue code.

---

## 8. What this design leaves open for later workstreams

- The concrete value of `κ` is left schematic throughout (now explicitly as an *infinite regular* cardinal, per §1.1's standing hypothesis), per the source document's mandate; every theorem above is stated "for `κ` infinite regular," deferring the Goldilocks choice to WS7 as instructed.
- **[RESOLVED, was previously flagged as a gap]** `GroundlessCarrier` now includes the `nondegenerate : ∃ a b : U, a ≠ b` field directly (§5), discharged by §3.3's fully-unfolded proof, so the structure can no longer be vacuously satisfied by a one-point coalgebra. This amendment is folded into the structure as given in this revision, rather than left as a note for a future patch.
- C3 (graph/decoration) and C6 (explicit final-sequence) are not built here but are compatible cross-checks: C6's finalSeq machinery is in fact *reused directly* in this design (§2.1), so formalizing C6 fully is nearly free once C1 is done — worth noting as an efficient next step rather than genuinely independent validation.
- **[NEW]** The `stabilization_theorem` axiom (§2.2) is stated with a general `hbdd` hypothesis (boundedness of `F` by `κ`, in the sense that every element of `F.obj X` is supported on a `< κ`-sized subset of `X`) rather than one hardcoded to `P_κ`, specifically so that later workstreams needing final coalgebras of *other* `κ`-bounded functors (should any arise) can reuse Theorem 2.1 without restating it. This is a design choice, not a correctness issue, but worth flagging so nobody duplicates the stabilization theorem for a second functor unnecessarily.
- Before any Lean work begins on Theorem 2.1, the bound-pinning task described in §2.2 (checking the axiom's exact statement against Worrell/Adámek–Koubek/Adámek–Milius–Moss) should be treated as its own scoped sub-task with its own sign-off, separate from and prior to the formalization effort itself.
