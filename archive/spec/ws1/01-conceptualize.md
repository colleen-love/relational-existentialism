# WS1 Obligation: The Groundless Carrier

## What is at stake

The object at stake is a **carrier for reflexive, relation-only entities**: a class or set of "objects" each of which is exhausted by (identical to) its collection of outgoing relations, with (a) at least one non-trivially self-involved inhabitant (e.g. a solution to `x = {x}`), (b) no atoms/urelements terminating any membership descent, and (c) a canonical identity criterion under which such objects are counted the same iff they have the same relational structure (bisimulation).

**Non-triviality.** In a well-founded ambient (ZF + Foundation) the ∈-relation admits no infinite descending chains and no `x` with `x ∈ x`; the intended inhabitants provably do not exist. So WS1 cannot be discharged inside standard foundations — it requires either a genuinely non-well-founded set theory, or a categorical/coalgebraic surrogate whose "elements" are behaviors rather than iterated-membership sets. The three requirements pull against each other: existence of self-involved objects (anti-foundation) versus a set-sized (not proper-class) carrier (Cantor/Lambek obstruction) versus a canonical identity that neither collapses everything to one point nor leaves bisimilar objects distinct. WS1 is the base-camp obligation: everything downstream quantifies over this carrier, so its existence and identity criterion must be pinned first, and the encoding choice constrains all later workstreams.

Below, 𝒰 denotes the intended carrier; ≈ denotes bisimilarity.

---

## Candidate framings

### C1 — Hyperset universe as final coalgebra of bounded powerset (Aczel/Barwise–Moss route)

**Ambient theory.** ZFC⁻ + AFA, encoded in Lean not by re-axiomatizing set theory but by taking the carrier to be the final coalgebra of the κ-bounded powerset functor `P_κ` on `Type u`. AFA is *modeled*, not assumed: bisimulation-as-equality is the defining property of finality, which is Aczel's theorem in coalgebraic dress.

**Framing of the obligation.** 𝒰 := `νP_κ` exists as a type; its structure map `νP_κ → P_κ (νP_κ)` is an isomorphism (Lambek); bisimilarity on `νP_κ` is propositional equality; there exists a fixed point of the "singleton-of-self" endo-operation witnessing `Ω ≈ {Ω}`.

**Proof strategy.** Bound branching by an inaccessible/regular `κ` so `P_κ` is `κ`-accessible ⇒ final coalgebra exists (terminal-sequence / accessible-functor theorem). Lambek's lemma gives the iso. Coinduction principle of `νP_κ` gives bisimulation = equality. Construct `Ω` as the anamorphism `unfold (fun _ => {∗}) ∗` on a one-point coalgebra `∗ ↦ {∗}`; verify it is its own singleton.

**Lean 4 signature.**
```lean
variable {κ : Cardinal.{u}} (hκ : κ.IsRegular)

def PkFunctor (κ : Cardinal.{u}) : Type u ⥤ Type u := -- κ-bounded powerset

structure GroundlessCarrier where
  U        : Type u
  final    : IsTerminal (CategoryTheory.Coalgebra.of (PkFunctor κ) U)
  struct   : U ≃ {s : Set U // Cardinal.mk s < κ}        -- Lambek iso
  bisim_eq : ∀ x y : U, Bisim (PkFunctor κ) x y ↔ x = y
  omega    : U
  omega_selfsingleton : struct omega = ⟨{omega}, by decide⟩   -- Ω = {Ω}

theorem ws1_C1 (hκ : κ.IsRegular) : Nonempty (GroundlessCarrier (κ := κ))
```

**Success condition.** `GroundlessCarrier` inhabited for some regular `κ ≥ ℵ₁`; `omega` provably distinct from a base object, so the carrier is non-degenerate.

**Failure modes.** (i) *Non-existence*: no regular `κ` makes `P_κ` accessible with a set-sized final coalgebra (would refute the accessible-functor machinery — unexpected). (ii) *Collapse*: `bisim_eq` holds but `νP_κ` turns out to be a single point (excluded once branching ≥ 2 is realized, but must be checked, not assumed). (iii) *Atom leakage*: the iso `struct` is not surjective, i.e. some subsets below `κ` are not realized, breaking "object = its relations."

---

### C2 — Solution-lemma framing (systems of equations, Barwise–Moss)

**Ambient theory.** Same carrier 𝒰 = `νP_κ`, but the obligation is cashed as the **Solution Lemma**: every "flat system" of equations `xᵢ = {terms in xⱼ and atoms}` has a unique solution in 𝒰. This is the working form of AFA that downstream WS3/WS5 actually invoke when they *define* objects by self-reference.

**Framing.** For any index type `I` and any system `e : I → P_κ (I ⊕ U)`, there is a unique `sol : I → U` making the substitution square commute.

**Proof strategy.** Reduce the system to a coalgebra on `I ⊕ U`, take the unique coalgebra morphism into the final coalgebra (finality), restrict to `I`. Uniqueness is finality's uniqueness.

**Lean 4 signature.**
```lean
theorem ws1_C2_solutionLemma
    (hκ : κ.IsRegular) (U : Type u) [FinalCoalgebra (PkFunctor κ) U]
    {I : Type u} (e : I → {s : Set (I ⊕ U) // Cardinal.mk s < κ}) :
    ∃! sol : I → U,
      ∀ i, (struct (sol i)).val
            = (Sum.elim sol id) '' (e i).val
```

**Success condition.** Existence *and* uniqueness of `sol` for all systems; specializing `I = Unit, e = fun _ => {inl ()}` recovers `Ω = {Ω}`.

**Failure modes.** (i) *No uniqueness*: two distinct solutions ⇒ carrier is not final / AFA fails ⇒ identity criterion underdetermined. (ii) *No existence*: some system unsolvable ⇒ carrier too small (missing objects the reification in WS2/WS3 needs).

**Trade-off vs C1.** C1 proves the carrier *is* the right thing; C2 proves it *does* the right work. C2 is more directly reusable as a BR-level lemma but presupposes C1's existence.

---

### C3 — Graph/decoration framing (Aczel's original picture)

**Ambient theory.** 𝒰 = pointed graphs (`nodes : Type u`, `edges : nodes → Set nodes`, `root`) quotiented by bisimilarity; AFA becomes: every graph has a unique decoration into 𝒰.

**Framing.** The map `decoration : APG → U` (accessible pointed graphs to carrier) exists, is surjective, and identifies exactly bisimilar graphs.

**Proof strategy.** Define bisimilarity as the greatest bisimulation (coinductive), quotient, show the quotient carries a `P_κ`-coalgebra structure and is final among APGs. Decoration = the canonical map to the quotient.

**Lean 4 signature.**
```lean
structure APG where
  N    : Type u
  edge : N → Set N
  root : N

def Bisimilar : APG → APG → Prop := -- greatest bisimulation on rooted graphs

theorem ws1_C3_decoration :
    ∃ (U : Type u) (dec : APG → U),
      Function.Surjective dec ∧
      (∀ g h, dec g = dec h ↔ Bisimilar g h)
```

**Success condition.** Surjectivity (every carrier element is *some* graph's picture ⇒ no hidden atoms) plus the exact-bisimilarity biconditional.

**Failure modes.** (i) *Kernel too coarse*: `dec g = dec h` for non-bisimilar `g,h` ⇒ over-identification (structural collapse). (ii) *Kernel too fine*: bisimilar graphs stay distinct ⇒ wrong identity criterion, AFA fails. (iii) Surjectivity fails ⇒ carrier has elements with no relational picture (atoms).

**Trade-off.** Most faithful to the intended metaphysics ("object = its picture") and cardinality-transparent, but the coinductive bisimilarity machinery is the heaviest to formalize.

---

### C4 — Existence of a nontrivial self-involved object only (minimal framing)

**Ambient theory.** Any category `C` with a `P_κ`-style functor `F` such that `νF` exists; obligation weakened to: `νF` contains a point `x` with `x ≈ F`-unfolds-to-something-containing-`x`, and `νF` is not terminal-object-trivial.

**Framing.** Provide one witness of genuine self-reference and one proof of ≥ 2 distinct behaviors. This isolates the *irreducible* content of WS1 from the full AFA package.

**Proof strategy.** Anamorphism for the witness; exhibit two coalgebras with no bisimulation between their roots (e.g. `∅`-object vs `Ω`) and push through finality to distinctness.

**Lean 4 signature.**
```lean
theorem ws1_C4_minimal
    (F : Type u ⥤ Type u) (U : Type u) [FinalCoalgebra F U] :
    (∃ x : U, SelfInvolved F x) ∧ (∃ a b : U, a ≠ b)
```
where `SelfInvolved F x` asserts `x` appears in its own unfolding (formalized via the structure map and a reachability relation).

**Success condition.** Both conjuncts hold.

**Failure modes.** (i) `∀ x, ¬ SelfInvolved x` ⇒ carrier is secretly well-founded (Foundation smuggled back in). (ii) `∀ a b, a = b` ⇒ full structural collapse.

**Trade-off.** Cheapest to prove, weakest guarantee; good as an early sanity milestone but does *not* by itself give the identity criterion downstream needs.

---

### C5 — Type-theoretic coinductive encoding (no set theory at all)

**Ambient theory.** No ZFC/AFA. Carrier is a coinductive/`M`-type over the finite-or-`κ`-multiset container; "sets" become quotients of `M`-types by bisimilarity (or QIITs/setoid). This trades set-theoretic axioms for type-theoretic ones (needs impredicative/`Prop` or quotient support).

**Framing.** `M`-type `M (P_κ)` exists; equip with setoid `≈`; the quotient is a final `P_κ`-coalgebra internally; `Ω` is a corecursive definition.

**Proof strategy.** `M`-types are Lean-native (`CoInductive`); bisimilarity coinductively; use `Quotient` (or work in the bisimulation setoid) to get equality = bisimilarity by construction; `Ω` by `corec`.

**Lean 4 signature.**
```lean
codata MTree (κ : Cardinal.{u}) where
  node : {s : Set (MTree κ) // Cardinal.mk s < κ} → MTree κ

def BisimSetoid (κ) : Setoid (MTree κ) := ⟨Bisim, bisim_equiv⟩
abbrev U (κ) := Quotient (BisimSetoid κ)

theorem ws1_C5_typeTheoretic (hκ : κ.IsRegular) :
    (Nonempty (FinalCoalgebra (PkFunctor κ) (U κ))) ∧
    (∃ ω : U κ, ω = Quotient.mk _ (MTree.node ⟨{repr ω}, _⟩))
```

**Success condition.** Final-coalgebra instance on the quotient; `Ω` definable and equal to its singleton in the quotient.

**Failure modes.** (i) Quotient fails to carry a coalgebra map (setoid-vs-`P_κ` interaction / lack of choice) ⇒ no internal finality. (ii) `codata` over a `Set`-container is not accepted (positivity/size) ⇒ no carrier at all in-system.

**Trade-off.** Most machine-checkable (stays inside Lean's kernel, no set-theory axiom import) and most reusable for a fully formal downstream, but the `Set`-valued container strains Lean's positivity/size checking and may force replacing `P_κ` by a finite/list container — which *changes the metaphysics* (finite branching only).

---

### C6 — Relational-limit / greatest-fixed-point framing (Rutten universal coalgebra)

**Ambient theory.** `Set`-based universal coalgebra; obligation = existence of `νF` via the final sequence `1 ← F1 ← F²1 ← …` stabilizing, plus `F` bounded ⇒ limit exists.

**Framing.** The final sequence of `P_κ` converges at some ordinal stage `α`; `νF := lim` and `F(νF) ≅ νF`.

**Proof strategy.** Boundedness ⇒ the sequence is eventually constant (Worrell/Adámek–Koubek); take the limit; Lambek.

**Lean 4 signature.**
```lean
theorem ws1_C6_finalSequence (hκ : κ.IsRegular) :
    ∃ (α : Ordinal) (L : Type u),
      IsLimit (finalSequence (PkFunctor κ) α) L ∧
      Nonempty (L ≃ (PkFunctor κ).obj L)
```

**Success condition.** Convergence ordinal `α` exists (`≤ κ` for `κ`-bounded); iso at the limit.

**Failure modes.** (i) *Non-convergence*: sequence never stabilizes ⇒ `νF` non-existent as a set (would happen for *unbounded* `P` — Cantor). (ii) Limit exists but iso fails ⇒ not actually final.

**Trade-off.** Gives an *explicit* construction (useful for later computing bisimulation and the Goldilocks band in WS7) and makes the cardinality bound the visible knob; heaviest in ordinal/limit bookkeeping.

---

## Cross-cutting trade-offs

The essential tension is **existence vs. identity vs. fidelity**, threaded through the size knob `κ`.

Existence-first candidates (C1, C6) settle whether the carrier is a set at all, exposing `κ` as the dial that separates "exists" from Cantor collapse; they are the safest base but say least about self-reference until augmented. Identity-first candidates (C2, C3) directly deliver bisimulation-as-equality and the solution/decoration machinery downstream phases consume, but presuppose existence. C4 is the cheap existential floor — good as milestone 1, insufficient alone. C5 buys full kernel-level formalizability at the cost of possibly retreating to finite branching, which would silently weaken the metaphysics (finite-branching `Ω` is fine, but "no atoms with `κ`-many relations" is not testable there).

Recommended spine: prove **C1** (carrier exists, is a set, Lambek iso, bisim = eq) as the framework memo's core, immediately derive **C2** (solution lemma) as the reusable BR lemma, and keep **C4** as the early smoke test. Reserve C3/C6 as alternative constructions to cross-validate the identity criterion, and treat C5 as the target refactor once the `Set`-container size issues are resolved (likely by fixing `κ` = a concrete inaccessible and using a bounded-cardinality container type).

A single hidden dependency runs under all six: the choice of `κ` (finite / ℵ₀ / regular uncountable / inaccessible) is not free — it is exactly the WS7 "richness vs. boundedness" dial appearing already at WS1. Fixing it here commits the whole program, so the framework memo should state `κ` as an explicit parameter and prove each result *schematically in `κ`* wherever possible, deferring the concrete choice to the non-collapse analysis.
