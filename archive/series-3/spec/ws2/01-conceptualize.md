# WS2 Obligation: Object = Relations, Coinductively

## What is at stake

The mathematical object is the **final coalgebra `νF`** of a chosen observation functor `F : Type u → Type u`, together with its **bisimulation theory**. WS1 discharged existence for `F = P_κ` specifically. WS2's obligation is broader and sharper: to *characterize* `νF` for the observation functor the program actually commits to, and to prove that **bisimilarity coincides with the internal identity** on that carrier (behavioral indistinguishability = equality).

The non-triviality has three sources:

1. **Bisimilarity = behavioral equivalence is not automatic.** It holds when `F` preserves weak pullbacks. For plain `P_κ` this holds; for *weighted*, *probabilistic*, or *quantale-enriched* variants (which §3.5/WS4 will want), weak-pullback preservation can fail, and then the greatest bisimulation is strictly coarser than behavioral/observational equivalence. Criterion (ii) — "identity = relational unfolding up to bisimulation" — silently breaks.

2. **`νF` existence is functor-dependent.** WS1's `Cofix`/QPF route works because `P_κ` is a QPF. A weighted functor over an arbitrary quantale need not be a QPF, need not be bounded/accessible, and may have no set-sized final coalgebra.

3. **The functor is a shared parameter.** Any `F` WS2 fixes must survive WS3's bialgebra coherence and WS4's grading. So WS2's "characterization" is only conditionally valid until ratified.

The core failure modes to guard against: **structural collapse** (`νF` is a single point — insufficient branching), **non-existence** (no set-sized `νF`), and the **bisimulation/behavioral-equivalence split** (the identity criterion fails).

---

## Candidate framings

### Framing 1 — Minimal: bisimulation = identity from terminality alone

The weakest, safest reading. Take `νF` as the terminal `F`-coalgebra (inherited from WS1 for `F = P_κ`). Prove only that every `F`-bisimulation is contained in the diagonal, using terminality directly — no weak-pullback lemma, no greatest-bisimulation packaging.

**Proof strategy.** Given a bisimulation `R` with its span coalgebra, the two projections `π₁, π₂` are coalgebra morphisms into the terminal object; terminality forces `π₁ = π₂`, so `R ⊆ Δ`. This is exactly WS1's `bisim_eq` generalized to abstract `F`. Requires only that `F` has a terminal coalgebra and that the bisimulation carries an `F`-coalgebra on its graph.

**Lean signature.**
```lean
theorem ws2_bisim_eq {F : Type u → Type u} [Functor F]
    (U : Coalg F) (hU : IsTerminalCoalg U)
    (R : U.X → U.X → Prop) (hR : Bisim F U R) :
    ∀ x y, R x y → x = y
```

**Ambient theory.** ZFC (Mathlib). `F` abstract with a `Functor` instance; no monad, no `λ`. AFA is *modeled* coalgebraically (final coalgebra ⇒ bisim = eq is the coalgebraic AFA), not imported set-theoretically.

**Success condition.** The theorem type-checks sorry-free for the abstract `F`, and instantiates at `F = P_κ` to recover WS1's `bisim_eq`.

**Failure.** None internal to this framing — but it is *incomplete*: it says nothing about whether *behavioral* equivalence (kernel of the unique map to `νF`) equals bisimilarity. If `F` fails weak pullbacks, this theorem is still true but vacuous-adjacent: bisimulations (in the span sense) may be a strict subclass of behaviorally-equivalent pairs, so "bisim = identity" no longer captures criterion (ii).

**Trade-off.** Maximally robust (functor-agnostic, terminality-only) but under-delivers: it does not certify that the *intended* equivalence (observational) is the one collapsed to identity.

---

### Framing 2 — Full: weak-pullback preservation ⇒ bisimilarity = behavioral equivalence

The intended reading. Prove `F` preserves weak pullbacks, derive that the greatest bisimulation is an equivalence relation and coincides with behavioral equivalence, and *then* that on the terminal coalgebra it is the diagonal.

**Proof strategy.** (a) Prove `PreservesWeakPullbacks F`. (b) Use it to show bisimilarity is transitive (composition of bisimulations is a bisimulation — the step that needs weak pullbacks), hence an equivalence. (c) Show behavioral equivalence (pairs identified by the unique map to `νF`) is a bisimulation, and every bisimulation refines behavioral equivalence — so they coincide. (d) On `νF`, behavioral equivalence is `Δ` by terminality.

**Lean signature.**
```lean
theorem ws2_bisim_behavioural {F : Type u → Type u} [Functor F]
    (hwp : PreservesWeakPullbacks F)
    (U : Coalg F) (hU : IsTerminalCoalg U) :
    ∀ x y : U.X,
      (∃ R, Bisim F U R ∧ R x y) ↔ x = y
```
(with `PreservesWeakPullbacks` a defined predicate: every weak pullback square is sent to a weak pullback.)

**Ambient theory.** ZFC/Mathlib; `F` concrete enough to prove weak-pullback preservation (`P_κ`: yes). No `T`, no `λ`.

**Success condition.** `hwp` proved for the committed `F`; both directions of the iff sorry-free.

**Failure.** `PreservesWeakPullbacks F` is *false* for the chosen `F` (the concrete hazard for weighted/probabilistic `F`). Then step (b) fails: composition of bisimulations need not be a bisimulation, transitivity fails, and the iff's forward direction breaks. This is the **bisimulation/behavioral split** — a genuine negative result about that `F`.

**Trade-off.** Delivers the criterion-(ii) content in full, but *couples* WS2 to a functor for which weak-pullback preservation is provable. Excludes exactly the enriched functors WS4 wants — forcing an early ratification decision.

---

### Framing 3 — Lambek non-degeneracy / anti-collapse floor

Recast the obligation as: `νF` is *not* a single point. Prove a richness floor on `F` guarantees `card(νF) ≥ 2` (indeed that non-bisimilar states exist).

**Proof strategy.** Exhibit two coalgebras (or two states) with provably distinct behaviors and map them into `νF`; use `bisim_eq`/injectivity of the anamorphism to conclude their images differ. Concretely the `Ω`-vs-`∅` witness of WS1 generalizes: any `F` with `≥ 2` distinguishable one-step behaviors (e.g. `∅` and a nonempty element in its image) yields `≥ 2` points. Formalize "richness floor" as: `∃ shapes s t : F PUnit, s ≠ t` lifting to distinct fixpoints.

**Lean signature.**
```lean
theorem ws2_nondegenerate {F : Type u → Type u} [Functor F]
    (U : Coalg F) (hU : IsTerminalCoalg U)
    (hrich : ∃ (C : Coalg F) (x y : C.X),
        ∀ (h : C.X → U.X), (∀ z, U.str (h z) = h <$> C.str z) → h x ≠ h y) :
    ∃ a b : U.X, a ≠ b
```

**Ambient theory.** ZFC/Mathlib; abstract `F`. No `T`/`λ`.

**Success condition.** For `F = P_κ`, discharge `hrich` via the empty/singleton coalgebras (already in WS1's `ws1_C1`), yielding `nondegenerate`.

**Failure — structural collapse.** If `F` is `Id`, a constant functor, or any functor with a single behavior up to bisimulation, `hrich` is unprovable and `νF` collapses to a point. Criterion (vii) structural-non-collapse fails at the WS2 level.

**Trade-off.** Directly targets the collapse hazard and is cheap for `P_κ`, but says nothing about the identity theorem; it is a *necessary* sub-obligation, not the whole of WS2.

---

### Framing 4 — Existence-carrying (QPF closure) rather than assumed-terminal

Rather than take `hU : IsTerminalCoalg U` as hypothesis, make WS2 *deliver* existence for the committed `F` by exhibiting it as a QPF (or accessible/bounded functor) and invoking `Cofix`. The characterization then rides on the construction.

**Proof strategy.** Provide a `QPF F` instance (as WS1 did for `P_κ`), obtain `νF := Cofix F` with `Cofix.dest`, prove terminality via `corec`/`dest_corec`/`bisim'`, and read off Lambek + bisim=eq as corollaries. For weighted `F`, attempt a QPF presentation via a polynomial with position types carrying weights in a fixed finite/ordinal-indexed set; if none exists, the framing fails loudly.

**Lean signature.**
```lean
theorem ws2_exists_terminal {F : Type u → Type u} [QPF F] :
    ∃ U : Coalg F, IsTerminalCoalg U
-- delivered object:
-- U := ⟨Cofix F, Cofix.dest⟩
```

**Ambient theory.** ZFC/Mathlib + a `QPF F` instance (the substantive obligation). No `T`/`λ`.

**Success condition.** `QPF F` instance constructed for the committed `F`; terminality proved (mirrors WS1's `exists_terminal_coalg`).

**Failure — non-existence.** No QPF (or accessible) presentation of `F` exists — the concrete risk for quantale-enriched `F` over a "large" quantale. Then `νF` may not be a set; the deliverable is an **impossibility/non-existence** result for that `F`.

**Trade-off.** Self-contained and honest about existence, but ties WS2 to functors admitting QPF presentation — a real restriction that pre-empts some WS4 enrichments. Stronger than Framing 1 (no assumed terminality) at the cost of constructive burden.

---

### Framing 5 — Coinduction-up-to / bisimulation-as-proof-principle

Cash out "an object *is* its relational unfolding, followed as far as one likes" as the **validity of the coinduction principle**: to prove two states equal, exhibit a bisimulation relating them. This is the *usable* form of bisim = identity.

**Proof strategy.** Package `bisim_eq` as a rewriting/tactic-level principle: provide `Cofix.bisim'`-style lemma specialized to the committed `F`, plus "bisimulation up-to context/equivalence" enhancements (Pous–Sangiorgi) so downstream proofs (WS3, WS5) can discharge equalities coinductively. Prove soundness of up-to-equivalence *only* under weak-pullback preservation (ties back to Framing 2).

**Lean signature.**
```lean
theorem ws2_coinduction {F : Type u → Type u} [Functor F]
    (U : Coalg F) (hU : IsTerminalCoalg U)
    (R : U.X → U.X → Prop) (hR : Bisim F U R) {x y : U.X} :
    R x y → x = y
-- plus an up-to companion (soundness conditional on hwp):
theorem ws2_coinduction_upto {F : Type u → Type u} [Functor F]
    (hwp : PreservesWeakPullbacks F) (U : Coalg F) (hU : IsTerminalCoalg U)
    (R : U.X → U.X → Prop) (hRupto : BisimUpToEquiv F U R) {x y : U.X} :
    R x y → x = y
```

**Ambient theory.** ZFC/Mathlib; abstract `F`; up-to soundness needs `hwp`. No `T`/`λ`.

**Success condition.** Plain coinduction sorry-free from terminality; up-to companion sorry-free given `hwp`.

**Failure.** Up-to-equivalence is *unsound* when `hwp` fails — the up-to companion becomes false, and downstream coinductive proofs built on it are invalid. Base coinduction survives (same content as Framing 1).

**Trade-off.** Produces the tool WS3/WS5 actually consume, but its stronger (up-to) form inherits Framing 2's weak-pullback dependency. Delivers usability at the cost of the same functor commitment.

---

### Framing 6 — Enriched/weighted commitment with declared split

The pessimistic-but-honest framing that anticipates WS4. Commit `F` to a weighted powerset `W_Q` over a quantale `Q`, *accept* that weak pullbacks may fail, and re-target the obligation: prove **behavioral equivalence** (kernel of the anamorphism) has the desired properties, explicitly *declaring* it distinct from span-bisimilarity.

**Proof strategy.** Define `νW_Q` (if it exists — inherits Framing 4's existence risk), define behavioral equivalence `x ≈ y ↔ anamorphism x = anamorphism y`, prove it is an equivalence and a congruence by construction (kernel of a map is always an equivalence — no weak pullback needed). Then prove, as a *separate* labeled result, whether span-bisimilarity coincides with it (expected: `⊆` only).

**Lean signature.**
```lean
-- behavioural equivalence is well-behaved unconditionally:
theorem ws2_behav_equiv {Q : Type u} [Quantale Q]
    (U : Coalg (WPow Q)) (hU : IsTerminalCoalg U) :
    Equivalence (fun x y : U.X => x = y)   -- trivial on νF; the content is:
-- the declared (expected strict) inclusion:
theorem ws2_bisim_lt_behav {Q : Type u} [Quantale Q]
    (hfail : ¬ PreservesWeakPullbacks (WPow Q))
    (U : Coalg (WPow Q)) (hU : IsTerminalCoalg U) :
    (∀ R, Bisim (WPow Q) U R → ∀ x y, R x y → x = y)
    ∧ (∃ C x y, behavEquiv C x y ∧ ¬ ∃ R, Bisim (WPow Q) U R ∧ R x y)
```

**Ambient theory.** ZFC/Mathlib; `F = WPow Q` weighted powerset over quantale `Q`; no `T`/`λ` (grading defers to WS4). Existence of `νW_Q` is a *precondition*, itself at risk.

**Success condition.** Behavioral-equivalence result unconditional; the split result proved *as* the declared substitution (a negative characterization) rather than hidden.

**Failure.** Even behavioral equivalence fails to be a congruence for pathological `Q`; or `νW_Q` doesn't exist at all (Framing 4 failure). Then WS2 reports **non-existence** for that enrichment.

**Trade-off.** Only framing compatible with WS4's grading ambition, but *concedes* criterion (ii) in its clean form — bisim ≠ identity, only behavioral-equivalence = identity. Most honest about the shared-parameter hazard; least clean as a "success."

---

## Cross-cutting trade-offs

The framings sit on two axes.

**Robustness vs. content.** Framings 1 and 3 are functor-agnostic and cheap, but individually incomplete: 1 gives the identity theorem without certifying it captures observational equivalence; 3 rules out collapse without touching identity. Framing 2 delivers the full intended content but only for weak-pullback-preserving `F`, excluding the enrichments WS4 wants.

**Commitment timing.** Framing 4 forces the existence/QPF question early and self-contained; Framing 6 forces the enrichment decision early and pessimistically. The safe program-level assembly is **1 + 3 + 4 instantiated at `P_κ`** as the ratifiable core (existence + non-degeneracy + identity, all discharged for the functor WS1 already built), with **2** added as the weak-pullback certificate that upgrades "bisim = identity" from terminality-formal to observationally-meaningful. **5** is the deliverable WS3/WS5 consume. **6** is held in reserve and activated only if WS4's grading forces abandonment of weak-pullback preservation — at which point the obligation is *re-registered* as behavioral-equivalence = identity with a declared, proved bisim/behavioral split, not reported as the original criterion (ii).

The single decision that couples everything: whether the committed `F` preserves weak pullbacks. If yes, Framings 1–5 compose into a clean success. If WS4 forces no, Framing 6 is the honest terminal form, and the "bisim = identity" criterion is discharged only in its behavioral-equivalence surrogate — which must be routed to WS7 as a ratification constraint, never relabeled as the original target.
