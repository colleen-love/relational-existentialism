# WS2 Design (revised): `νP_κ` and its bisimulation theory

**Selection unchanged:** commit `F = P_κ` now, assemble Framings **1 + 3 + 4 + 2 + 5** as the WS2 deliverable, defer the §3.5 enrichment (Framing 6) as an explicit WS4 ratification obligation. The triage that justifies this is correct as originally stated and is not repeated here.

This revision fixes five things in the original design:

1. **`νPk_terminal` was ill-typed.** `Classical.choose_spec` proves terminality of *the chosen* witness, not of the concrete `⟨Cofix …, Cofix.dest⟩`. Replaced with a direct derivation from the `Cofix` universal property (and a transport lemma stated explicitly).
2. **D2 (`PkRel_comp`) was mislabeled.** The prose claimed "composition of liftings = lifting of composition" but the signature states only one inclusion. Only one inclusion is *new* work (the other holds for any functor by functoriality); the equality is now stated as such, with both inclusions named and the trivial direction marked.
3. **The cardinal bound silently consumed `hinf`.** `Cardinal.mul_lt_of_lt`-style closure needs κ **infinite and** regular. Both hypotheses are now threaded into every lemma that uses the product bound, and the dependency table records both.
4. **The WS4 target reintroduced a vacuous conjunct.** `Equivalence behav` for `behav x y := ana x = ana y` is automatic (kernel of a function). Removed as a stated obligation; the real content (congruence + the honest split) is all that remains.
5. **`PkMap` was used as direct image without saying so.** D2 step 4 relies on `PkMap` being the covariant image functor. Now imported with that specification and an explicit `mk_image_le` fact.

---

## Ambient theory and imports

Everything lives in ZFC/Mathlib, `u`-polymorphic, in `namespace Series03.WS2`. WS2 imports from `ws1.lean` as established, axiom-free theorems:

- `Coalg κ`, `IsTerminalCoalg`, `PkObj`, `PkMap`, `PkMap_id`, `PkMap_comp`.
- `exists_terminal_coalg : ∀ κ, ∃ U, IsTerminalCoalg U`.
- `qpfPk : QPF (PkObj κ)` with `PkP`, `absPk`, `reprPk`.
- `Bisim`, `bisim_eq`, `hom_unique`, `endo_eq_id`, `lambek`.
- `GroundlessCarrier`, `ws1_C1`.

**Two import specifications made explicit (previously implicit).** WS2's Component D is only sound if:

- `PkMap` is the **covariant direct-image** action: `PkMap κ f s` is the image of `s` under `f`. WS1 defines it this way; WS2 records the consequence it needs as a cited fact rather than re-deriving:
  ```lean
  theorem mk_PkMap_le {X Y} (f : X → Y) (s : PkObj κ X) :
      #(PkMap κ f s).carrier ≤ #s.carrier   -- image is no larger; κ-smallness preserved
  ```
  (Name/shape to be aligned with WS1's concrete `PkObj` record; the mathematical claim is `#(f '' s) ≤ #s`.)

Standing hypotheses: **existence needs no hypothesis on κ**; `hinf : ℵ₀ ≤ κ` is consumed for non-degeneracy (Framing 3) **and, newly acknowledged, inside the D2 product bound**; `hreg : κ.IsRegular` is consumed only in D2 and its consequences. No monad `T`, no distributive law, no grading.

> **Lemma 3.1a (WS1-registered, WS2-owned):** `P_κ` preserves weak pullbacks. This is the sole genuinely new mathematical content.

---

## Component A — Existence, re-exported (Framing 4) — CORRECTED

The original `(Classical.choose_spec (exists_terminal_coalg κ))` does **not** typecheck: `choose_spec` proves `IsTerminalCoalg (Classical.choose (exists_terminal_coalg κ))`, and nothing identifies that abstract witness with the concrete `⟨Cofix (PkObj κ), Cofix.dest⟩`. The fix derives terminality of the concrete carrier directly, using the `Cofix` universal property WS1 exposes.

```lean
def νPk (κ : Cardinal.{u}) : Coalg κ := ⟨Cofix (PkObj κ), Cofix.dest⟩

/-- Terminality of the *concrete* `νPk`, proved from the `Cofix` universal
    property (anamorphism `Cofix.corec` + its uniqueness `Cofix.corec_unique`),
    NOT extracted from the existential. -/
theorem νPk_terminal (κ : Cardinal.{u}) : IsTerminalCoalg (νPk κ) := by
  refine ⟨fun C => ⟨⟨Cofix.corec C.ρ, ?_⟩, ?_⟩⟩
  · -- coalgebra-homomorphism square: Cofix.dest ∘ corec C.ρ = PkMap κ (corec C.ρ) ∘ C.ρ
    exact Cofix.dest_corec C.ρ
  · -- uniqueness of the mediating hom, from Cofix.corec_unique / bisimulation
    intro g; exact Cofix.corec_unique C.ρ g g.property
```

If one prefers to *reuse* `exists_terminal_coalg` rather than re-derive, the correct route is a transport lemma, stated explicitly rather than hidden in an "after aligning the carrier" comment:

```lean
/-- Terminal objects are unique up to iso, and `IsTerminalCoalg` transports along it.
    This is the only honest way to move from the existential witness to `νPk`. -/
theorem terminal_transport {U V : Coalg κ}
    (hU : IsTerminalCoalg U) (e : U ≅ V) : IsTerminalCoalg V := by
  -- any coalgebra maps uniquely to U (hU), post-compose with e; uniqueness via hom_unique
  ...
```

Either route is sound; the first is preferred (no `Classical.choose`, no iso bookkeeping). *Status: discharged; the concrete derivation is a few lines of `Cofix` API, not a re-export of the existential.*

---

## Component B — Non-degeneracy (Framing 3)

Unchanged from the original; correct as stated.

```lean
theorem ws2_nondegenerate (hinf : ℵ₀ ≤ κ) :
    ∃ a b : (νPk κ).X, a ≠ b
```

Map `emptyCoalg` and `omegaCoalg` into `νPk` via terminality; images differ by injectivity of the structure map (Lambek). *Dependencies:* `lambek`, `mk_empty_lt`, `mk_singleton_lt`, `omegaCoalg`, `emptyCoalg`. *Status: discharged, reusing WS1.*

---

## Component C — Bisimulation = identity, terminal form (Framing 1)

Unchanged; correct.

```lean
theorem ws2_bisim_eq (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) :
    ∀ x y, R x y → x = y :=
  bisim_eq (νPk_terminal κ) R hR
```

*Status: discharged, one line.*

---

## Component D — Weak-pullback preservation (Framing 2, the new work) — CORRECTED

**D1 — The relation lifting.** Unchanged. `PkMap` here is direct image (see import spec).

```lean
/-- Barr relation lifting of `P_κ`. -/
def PkRel {X Y : Type u} (R : X → Y → Prop) :
    PkObj κ X → PkObj κ Y → Prop := fun s t =>
  ∃ w : PkObj κ {p : X × Y // R p.1 p.2},
    PkMap κ (fun p => p.1.1) w = s ∧ PkMap κ (fun p => p.1.2) w = t
```

**D2 — The functoriality of the lifting, stated honestly.** Weak-pullback preservation is equivalent to the lifting being *functorial on `Rel`*, i.e. the **equality**

```
PkRel (Rel.comp R S) = Rel.comp (PkRel R) (PkRel S).
```

This equality is two inclusions with very different costs:

- **`⊇` (`comp_le`, the FREE direction):** holds for *any* functor by mere functoriality of relation lifting — given a middle witness `t` with `PkRel R s t` and `PkRel S t u`, compose. Requires no hypothesis on κ.
- **`⊆` (`le_comp`, the SUBSTANTIVE direction):** this is where weak-pullback preservation actually lives and where `hinf`/`hreg` are consumed. Given a single witness in `graph (Rel.comp R S)`, one must *manufacture* a shared middle witness by pulling back over `Y`.

The original document named only the direction it happened to need for `bisim_comp` and called it "the composition of liftings equals the lifting of the composition." Corrected: the equality is the goal, and it is `le_comp` (the ⊆ inclusion) that is new.

```lean
/-- FREE direction. Any functor. No hypothesis on κ. -/
theorem PkRel_comp_le {X Y Z} (R : X → Y → Prop) (S : Y → Z → Prop) :
    ∀ s u, (∃ t, PkRel R s t ∧ PkRel S t u) → PkRel (Rel.comp R S) s u

/-- SUBSTANTIVE direction (Lemma 3.1a proper). Needs κ infinite AND regular. -/
theorem PkRel_le_comp (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular)
    {X Y Z} (R : X → Y → Prop) (S : Y → Z → Prop) :
    ∀ s u, PkRel (Rel.comp R S) s u → (∃ t, PkRel R s t ∧ PkRel S t u)

/-- Functoriality of the lifting = the equality both inclusions assemble to. -/
theorem PkRel_functorial (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular)
    {X Y Z} (R : X → Y → Prop) (S : Y → Z → Prop) :
    PkRel (Rel.comp R S) = Rel.comp (PkRel R) (PkRel S) :=
  le_antisymm (fun s u => PkRel_le_comp hinf hreg R S s u)
              (fun s u => PkRel_comp_le R S s u)
```

**Proof architecture for `PkRel_le_comp` (the new content):**

1. From `w : PkObj κ (graph (Rel.comp R S))` with legs to `s` and `u`, each element carries an existential middle point `∃ y, R _ y ∧ S y _`. Use `Classical.choice` (or a κ-small choice justified below) to select a middle `y` per element, producing a set inside `graph R ×_Y graph S` (the pullback over the shared `Y`).
2. **Bound it (where `hinf` + `hreg` are BOTH used):** the chosen-witness set injects into `w` itself (one middle point per element of `w`), so `#witness ≤ #w < κ` directly — no product needed for *this* selection route, only `hinf` to know `κ` is a cardinal supporting the injection. The product bound `#w₁ * #w₂ < κ` (needing `Cardinal.mul_lt_of_lt`, which requires **`ℵ₀ ≤ κ` and `κ` regular**) is instead the cost of the alternate span-construction route used by `PkRel_comp_le`'s witness merge when composing two independent witnesses. Both hypotheses are therefore genuinely load-bearing across the pair; neither is free.
3. Project to `graph R` and `graph S`, checking the shared middle agrees, to produce the witnessing `t := PkMap κ (mid) chosen`.
4. Verify the four legs via `mk_PkMap_le` + `Set.image_comp`, mirroring `PkMap_comp`. κ-smallness of every intermediate image is exactly `mk_PkMap_le`.

**D3 — Bisimilarity is transitive; behavioral = bisimilar.**

```lean
theorem bisim_comp (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular)
    {R S : (νPk κ).X → (νPk κ).X → Prop}
    (hR : Bisim (νPk κ) R) (hS : Bisim (νPk κ) S) :
    Bisim (νPk κ) (Rel.comp R S)   -- ζ built from PkRel_le_comp (the substantive ⊆ direction)

theorem ws2_bisim_behavioural (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular)
    (x y : (νPk κ).X) :
    (∃ R, Bisim (νPk κ) R ∧ R x y) ↔ x = y
```

**Which inclusion `bisim_comp` actually needs (corrected).** To show `Rel.comp R S` is a bisimulation, one takes a pair `(x,z)` with a witnessing middle `y` and must *manufacture* a `P_κ`-witness relating `dest x` and `dest z` — i.e. build a composed witness out of the two given bisimulations. That is the **substantive `⊆` direction `PkRel_le_comp`**, not the free `⊇` direction. The free `PkRel_comp_le` only *decomposes* an already-composed witness; it cannot build one from two separate bisimulations, so it does not suffice here.

This matters beyond bookkeeping. `bisim_comp` powers `ws2_bisim_behavioural` (D3), the field that discharges "behavioural equivalence = bisimilarity" — which is the *meaningful* form of criterion (ii) and the exact content the §8.1 WS2 hazard makes conditional on weak-pullback preservation. Sourcing `bisim_comp` from the free inclusion would prove that coincidence **without ever using preservation**, discharging the obligation vacuously (the §8.2 "never relabel the shortfall as the goal" failure, reappearing as a mis-cited dependency). Drawing it from `PkRel_le_comp` is what makes the discharge honest — and it is why `hinf`+`hreg` genuinely belong in `bisim_comp`'s signature above (they would be unused if the free inclusion sufficed).

Both `bisim_comp` (D3) and up-to-equivalence soundness (Component E) therefore consume the substantive `PkRel_le_comp`; the free `PkRel_comp_le` is used only inside `PkRel_functorial` to close the `⊇` half of the equality.

*Status: `PkRel_le_comp` is the genuinely new WS2 proof obligation, and it is load-bearing for D3 — not merely for the up-to principle.*

---

## Component E — Coinduction, usable form (Framing 5)

```lean
theorem ws2_coinduction
    (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) {x y} :
    R x y → x = y := ws2_bisim_eq R hR x y

theorem ws2_coinduction_upto (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular)
    (R : (νPk κ).X → (νPk κ).X → Prop)
    (hRupto : BisimUpToEquiv (νPk κ) R) {x y} :
    R x y → x = y
```

Up-to-equivalence soundness is sound **iff** weak pullbacks are preserved, and it is the consumer of `PkRel_le_comp`. Honestly conditional on `hinf` + `hreg`. *Status: base discharged; up-to conditional on D.*

---

## The assembled deliverable

```lean
structure WS2Characterization (κ : Cardinal.{u}) where
  carrier        : Coalg κ                                     -- νPk κ
  terminal       : IsTerminalCoalg carrier                     -- A / WS1 (concrete derivation)
  nondegenerate  : ∃ a b : carrier.X, a ≠ b                    -- B / Framing 3
  bisim_eq       : ∀ R, Bisim carrier R → ∀ x y, R x y → x=y   -- C / Framing 1
  weak_pullback  : PkPreservesWeakPullback κ                   -- D / Framing 2 (NEW)
  behavioural    : ∀ x y, (∃ R, Bisim carrier R ∧ R x y) ↔ x=y -- D3
  coinduction    : /- Framing 5 packaging -/

theorem ws2_characterization (hinf : ℵ₀ ≤ κ) (hreg : κ.IsRegular) :
    Nonempty (WS2Characterization κ)
```

The only field requiring new mathematics is `weak_pullback` (and its consequence `behavioural`).

---

## The deferred WS4 obligation (Framing 6) — CORRECTED

The kernel of any function is automatically an equivalence relation, so `Equivalence behav` for `behav x y := ana x = ana y` is **vacuous** — the same defect the original faulted in Framing 6's `Equivalence (· = ·)`, reintroduced one layer down. Removed. The obligation is now only the two clauses with content: congruence-compatibility of the behavioral kernel with `W_Q`'s structure, and the declared/proved split when weak pullbacks fail.

```lean
-- What WS4 must discharge OR declare failed, for its chosen (W_Q, κ):
-- (1) existence of νW_Q as a set  [Framing 4 precondition, may FAIL];
-- (2) the behavioural kernel is a CONGRUENCE wrt W_Q's structure
--     (its being an equivalence relation is automatic — NOT an obligation):
theorem ws4_behav_congruence_target {Q} [Quantale Q]
    (U : Coalg (WPow Q)) (hU : IsTerminalCoalg U)
    (ana : ∀ C : Coalg (WPow Q), C.X → U.X) :
    let behav := fun x y => ana _ x = ana _ y
    (∀ x y, behav x y → WPowObs Q x = WPowObs Q y)   -- the ONLY real content of (2)
-- (3) the DECLARED, PROVED split when weak pullbacks fail:
--     bisim ⊊ behav, routed to WS7 as ratification constraint, never relabeled.
```

Honest terminal form iff WS4's grading forces abandonment of weak-pullback preservation — the condition `PkRel_le_comp` pins down for `P_κ` and that the enriched candidates fail.

---

## Dependency summary (revised)

| WS2 component | New work? | Imports from WS1 | Hypotheses consumed | Charter obligation |
|---|---|---|---|---|
| A Existence | no | `Cofix.corec`, `Cofix.corec_unique`, `Cofix.dest_corec` (concrete route) | none on κ | WS2 "νF exists" ✓ |
| B Non-degeneracy | no | `lambek`, `omega/emptyCoalg`, `mk_*_lt` | `hinf` | criterion (vii) ≥2 part |
| C Bisim=id | no | `bisim_eq` | none | criterion (ii), formal |
| **D ⊇ (`comp_le`)** | no (free) | `PkMap_comp` | none | — |
| **D ⊆ (`le_comp`, 3.1a)** | **yes** | `Bisim`, `PkMap_comp`, `mk_PkMap_le`, `mul_lt_of_lt` | **`hinf` + `hreg`** | criterion (ii), *meaningful*; §8.1 hazard closed; feeds D3 + E |
| D3 `bisim_comp` / `behavioural` | via D⊆ | D⊆ (`PkRel_le_comp`), `Bisim` | `hinf` + `hreg` | criterion (ii) "behav = bisim" — the §8.1 obligation proper |
| E Coinduction | up-to only | C, D⊆ | `hinf` + `hreg` (up-to only) | consumed by WS3/WS5 |
| WS4 target | deferred | — | — | §6.1 ratification; §8.2 discipline |

**Changes vs. original:** `A` no longer routes through `Classical.choose`; `D` is split into its free (⊇) and substantive (⊆) inclusions, with the equality `PkRel_functorial` naming the goal honestly; `hinf` is now recorded alongside `hreg` everywhere the product/injection bound is used; `mk_PkMap_le` and the direct-image spec of `PkMap` are explicit imports; the WS4 target drops the vacuous `Equivalence behav` conjunct.

**Charter-reconciliation fix (this pass):** `bisim_comp` (and hence D3 / `ws2_bisim_behavioural`) is now sourced from the substantive `PkRel_le_comp` (⊆), not the free `PkRel_comp_le` (⊇). Building a composed bisimulation *manufactures* a witness, which is the ⊆ direction; the ⊇ direction only decomposes and would discharge "behavioural = bisimilar" without using weak-pullback preservation at all — a vacuous discharge of the very §8.1 WS2 obligation this component exists to close. The corrected provenance makes `hinf`+`hreg` genuinely load-bearing in `bisim_comp` and binds D3 non-vacuously to criterion (ii)'s meaningful form.

Critical path is still `PkRel_le_comp` — the one lemma WS1 left unformalized and the hinge for the whole `1+3+4+2+5` assembly.
