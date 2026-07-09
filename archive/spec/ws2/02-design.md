The best candidate is **plain `P_κ` now, with the enrichment fork deferred to WS4** — the sequencing that Document 1 argues for and that the triage in Document 1 formalizes. Concretely: commit `F = P_κ`, assemble Framings **1 + 3 + 4 + 2 + 5** as a single WS2 deliverable, and register the §3.5 enrichment (Framing 6's territory) as an explicit WS4 ratification obligation rather than pre-satisfying it now.

The reasoning for the selection, briefly, then the full design.

## Why this candidate

Run Document 1's three-question triage on the open candidates:

| Candidate `F` | (1) QPF/accessible → `νF` exists? | (2) preserves weak pullbacks? | (3) grading earns its keep? |
|---|---|---|---|
| plain `P_κ` | yes (WS1 built it via `Cofix`) | yes (classical: relational/`Rel`-liftable) | n/a |
| `[0,1]`-weighted `P` | uncertain; depends on presentation | **generally no** | maybe |
| distribution/prob. functor `D` | yes over reasonable base | **no** (Giry-style `D` famously fails) | yes |
| quantale-enriched `W_Q` | uncertain for "large" `Q` | depends on integrality/distributivity of `Q` | yes |

Only `P_κ` passes (1) and (2) outright, which is exactly the precondition for the clean `1+3+4+2+5` assembly to go through. Every enriched candidate either risks failing existence (1) or falls to the bisimulation/behavioral split (2), landing in Framing 6. Since the charter (§3.9, §6.1) treats `(F,κ)` as a *shared* parameter that WS4 may still change, committing `P_κ` now discharges everything already in hand from WS1 without pre-committing to a WS4 requirement nobody has specified. This is the move §8.2 explicitly endorses: substitute openly, recover canonical content in the surrogate, route the residual to the owning workstream.

I incorporate Document 1's correction to Framing 6's vacuous `ws2_behav_equiv` signature into the deferred-obligation spec, so the WS4 hand-off is stated with real content rather than a trivial `Equivalence (· = ·)`.

---

## WS2 Design: `νP_κ` and its bisimulation theory

### Ambient theory and imports

Everything lives in ZFC/Mathlib, `u`-polymorphic, in `namespace Series3.WS2`. WS2 imports the following from `ws1.lean` (Document 3) as *established, axiom-free theorems*:

- `Coalg κ`, `IsTerminalCoalg`, `PkObj`, `PkMap`, `PkMap_id`, `PkMap_comp` — the functor and coalgebra category.
- `exists_terminal_coalg : ∀ κ, ∃ U, IsTerminalCoalg U` — **existence** (this is Framing 4's precondition, already discharged, so WS2 does not re-prove existence, it *cites* it).
- `qpfPk : QPF (PkObj κ)` with `PkP`, `absPk`, `reprPk` — the QPF presentation.
- `Bisim`, `bisim_eq`, `hom_unique`, `endo_eq_id`, `lambek`.
- `GroundlessCarrier`, `ws1_C1`.

Standing hypotheses match WS1: existence needs no hypothesis on `κ`; `hinf : ℵ₀ ≤ κ` is consumed only for non-degeneracy witnesses (Framing 3). No monad `T`, no distributive law `λ` — those defer to WS3. No grading — defers to WS4.

The **one lemma WS1 deliberately did not formalize** (flagged in Document 3's "registered dependency" note and Document 4 §8.1) is the load-bearing new obligation of WS2:

> **Lemma 3.1a (WS1-registered, WS2-owned):** `P_κ` preserves weak pullbacks.

This is what upgrades `bisim_eq` from "terminality-formal" to "observationally meaningful," and it is the sole genuinely new mathematical content of the core deliverable.

### Component A — Existence, re-exported (Framing 4)

No new proof. WS2 packages WS1's result under the abstract interface it will use downstream:

```lean
def νPk (κ : Cardinal.{u}) : Coalg κ := ⟨Cofix (PkObj κ), Cofix.dest⟩

theorem νPk_terminal (κ : Cardinal.{u}) : IsTerminalCoalg (νPk κ) :=
  -- extract the witness produced inside exists_terminal_coalg
  (Classical.choose_spec (exists_terminal_coalg κ)) -- after aligning the carrier
```

*Dependency:* `exists_terminal_coalg`, `qpfPk` (Document 3, §2). *Status: discharged upstream; re-exported.*

### Component B — Non-degeneracy (Framing 3)

The anti-collapse floor. WS1's `ws1_C1` already produces two distinct points (`hE`/`hΩ`); WS2 lifts this to the standalone richness statement and connects it to the QPF shape count.

```lean
theorem ws2_nondegenerate (hinf : ℵ₀ ≤ κ) :
    ∃ a b : (νPk κ).X, a ≠ b
```

**Proof strategy.** Map `emptyCoalg` and `omegaCoalg` (both from Document 3, §4) into `νPk` via terminality; their structure maps land on `∅` and a nonempty singleton respectively, so by injectivity of the structure map (Lambek) the images differ. This is `ws1_C1`'s `hne` argument, re-stated as a lemma about `νPk` alone.

*Dependencies:* `lambek`, `mk_empty_lt`, `mk_singleton_lt`, `omegaCoalg`, `emptyCoalg`. *Status: discharged, reusing WS1.*

### Component C — Bisimulation = identity, terminal form (Framing 1)

```lean
theorem ws2_bisim_eq (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) :
    ∀ x y, R x y → x = y :=
  bisim_eq (νPk_terminal κ) R hR
```

Direct instantiation of WS1's `bisim_eq` at the WS2 carrier. *Status: discharged, one line.*

### Component D — Weak-pullback preservation (Framing 2, the new work)

This is the core. It needs three new pieces of theory.

**D1 — The predicate.** Define weak-pullback preservation concretely for the `PkObj` functor. Rather than a general categorical `PreservesWeakPullbacks`, use the *relation-lifting* characterization, which is what actually gets used and is tractable in Mathlib:

```lean
/-- The Barr relation lifting of `P_κ`: two κ-small sets are related iff every
    element of each is R-related to some element of the other, witnessed by a
    κ-small subset of the graph. -/
def PkRel {X Y : Type u} (R : X → Y → Prop) :
    PkObj κ X → PkObj κ Y → Prop := fun s t =>
  ∃ w : PkObj κ {p : X × Y // R p.1 p.2},
    PkMap κ (fun p => p.1.1) w = s ∧ PkMap κ (fun p => p.1.2) w = t
```

**D2 — The key lemma (Lemma 3.1a).**

```lean
theorem PkRel_comp {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop) :
    ∀ s u, (∃ t, PkRel R s t ∧ PkRel S t u) → PkRel (Rel.comp R S) s u
```

Equivalently phrased as the categorical statement: `PkMap κ` sends weak pullbacks to weak pullbacks. **The mathematical content:** given a `Y`-indexed span witnessing `PkRel R s t` and `PkRel S t u`, one must build a κ-small witness in the graph of `R ∘ S`. The classical fact is that `P` (and `P_κ`) preserves weak pullbacks because it admits a *relation lifting that is functorial on `Rel`* — the composition of liftings equals the lifting of the composition. The κ-bound is preserved because the witness set injects into a product of two κ-small sets, and `κ` regular gives `< κ · < κ = < κ`.

**This is the single place `hreg : κ.IsRegular` becomes load-bearing in WS2** — WS1 needed it nowhere on the `Cofix` route, but the product bound for the composed witness needs regularity (or at least `κ` closed under the relevant products). This is exactly the kind of hypothesis-tracking §8.1 demands.

**Proof architecture for D2:**
1. `Rel.comp`-witness construction: from `w₁ : PkObj κ (graph R)` and `w₂ : PkObj κ (graph S)` sharing the middle `t`, form the pullback set `{(p,q) // p.1.2 = q.1.1}` inside `graph R × graph S`.
2. Bound it: `mk ≤ mk w₁ * mk w₂ < κ` by regularity (`Cardinal.mul_lt_of_lt` for regular `κ`).
3. Project to `graph (Rel.comp R S)` via `(p,q) ↦ ((p.1.1, q.1.2), ⟨_, _⟩)`.
4. Check the two `PkMap` legs reproduce `s` and `u` — image-of-image bookkeeping via `Set.image_comp`, mirroring `PkMap_comp`'s proof style in Document 3.

**D3 — Consequence: bisimilarity is transitive, hence the greatest bisimulation is an equivalence coinciding with behavioral equivalence.**

```lean
theorem ws2_bisim_behavioural (hreg : κ.IsRegular)
    (x y : (νPk κ).X) :
    (∃ R, Bisim (νPk κ) R ∧ R x y) ↔ x = y
```

- (←) `x = y` gives the diagonal bisimulation (trivially an `F`-bisimulation).
- (→) is `ws2_bisim_eq` (Component C).
- The *substantive* upgrade is the intermediate lemma, powered by D2, that composition of bisimulations is a bisimulation (so "behaviorally equivalent" = "bisimilar" rather than merely "bisimilar ⊆ behaviorally equivalent"):

```lean
theorem bisim_comp (hreg : κ.IsRegular)
    {R S : (νPk κ).X → (νPk κ).X → Prop}
    (hR : Bisim (νPk κ) R) (hS : Bisim (νPk κ) S) :
    Bisim (νPk κ) (Rel.comp R S)   -- ζ built from PkRel_comp
```

*Dependencies:* D2 (`PkRel_comp`), `Bisim` (WS1), `Cardinal.mul_lt_of_lt`/regularity from Mathlib. *Status: the genuinely new WS2 proof obligation.*

### Component E — Coinduction principle, usable form (Framing 5)

The deliverable WS3/WS5 consume.

```lean
theorem ws2_coinduction
    (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) {x y} :
    R x y → x = y := ws2_bisim_eq R hR x y

theorem ws2_coinduction_upto (hreg : κ.IsRegular)
    (R : (νPk κ).X → (νPk κ).X → Prop)
    (hRupto : BisimUpToEquiv (νPk κ) R) {x y} :
    R x y → x = y
```

`BisimUpToEquiv` (bisimulation up to equivalence, Pous–Sangiorgi) is a new definition; its soundness lemma is **exactly** where D2 is reused — up-to-equivalence is sound *iff* weak pullbacks are preserved, so this component is honestly conditional on `hreg` and inherits from Component D rather than duplicating it.

*Dependencies:* Component C (base), Component D (up-to soundness). *Status: base discharged; up-to conditional on D.*

### The assembled deliverable

```lean
structure WS2Characterization (κ : Cardinal.{u}) where
  carrier        : Coalg κ                                    -- νPk κ
  terminal       : IsTerminalCoalg carrier                    -- A / WS1
  nondegenerate  : ∃ a b : carrier.X, a ≠ b                   -- B / Framing 3
  bisim_eq       : ∀ R, Bisim carrier R → ∀ x y, R x y → x=y  -- C / Framing 1
  weak_pullback  : PkPreservesWeakPullback κ                  -- D / Framing 2 (NEW)
  behavioural    : ∀ x y, (∃ R, Bisim carrier R ∧ R x y) ↔ x=y -- D3
  coinduction    : /- Framing 5 packaging -/

theorem ws2_characterization (hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ) :
    Nonempty (WS2Characterization κ)
```

The only field requiring new mathematics is `weak_pullback` (and its consequence `behavioural`); the rest are re-exports or one-line instantiations of WS1.

---

## The deferred WS4 obligation (Framing 6, correctly stated)

WS2 does **not** commit an enriched `F`. It registers, per §6.1's management rule, the ratification obligation for WS4, and — incorporating Document 1's correction — states it with real content rather than the vacuous `Equivalence (· = ·)`:

```lean
-- The obligation WS4 must discharge OR declare failed, for its chosen (W_Q, κ):
-- (1) existence of νW_Q as a set  [Framing 4 precondition, may FAIL];
-- (2) behavioural equivalence = KERNEL OF THE ANAMORPHISM is a congruence
--     wrt W_Q's structure — NOT `Equivalence (fun x y => x = y)`:
theorem ws4_behav_equiv_target {Q} [Quantale Q]
    (U : Coalg (WPow Q)) (hU : IsTerminalCoalg U)
    (ana : ∀ C : Coalg (WPow Q), C.X → U.X) :
    let behav := fun x y => ana _ x = ana _ y
    Equivalence behav ∧
      (∀ x y, behav x y → WPowObs Q x = WPowObs Q y)   -- the real content
-- (3) the DECLARED, PROVED split when weak pullbacks fail:
--     bisim ⊊ behav, routed to WS7 as ratification constraint, never relabeled.
```

This is the honest terminal form if and only if WS4's grading forces abandonment of weak-pullback preservation — precisely the condition D2 pins down for `P_κ` and that the enriched candidates fail.

---

## Dependency summary

| WS2 component | New work? | Imports from WS1 (Doc 3) | Charter obligation (Doc 4) |
|---|---|---|---|
| A Existence | no | `exists_terminal_coalg`, `qpfPk` | WS2 "νF exists" ✓ |
| B Non-degeneracy | no | `lambek`, `omega/emptyCoalg`, `mk_*_lt` | criterion (vii) ≥2 part |
| C Bisim=id (terminal) | no | `bisim_eq` | criterion (ii), formal |
| **D Weak-pullback (3.1a)** | **yes** | `Bisim`, `PkMap_comp`; +`hreg` | criterion (ii), *meaningful*; §8.1 WS2 hazard closed for `P_κ` |
| E Coinduction | up-to only | C, D | consumed by WS3/WS5 |
| WS4 target | deferred | — | §6.1 ratification; §8.2 discipline |

The critical path is Component D: it is the one lemma WS1 explicitly left unformalized, the one place `hreg` earns its place in WS2, and the exact hinge on which the whole `1+3+4+2+5` assembly either composes cleanly (for `P_κ`, expected: yes) or collapses to the Framing 6 fallback (for the enriched candidates WS4 may later want). Committing `P_κ` now makes D provable today and defers the fork honestly.
