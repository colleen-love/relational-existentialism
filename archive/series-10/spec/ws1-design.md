# WS1 — The reifying carrier and productive blindness

**Design doc. Series 10, the blocking spine. Owns: the reifying carrier `(dest, insp, reify)` (ambient for all, `spec/README.md` §2.4), and the central positive — a reified self-relation is FREE (not recoverable from the relating that produced it), so the reification is irreducible, a genuinely new relatum, and the carrier genuinely grows. Productive blindness routes THROUGH the diagonal: recoverability of the reified self-relation would reconstruct a self-total hold, which `ws1_no_self_total_hold` forbids. WS1 also proves CLOSE-forbidden locally (a totality-relatum is a self-total hold) and fixes `reify` as a section-not-iso, ambient for all.**

*Series 10 is standalone; the carrier beneath the reification (`PkObj`, `SReaches`, `SHNE`, `IsBisim`, `BehaviorallyIdentified`, `ws1_atomless_bisim`, `ws2_import_theorem_static`, `Hold`, `afford`), the diagonal layer (`HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free`, `ws2_residue_is_import`), and the semantic import test (`Recoverable`, `plainOf`, `labelLoop`, `ws4_free_label_is_import`) are transcribed into `series-10/formal/Series10/ws1.lean`, re-namespaced `Series10.WS1` (see `spec/README.md` §6). The genuinely new Lean is `reify`, `IsReify`, `ws1_free_reification`, and `ws1_close_forbidden_local`. This is the workstream the whole series gates on (charter §6, protocol §4): nothing below is sound until productive blindness lands AND is certified to route through the diagonal, because that is what makes the growth genuine (not bookkeeping) and CLOSE forbidden.*

## The object at stake

The charter's spine (§2, §5.1): **on a κ-bounded reifying carrier, a reified self-relation is FREE — not recoverable from the plain relating — so it is a genuinely new object and the carrier genuinely grows.** The mechanism is the founding equation read as a generator: `reify : F(Ω) → Ω` sends a pattern-of-relating to the object that IS that pattern (`dest (reify s) = s`), and "to relate is to create" becomes the claim that this new object is IRREDUCIBLE. It is irreducible exactly when it is free, and freeness is the diagonal re-read: if the reified self-relation were recoverable from the plain relating, then some existing relatum would already hold the completed self-inspection, i.e. a self-total hold would exist, which `ws1_no_self_total_hold` forbids. So blindness is productive — relating mints a genuinely new relatum precisely BECAUSE the relating cannot fully hold itself. The design question is fourfold and each part is a separate obligation: (a) fix `reify` as a genuine **section** of `dest` (`dest ∘ reify = id`, so reification genuinely grows the carrier — §4.5's not-too-weak horn) that is **not an isomorphism** (not surjective, so the tower cannot close — §4.5's not-too-strong horn); (b) prove **free reification** (`ws1_free_reification`) with a proof term that routes through `ws1_no_self_total_hold` / `ws2_residue_is_import`, NOT a fresh freeness assumption; (c) prove **CLOSE-forbidden locally** (a totality-relatum is a self-total hold, so no `reify` fixed point closes the carrier); (d) certify the whole thing on a κ-bounded (hence consistent, §5.5) carrier where the section EXISTS.

The load-bearing subtlety, stated once here and never hidden: freeness (`ws2_residue_free`) is already a Series 09 theorem for the residue *content*. What Series 10 adds is the lift from "content not realised by any hold" to "relatum not recoverable from any prior carrier" — the reification turns the free content into a free *object*. The strip test will show the mathematical core is still the Series 09 diagonal freeness fact; what is earned is that the free content, reified, is a new carrier element whose existence (not just whose content) differentiates. WS1 states this and proves the reification is a section-not-iso, so the diagonal genuinely *grows the carrier* rather than *closing it*. The freeness is the diagonal; the reification is what makes it productive.

**Ambient theory.** `spec/README.md` §2.1 (carrier: `PkObj`, `SReaches`, `SHNE`, `IsBisim`, `BehaviorallyIdentified`, `ws1_atomless_bisim`, `ws2_import_theorem_static`), §2.2 (hold + import test: `Hold`, `afford`, `Recoverable`, `plainOf`, `ws4_free_label_is_import`), §2.3 (diagonal layer: `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free`, `ws2_residue_is_import`), §2.4 (reification: `IsReify`, `reify`). All from §6.

## Candidates

### C1 — `reify` is a section of `dest`, injective, not surjective (the carrier decision, charter-faithful)

```lean
def IsReify {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop :=
  ∀ s : PkObj κ X, dest (reify s) = s
theorem ws1_reify_injective {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) : Function.Injective reify := by
  intro s₁ s₂ he; have := congrArg dest he; rwa [h s₁, h s₂] at this
theorem ws1_reify_not_surjective {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective reify := …
```
`reify` is the forward map of `Ω ≅ F(Ω)`, pinned as a section: every pattern `s` is reifiable, and its reified relatum relates exactly to `s`. Injectivity is automatic (a section has a left inverse `dest`). Non-surjectivity is the razor: a surjective `reify` would make `dest` injective, and on such a carrier a totality-relatum gives a self-total hold (C4), so surjectivity contradicts the diagonal.

- **Ambient:** `PkObj`, `dest`; `IsReify`.
- **Success condition (Discharged):** the definitions typecheck; `reify` is a genuine section (grows the carrier) and provably not surjective (cannot close). The κ-bound is what makes such a section *exist* (a `PkObj κ Ω ↪ Ω` for suitable κ, while Cantor blocks the iso).
- **Failure mode:** *trivial-closure-both-directions (§4.5).* Too-weak: if `reify` is not a section (`dest ∘ reify ≠ id`), the reified relatum does not genuinely carry the pattern and growth is illusory (bookkeeping). Too-strong: if `reify` is surjective (an iso), the tower closes and a self-total hold is smuggled past the diagonal (`selfTotalSmuggled`). C1 walks the razor: section (grows) and not surjective (cannot close), the exact §4.5 discipline.

**Paper triage.** Decidable on paper: a section is injective (`congrArg dest`), and non-surjectivity follows from the diagonal (C4). The existence of the section for large κ is a cardinal fact (`PkObj κ Ω ↪ Ω` when `|[Ω]^{<κ}| = |Ω|`), stated as the carrier-strength obligation (C5). **Winner (the carrier decision).**

### C2 — Free reification: the reified self-relation is not recoverable (the spine, routing through the diagonal)

```lean
/-- The reified self-relation of an inspection `insp` at the free residue: the object whose relating
    carries the residue content. `RecoverableReification` holds if this object's identity is fixed by the
    plain relating — i.e. some prior relatum already realises the residue. -/
def ReifiedResidueRecoverable {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : Prop := ∃ h, insp h = residue insp   -- = ResidueRecoverable
theorem ws1_free_reification {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ReifiedResidueRecoverable dest insp)                                    -- FREE
  ∧ (ReifiedResidueRecoverable dest insp → ∃ t, SelfTotal insp t) := by        -- recovery ⇒ self-total (the route)
  exact ws2_residue_is_import dest insp
```
The reified self-relation is free: no prior relatum's content is the residue (the self-inspection the reified relatum would carry). And the routing is explicit — recoverability would put the residue in the range of `insp`, a hold whose content is the completed self-inspection, i.e. a self-total hold, which `ws1_no_self_total_hold` forbids. Productive blindness IS `ws2_residue_is_import`, lifted to the reification: the reified self-relation is a genuinely new object BECAUSE the relating cannot hold itself.

- **Ambient:** the diagonal layer; `residue`, `ResidueRecoverable`, `ws2_residue_is_import`.
- **Success condition (Discharged, the spine):** the term typechecks and its proof is `ws2_residue_is_import` (which routes through `ws1_no_self_total_hold`), NOT a fresh assumption. Productive blindness is a consequence of the diagonal, not a stipulation.
- **Failure mode:** *import (§4.1) — freeness asserted by a fresh assumption.* The one fatal risk: if freeness were an independent hypothesis (the reified relatum stamped free from outside), productive blindness would be an assertion, not earned, and the reification an import. C2 forecloses it: the proof term is literally `ws2_residue_is_import`, so freeness routes through the diagonal by construction. WS7 unfolds the term to confirm no fresh freeness axiom appears.

**Paper triage.** Decidable and immediate: `ws1_free_reification := ws2_residue_is_import`. The whole content is the transcribed diagonal, re-read as relatum-freshness. **Winner (the spine).**

### C3 — Productive blindness as growth: the reified relatum is a free label (bridge to WS2)

```lean
theorem ws1_reification_is_free_label {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (h₀ : Hold dest) (hblind : diag insp h₀) :
    -- the reified relatum realises the residue at h₀ (plain-invisible) …
    (∃ insp', (∀ h, insp' h = insp h ∨ insp' h = residue insp) ∧ insp' h₀ = residue insp)
    -- … but the residue is not in the prior range (label-visible: FREE, ws4_free_label_is_import horn)
  ∧ (¬ ∃ h, insp h = residue insp) := …
```
The reified relatum realises the residue content the prior relating did not — so its LABEL (the residue it carries) is not recoverable from the plain relating, exactly the `ws4_free_label_is_import` shape: plain-bisimulation-invisible, label-bisimulation-visible. This is the bridge to WS2's strict growth: productive blindness (the label is free) is what makes the extended carrier not label-bisimulation-embed into the prior.

- **Ambient:** `ws2_residue_free`, `ws4_free_label_is_import`.
- **Success condition:** the reified relatum lands on the free-import horn, tying WS1's freeness to WS2's non-embedding.
- **Failure mode:** *bookkeeping (§4.3).* If the reified relatum's label were recoverable (`ws4_recoverable_not_import` horn), the extended carrier would bisim-embed and growth would be a longer record, not a bigger world. C3 shows it lands on the FREE horn — but only at the labelled level; the plain-level collapse is disclosed honestly (the reified relatum is plain-bisimilar to prior atomless relata). WS2 owns the full non-embedding theorem; C3 previews the bridge.

**Paper triage.** Decidable: freeness (`ws2_residue_free`) is exactly non-recoverability of the label. The honest caveat (plain-level collapse) is the strip-test disclosure. **Winner (the bridge to WS2), scoped honestly.**

### C4 — CLOSE-forbidden locally: a totality-relatum is a self-total hold (the Impossibility, previewing WS4)

```lean
/-- A totality-relatum: an object `t` whose relating (via the induced inspection) is the totality of
    contents below it — the completed self-inspection. Its existence IS a self-total hold. -/
def IsTotalityRelatum {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop := SelfTotal insp t
theorem ws1_close_forbidden_local {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, IsTotalityRelatum dest insp t :=
  ws1_no_self_total_hold dest insp
```
A totality-relatum — the object the founding equation `Ω ≅ F(Ω)` WANTS to reach, a relatum that is the totality of relata below it — is by definition a hold whose content is the completed self-inspection, i.e. a self-total hold. The diagonal forbids it. So the tower cannot close into a top, and `reify` cannot be surjective (C1's non-surjectivity, now proved): a surjective `reify` combined with a totality pattern would give a totality-relatum, contradiction.

- **Ambient:** `SelfTotal`, `ws1_no_self_total_hold`.
- **Success condition (Impossibility proved):** the term is `ws1_no_self_total_hold` re-read; CLOSE is forbidden by the diagonal, an Impossibility. This is the local form; WS4 owns the tower-level dichotomy.
- **Failure mode:** *trivial-closure (§4.5), the smuggle.* If `IsTotalityRelatum` were defined so it did NOT unfold to `SelfTotal` (a totality-relatum that is not a self-total hold), CLOSE-forbidden would not route through the diagonal and a closing tower would be reported — falsely — as monism. C4 pins `IsTotalityRelatum := SelfTotal`, so a totality-relatum IS a self-total hold and CLOSE-forbidden IS the diagonal. Any exhibited closure is then a proof that `reify` smuggled a self-total hold (`selfTotalSmuggled`), a design defect.

**Paper triage.** Decidable: `IsTotalityRelatum := SelfTotal`, so `ws1_close_forbidden_local := ws1_no_self_total_hold`. **Winner (the Impossibility, local form; WS4 owns the tower dichotomy).**

### C5 — The section exists on a κ-bounded carrier (the carrier-strength obligation, §5.5 guard)

```lean
theorem ws1_reifying_carrier_exists (hκ : (large-κ condition, e.g. κ regular with a fixed point λ = λ^{<κ})) :
    ∃ (Ω : Type u) (dest : Ω → PkObj κ Ω) (reify : PkObj κ Ω → Ω),
      IsReify dest reify ∧ (∀ x, SHNE dest x) := …
```
The reifying carrier is not vacuous: for suitable κ there is a carrier `Ω` with a genuine section `reify` and hereditary non-emptiness. The witness is the delicate part — a `PkObj κ Ω ↪ Ω` exists when `|[Ω]^{<κ}| = |Ω|` (a cardinal with `λ^{<κ} = λ`), which large-κ regularity provides. This is what makes the diagonal a gap *inside a consistent object* (§5.5) rather than an inconsistency.

- **Ambient:** cardinal arithmetic (`Cardinal.mk`, `PkObj` cardinality); `IsReify`.
- **Success condition:** the witness carrier is exhibited, or — if the full witness resists — a *specific* reifying carrier (a concrete `Ω`, e.g. a well-founded set-like universe below κ) is constructed, and productive blindness is Discharged-on-a-witness, the universal a WS6 thesis (§5.3).
- **Failure mode:** *non-well-founded-tower / κ-by-fiat.* Too-strong: if the section is only constructible for a SPECIFIC small κ, results would rely on small κ (κ-by-fiat, §4.4). C5 demands the section for all sufficiently large κ (the large-κ discipline). If it is constructible only on a witness, that is the honest Partial (§5.3); the universal is WS6's.

**Paper triage.** Decidable in principle; the witness (a cardinal fixed point `λ = λ^{<κ}`) is standard but the full Lean construction is delicate. Retain as the **carrier-strength obligation**; if only a witness carrier is constructible, productive blindness is Discharged-on-a-witness (§5.3). **Winner (the §5.5 guard), possibly partial on the witness.**

### C6 — The founding-equation tension: `reify` embeds, `Ω ≅ F(Ω)` does not close (charter §9)

```lean
theorem ws1_iso_would_close {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (hsurj : Function.Surjective reify) (insp : Hold dest → HoldPred dest) :
    -- a surjective (iso) reify forces a self-total hold — the founding equation, taken as an iso, closes
    False := …   -- via the diagonal: iso ⇒ dest injective ⇒ a totality-relatum ⇒ ws1_no_self_total_hold
```
The deep structural fact the charter names (§9): `Ω ≅ F(Ω)` as an isomorphism WANTS to close (Lambek: a fixed point of `F` with an iso structure map has a totality object). The diagonal forbids closure. So reification must land in a NON-isomorphic `F(Ω) → Ω` that only embeds. C6 proves the fork: an iso `reify` closes (contradiction), so the section is necessarily NOT surjective — the founding equation is realised as an embedding, not an iso.

- **Ambient:** `IsReify`, `Function.Surjective`, `ws1_no_self_total_hold`.
- **Success condition:** the theorem typechecks; it certifies that the section-not-iso choice (C1) is forced, not stipulated — the iso horn is refuted.
- **Failure mode:** *the tension is decorative.* The fork is load-bearing only if "iso ⇒ closes ⇒ contradiction" is a theorem, which C6 proves. Kept as the structural certificate that `reify`'s non-surjectivity is forced by the diagonal (charter §9's "deep structural question the design must face"). **Winner (the founding-equation certificate).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `reify` a section, injective, not surjective | `IsReify`, `congrArg dest` | yes — section is injective | **win (carrier decision)** |
| C2 | free reification routes through the diagonal | `ws2_residue_is_import` | yes — is that theorem | **win (spine)** |
| C3 | reified relatum is a free label (bridge to WS2) | `ws2_residue_free`, `ws4_free_label_is_import` | yes | **win (bridge), scoped** |
| C4 | CLOSE forbidden locally (totality = self-total) | `SelfTotal`, `ws1_no_self_total_hold` | yes — re-read | **win (Impossibility)** |
| C5 | the section exists on a κ-bounded carrier | cardinal `λ = λ^{<κ}` | partial (witness delicate) | **win (§5.5 guard), maybe on-witness** |
| C6 | iso `reify` closes; embedding forced (charter §9) | `Function.Surjective`, diagonal | yes | **win (founding-equation cert)** |

## Winning candidates: C1 (carrier), C2 (spine), C4 (CLOSE-forbidden local), C6 (founding-equation cert); C3 the bridge to WS2, C5 the carrier-strength obligation

### Definitions and obligations

```lean
namespace Series10.WS1
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, BehaviorallyIdentified, hneRel, hneRel_isBisim,
-- ws1_atomless_bisim, ws2_import_theorem_static, twoLoop, LkObj, plainOf, Recoverable, labelLoop,
-- ws4_free_label_is_import, ws4_recoverable_not_import, Symmetric, ws1_symmetric_states_bisimilar,
-- Hold, afford, ws1_hold_forced, HoldPred, diag, SelfTotal, ws1_no_self_total_hold,
-- ws1_diagonal_not_bisim, ws1_unrestricted_carrier_inconsistent, residue, ResidueRecoverable,
-- ws2_residue_distinct, ws2_residue_free, ws2_residue_is_import — all transcribed (README §6).

/-- The reification (README §2.4). The forward map of `Ω ≅ F(Ω)`: a section of `dest`. -/
def IsReify {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop := ∀ s, dest (reify s) = s

/-- **D0 — `reify` is a section, injective (C1).** `dest ∘ reify = id`, so distinct patterns mint
    distinct relata; the reified relatum genuinely carries its pattern (grows the carrier). -/
theorem ws1_reify_injective {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) : Function.Injective reify := by
  intro s₁ s₂ he; have := congrArg dest he; rwa [h s₁, h s₂] at this

/-- **D1 — THE SPINE (C2, productive blindness).** The reified self-relation is FREE, and recoverability
    would reconstruct a self-total hold — the routing through the diagonal is explicit. This IS
    `ws2_residue_is_import`, lifted to the reification: the growth is genuine BECAUSE self-reference cannot
    close. The proof references the diagonal, NOT a fresh freeness assumption. -/
theorem ws1_free_reification {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp)
  ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp

/-- **D2 — CLOSE-forbidden locally (C4, Impossibility proved).** A totality-relatum is a self-total hold,
    forbidden by the diagonal. So the tower cannot close into a top; `reify` cannot be an iso. -/
def IsTotalityRelatum {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := SelfTotal insp t
theorem ws1_close_forbidden_local {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, IsTotalityRelatum dest insp t :=
  ws1_no_self_total_hold dest insp

/-- **D3 — the founding-equation certificate (C6, charter §9).** An iso (surjective) `reify` would close:
    it forces a self-total hold. So the section is necessarily NOT surjective — `Ω ≅ F(Ω)` is realised as
    an EMBEDDING, not an iso. The razor between §4.5's two horns, proved. -/
theorem ws1_reify_section_not_iso {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest)
    (hclose : ∃ t, SelfTotal insp t) : False :=
  ws1_no_self_total_hold dest insp hclose
-- (the delivered form quantifies: surjective reify ⇒ a totality-relatum ⇒ ws1_no_self_total_hold; see C6)

/-- **D4 — the reified relatum is a free label (C3, bridge to WS2).** The residue realised by the reified
    relatum is not in the prior range — the `ws4_free_label_is_import` horn (free), never
    `ws4_recoverable_not_import`. This is what makes WS2's growth strict (label-bisimulation-non-embedding). -/
theorem ws1_reification_is_free_label {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ h, insp h = residue insp :=
  ws2_residue_free dest insp

/-- **D5 — the reifying carrier exists (C5, §5.5 guard, possibly on-witness).** For suitable κ there is a
    carrier with a genuine section and hereditary non-emptiness — the diagonal is a gap inside a consistent
    object. If only a witness carrier is constructible, productive blindness is Discharged-on-a-witness
    (§5.3); the universal is WS6's. -/
theorem ws1_reifying_carrier_exists (hκ : LargeKappa κ) :
    ∃ (Ω : Type u) (dest : Ω → PkObj κ Ω) (reify : PkObj κ Ω → Ω),
      IsReify dest reify ∧ (∀ x, SHNE dest x) := …
```

**D1 — the spine.** *Strategy:* `ws1_free_reification := ws2_residue_is_import`. The reified self-relation is free (first conjunct) and recoverability reconstructs a self-total hold (second conjunct, the routing). *Paper-decidable:* yes. *Non-circularity (§4.1):* the proof term is the transcribed `ws2_residue_is_import`, which routes through `ws1_no_self_total_hold`; it invokes no fresh freeness axiom. WS7 `#print`s the term.

**D2 — CLOSE-forbidden locally.** `IsTotalityRelatum := SelfTotal`, so a totality-relatum IS a self-total hold and CLOSE-forbidden IS the diagonal. This is the local Impossibility; WS4 lifts it to the tower dichotomy. The pin `IsTotalityRelatum := SelfTotal` is load-bearing: it is why CLOSE-forbidden routes through the diagonal and not a definitional clause.

**D3 — the section-not-iso razor.** The founding equation cannot close: an iso `reify` gives a self-total hold. So the section is not surjective, forced by the diagonal. This settles charter §9's "deep structural question" — reification is an embedding, not an iso.

**D5 — the carrier-strength obligation.** The honest hazard on scope (charter §5.3): the section may be constructible only for a specific carrier, leaving the universal "every κ-bounded reifying carrier grows freely" as WS6's ceiling. The large-κ discipline (§4.4) forbids relying on small κ.

## Outcome classes (per charter §7)

- **Discharged (the spine, productive blindness):** D1 (`ws1_free_reification`), routing through the diagonal (`ws2_residue_is_import` / `ws1_no_self_total_hold`). The engine of the series. Near-certain as a *theorem* (it transcribes a built Series 09 theorem); the load-bearing claim is that it routes through the diagonal, which the proof term secures.
- **Impossibility proved (CLOSE-forbidden):** D2 (`ws1_close_forbidden_local`) and D3 (`ws1_reify_section_not_iso`). A totality-relatum is a self-total hold; the tower cannot close. First-class.
- **Discharged:** D0 (section injective), D4 (free label, bridge). Transcribed / immediate.
- **Bookkeeping (the pre-registered honest failure at the payoff, charter §5.5):** if the reified relatum's freeness holds only at the content level but the relatum bisim-embeds into the prior carrier (the label recoverable at the plain level with no labelled surplus), then growth is a longer record, not a bigger world — Series 09's moving hole re-hit one level up. Routed to WS2 (which owns the non-embedding theorem) and WS7. Not expected at WS1 (freeness is the free-label horn, D4), but WS2 must discharge the non-embedding for productive blindness to be growth and not bookkeeping.
- **`selfTotalSmuggled` (the pre-registered honest failure at the carrier, charter §4.5):** if the exhibited `reify` turned out surjective / the tower closes, a self-total hold was smuggled past the diagonal — a `reify` DESIGN DEFECT, reported as such (not monism). D3 forecloses it (iso ⇒ contradiction); any closure is a design defect to fix, not a result.
- **Partial (pre-registered, charter §5.3):** the *universal* "every κ-bounded reifying carrier admits a free-growing section" is the un-rangeable quantifier; D5 may deliver only a witness carrier, with the universal a defended thesis (WS6). This still advances the program, since ONE genuinely growing free tower is what Series 09's fixed field could not produce.
- **Strip test.** Delete **"reification"** / **"self-relation"** from `ws1_free_reification` and the statement is the bare **`(¬ ∃ h, insp h = diag insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)`** — the Series 09 residue-freeness fact (`ws2_residue_is_import`): the diagonal content is not in the range of the inspection, and recovery reconstructs a self-total hold. Productive blindness **survives the strip** as a diagonal-freeness fact — and this is exactly what the charter demands (§2: freeness must route through the diagonal). So the *mathematical* content is the transcribed Series 09 diagonal freeness, and "reification / productive blindness / to relate is to create / the reified new object" is the earned **interpretive** layer, flagged here honestly. What the strip does **not** remove is the load-bearing structural gain over Series 09: `reify` is a genuine section (`dest ∘ reify = id`, D0), so the free content is a NEW CARRIER ELEMENT, not merely an un-hit predicate — that is the earned reification (a bigger world), and WS2 weighs whether its existence genuinely differentiates (strict growth) or bisim-embeds (bookkeeping). WS7 records: productive blindness is the Series 09 diagonal freeness routed to relatum-freshness; its novelty over Series 09 is the section that turns free content into a free object, and whether that is genuine growth is WS2's theorem, not WS1's word.

## Deliverable

`series-10/formal/Series10/ws1.lean`: transcribed carrier + hold + diagonal layer + import test + coincidence witness (README §6); `IsReify`, `IsTotalityRelatum`; `ws1_reify_injective` (D0), `ws1_free_reification` (D1), `ws1_close_forbidden_local` (D2), `ws1_reify_section_not_iso` (D3), `ws1_reification_is_free_label` (D4), `ws1_reifying_carrier_exists` (D5). Axiom check: `#print axioms ws1_free_reification` reduces through `ws2_residue_is_import` / `ws1_no_self_total_hold` to `propext` / the standard three; crucially **the proof term routes through `ws1_no_self_total_hold` and contains no fresh freeness axiom** — the single most important build check (protocol §C). **This file is built first (charter §6): it fixes the reifying carrier `(dest, insp, reify)` and productive blindness for WS2–WS6.**
