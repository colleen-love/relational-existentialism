# WS2 — Genuine growth, not bookkeeping

**Design doc. Series 10, the payoff. Owns: the reified relatum genuinely grows the carrier — `Ω_{α+1}` does NOT bisimulation-embed into `Ω_α` (strict internal growth, a bigger world, not a longer `List`) — and two objects with distinct reification histories are not merged by `BehaviorallyIdentified` (breaks the Series 07 collapse where Series 09's moving hole could not). The direct repair of Series 09's moving hole: a free reified relatum differentiates by its EXISTENCE, where the residue only relocated.**

*Series 10 is standalone; the collapse engine (`ws1_atomless_bisim`, `hneRel_isBisim`, `ws2_import_theorem_static`) and the semantic import test (`ws4_free_label_is_import`, `ws4_recoverable_not_import`, `Recoverable`, `plainOf`, `labelLoop`, `ws4_label_survives_quotient`) are transcribed into `series-10/formal/Series10/ws2.lean`, re-namespaced `Series10.WS2` (see `spec/README.md` §6). WS2's growth is stated with **WS1's freeness as the load-bearing hypothesis** (charter §6, protocol §4): the extended carrier fails to bisim-embed only if the reified relatum is genuinely free (not recoverable), which WS1's `ws1_free_reification` secures. The genuinely new Lean is `ws2_growth_strict` and `ws2_history_not_merged`; the non-embedding re-reads `ws4_label_survives_quotient`.*

## The object at stake

The charter's Consequence 1 and 2 (§2, §5.2): Series 09's residue was bisimulation-invariant — it moved, but its shape was the same everywhere, so two towers relating alike were still collapsible by the engine (`ws1_atomless_bisim`: any two atomless states are bisimilar). Series 10's reified relatum is FREE (WS1): its EXISTENCE differentiates. The two obligations:

- **Strict internal growth (the bookkeeping check, PROMOTED to first-class, protocol §0.4).** `Ω_{α+1}` — the carrier extended by the reified free relatum — does NOT bisimulation-embed into `Ω_α`. The new relatum is genuinely absent from the prior carrier (up to bisimulation), so growth is a bigger world, not a lengthening `List`/index recorded on the side (Series 09's `accResidue` ghost, series-review-1 F-8, at the carrier level). This is the exact repair of the moving hole: a moving hole (bisimulation-invariant) still embeds; a free relatum (bisimulation-visible) does not.
- **Breaks the Series 07 collapse.** Two objects with distinct reification histories differ in which relata exist for them, and existence-of-a-free-relatum is not bisimulation-invariant, so `BehaviorallyIdentified` does not force them equal. Series 09's moving hole WAS bisimulation-invariant and so was still merged; the reified relatum is not.

The design must be scrupulous about the level at which non-embedding holds — this is the payoff most at risk of being Series 09's moving hole wearing the word "growth." The honest architecture: at the PLAIN level, the collapse engine still merges (any two atomless relata are plain-bisimilar, `ws1_atomless_bisim`), so plain-level non-embedding is FALSE and claiming it would be a lie. Genuine growth lives at the LABELLED level: the reified relatum carries the free residue as a label, and `ws4_label_survives_quotient` shows the label is not label-bisimulation-recoverable — so `Ω_{α+1}` does not LABEL-bisimulation-embed into `Ω_α`. WS2 states this level explicitly and does not oversell it; the strip test flags that "growth," deleted, leaves `ws4_free_label_is_import`, and **Bookkeeping is the pre-registered honest alternative** if a reviewer judges the label external (Series 09's moving hole re-hit one level up). WS7 adjudicates.

**Ambient theory.** `spec/README.md` §2.1 (collapse engine: `ws1_atomless_bisim`, `hneRel_isBisim`, `ws2_import_theorem_static`), §2.2 (import test: `LkObj`, `IsBisimL`, `plainOf`, `Recoverable`, `labelLoop`, `ws4_free_label_is_import`, `ws4_label_survives_quotient`), §2.3–§2.4 (WS1's `ws1_free_reification`, `residue`, `ws2_residue_free`). All transcribed.

## Candidates

### C1 — Strict growth: the extended carrier does not label-bisimulation-embed (the lead)

```lean
/-- A label-bisimulation EMBEDDING of `Ω_α` into `Ω_{α+1}`: a label-bisimulation relating every prior
    relatum to some relatum, that MISSES the reified relatum (it embeds the old world unchanged). Strict
    growth is the NEGATION: no such embedding exists, because the reified relatum's label is free. -/
def BisimEmbeds {Q X : Type u} (dest : X → LkObj κ Q X) (new : X) : Prop :=
  ∃ R, IsBisimL dest R ∧ (∀ x, ∃ y, R x y) ∧ (∀ x, ¬ R x new)   -- old world embeds, missing `new`
theorem ws2_growth_strict (hinf : ℵ₀ ≤ κ) :
    -- the reified free relatum (the free label) is NOT bisim-embedded away: growth is strict
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ := ws4_label_survives_quotient hinf
```
Strict growth is the failure of the old world to bisim-embed into the extended one with the reified relatum quotiented away. Concretely, transcribing `ws4_label_survives_quotient`: the reified relatum (carrying the free residue as its label) is not label-bisimilar to any prior relatum, so it cannot be embedded away. The carrier is genuinely bigger.

- **Ambient:** `IsBisimL`, `labelLoop`, `ws4_label_survives_quotient` (the built non-recoverability).
- **Success condition (Discharged, at the labelled level):** the reified relatum is not label-bisimilar to the prior relata, so `Ω_{α+1}` does not label-bisim-embed into `Ω_α` — strict internal growth, secured by WS1's freeness.
- **Failure mode:** *bookkeeping (§4.3).* If the non-embedding held only for an external `List`/index while the carrier were label-bisimulation-constant, growth would be a longer record. C1 forecloses it AT THE LABELLED LEVEL: the reified relatum's label (the free residue) is genuinely absent from the prior carrier (`ws4_label_survives_quotient` / `ws2_residue_free`). The honest caveat: at the PLAIN level the collapse engine merges, so growth is NOT plain-strict — disclosed in the strip test, adjudicated by WS7.

**Paper triage.** Decidable: the non-embedding IS `ws4_label_survives_quotient` (a built Series 09/08 theorem), re-read as the reified relatum surviving the bisimulation quotient. **Winner (strict growth, at the labelled level).**

### C2 — Growth is the free-label import: the residue reified is not recoverable (the certificate)

```lean
theorem ws2_growth_is_free_label (hinf : ℵ₀ ≤ κ) :
    -- the reified relatum is plain-bisimilar to prior relata (plain-invisible) …
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
    -- … but NOT label-bisimilar: FREE, the `ws4_free_label_is_import` horn — genuine growth, not recovered
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf
```
Growth lands on the `ws4_free_label_is_import` horn: the reified relatum is plain-bisimulation-invisible (the collapse engine would merge it) but label-bisimulation-visible (its free label differentiates). This is the precise sense in which reification breaks the collapse where the moving hole could not — the moving hole was plain-invisible AND label-invisible (bisimulation-invariant), so it was merged; the reified relatum is label-visible, so it is not.

- **Ambient:** `ws4_free_label_is_import`, `plainOf`, `IsBisimL`.
- **Success condition:** growth is certified as a genuine import (free), not a recovered distinction — the `ws4_recoverable_not_import` horn (which would be Bookkeeping) is avoided.
- **Failure mode:** *bookkeeping / import.* This candidate IS the bookkeeping check as a theorem: it shows the reified relatum is on the FREE horn (genuine) not the RECOVERABLE horn (collapse). If a reified relatum landed on the recoverable horn, growth would be bookkeeping. C2 shows the free residue lands free. **Winner (the growth-is-import certificate, the bookkeeping check discharged).**

### C3 — Distinct reification histories are not merged (breaks the Series 07 collapse)

```lean
theorem ws2_history_not_merged (hinf : ℵ₀ ≤ κ) :
    -- BehaviorallyIdentified at the LABELLED level does not force two distinct-history relata equal:
    -- the free label distinguishes them, so the Series 07 collapse (which merges relate-alike) fails here.
    ¬ (BehaviorallyIdentifiedL (labelLoop hinf) → ⟨true⟩ = ⟨false⟩) := …
    -- i.e. there are two relata, plain-bisimilar (relate alike plainly) but with distinct free labels,
    -- that BehaviorallyIdentified does NOT merge — because existence-of-a-free-relatum is not bisim-invariant
```
Two objects with distinct reification histories (`⟨true⟩` reified one free relatum, `⟨false⟩` another) relate alike PLAINLY (the collapse engine would merge them, `ws1_atomless_bisim`) but carry distinct free labels, so `BehaviorallyIdentified` does not force them equal. Series 09's moving hole was bisimulation-invariant (same free label everywhere), so `BehaviorallyIdentified` DID merge; the reified relatum's free label breaks this.

- **Ambient:** `BehaviorallyIdentifiedL`, `ws1_atomless_bisim`, `ws4_label_survives_quotient`.
- **Success condition (Discharged):** the two distinct-history relata are not merged at the labelled level, so reification breaks the Series 07 collapse where Series 09's moving hole (bisimulation-invariant) was still merged (charter §5.2).
- **Failure mode:** *trivial-closure / bookkeeping.* If the two histories were label-bisimilar after all (the labels recoverable), they would merge and the collapse would stand — Bookkeeping. C3 shows they are not label-bisimilar (`ws4_label_survives_quotient`). The honest caveat: they ARE plain-bisimilar (the collapse engine still merges plainly), so the break is at the labelled level only — the same disclosure as C1. **Winner (breaks the collapse, at the labelled level).**

### C4 — The plain-level collapse still holds (the honest disclosure, not a payoff)

```lean
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    -- at the PLAIN level the collapse engine still merges: any two atomless relata are plain-bisimilar.
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩
```
The honest disclosure the whole payoff must carry: at the PLAIN (label-forgetting) level, the collapse engine (`ws1_atomless_bisim`) still merges the two distinct-history relata — they are plain-bisimilar. Growth and the break of the collapse live EXACTLY at the labelled level, where the free label survives. This is not a defect; it is the precise location of genuine growth, and stating it is what keeps WS2 from overclaiming plain-level non-embedding (which is false).

- **Ambient:** `plainOf`, `plainOf_labelLoop_true_bisim`.
- **Success condition:** the disclosure is stated as a theorem, so the level of growth is pinned and cannot be silently inflated to the plain level.
- **Failure mode:** *overclaim.* Without C4, a reviewer could read C1/C3 as claiming plain-level growth, which is false (the engine merges). C4 pins the level. **Winner (the honest disclosure, the anti-overclaim pin).**

### C5 — The moving hole re-hit refuted: existence differentiates where relocation did not (the direct repair)

```lean
theorem ws2_not_moving_hole (hinf : ℵ₀ ≤ κ) :
    -- Series 09's residue was bisimulation-invariant (a moving hole embeds); the reified relatum is not.
    -- The contrast IN ONE STATEMENT: the residue content is realised nowhere (free, moves) …
    (∀ h, insp h ≠ residue insp)
    -- … whereas the reified relatum EXISTS in Ω_{α+1} and its label is not bisim-recoverable (does not embed).
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) := …
```
The direct repair of Series 09's moving hole, stated as a contrast: Series 09's residue was a content realised by no relatum (it moved but never became an object, bisimulation-invariant); Series 10's reified relatum EXISTS as an object whose free label does not bisim-embed. Relocation (Series 09) vs. generation (Series 10): the difference is that the reified relatum is a new carrier element, and existence-of-a-free-relatum is not bisimulation-invariant.

- **Ambient:** `ws2_residue_distinct`, `ws4_label_survives_quotient`.
- **Success condition:** the contrast typechecks; it certifies that Series 10 does what Series 09 could not — generation, not relocation.
- **Failure mode:** *bookkeeping (the moving hole re-hit).* If the reified relatum turned out bisimulation-invariant after all (like the moving hole), this would collapse to Series 09's limitation. C5 shows the free label is bisimulation-visible. **Winner (the direct repair), the headline contrast.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `Ω_{α+1}` does not label-bisim-embed into `Ω_α` | `ws4_label_survives_quotient` | yes — that theorem | **win (strict growth, labelled)** |
| C2 | growth is the free-label import (bookkeeping check) | `ws4_free_label_is_import` | yes — that theorem | **win (growth-is-import cert)** |
| C3 | distinct histories not merged (breaks collapse) | `BehaviorallyIdentifiedL`, non-recovery | yes | **win (breaks the collapse, labelled)** |
| C4 | plain-level collapse persists (disclosure) | `plainOf_labelLoop_true_bisim` | yes | **win (honest disclosure)** |
| C5 | existence differentiates, not relocation (repair) | `ws2_residue_distinct` + non-recovery | yes | **win (direct repair, headline)** |

## Winning candidates: C1 (strict growth) + C2 (growth-is-import) + C3 (breaks the collapse) + C5 (the repair); C4 the honest disclosure

### Definitions and obligations (cite `spec/README.md` §2; consume WS1)

```lean
namespace Series10.WS2
-- collapse engine (ws1_atomless_bisim, hneRel_isBisim, ws2_import_theorem_static), import test
-- (LkObj, IsBisimL, BehaviorallyIdentifiedL, plainOf, Recoverable, labelLoop, ws4_free_label_is_import,
-- ws4_recoverable_not_import, ws4_label_survives_quotient, plainOf_labelLoop_true_bisim), and
-- ws1_free_reification, residue, ws2_residue_free, ws2_residue_distinct from WS1 — transcribed (README §6).

/-- **D1 — strict internal growth (C1).** The reified free relatum is not label-bisimilar to any prior
    relatum, so `Ω_{α+1}` does NOT label-bisimulation-embed into `Ω_α`: growth is a bigger world, not a
    lengthening record. Secured by WS1's freeness (`ws2_residue_free` / `ws4_label_survives_quotient`). -/
theorem ws2_growth_strict (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ws4_label_survives_quotient hinf

/-- **D2 — growth is the free-label import (C2, the bookkeeping check discharged).** The reified relatum
    is plain-invisible (the collapse engine would merge it) but label-visible (FREE) — the
    `ws4_free_label_is_import` horn, never `ws4_recoverable_not_import`. Genuine growth, not recovered. -/
theorem ws2_growth_is_free_label (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D3 — distinct histories not merged (C3, breaks the Series 07 collapse).** Two distinct-history
    relata carry distinct free labels, so `BehaviorallyIdentified` does not merge them — where Series 09's
    moving hole (bisimulation-invariant) was still merged. -/
theorem ws2_history_not_merged (hinf : ℵ₀ ≤ κ) :
    (∀ (R : ULift Bool → ULift Bool → Prop), IsBisimL (labelLoop hinf) R → R ⟨true⟩ ⟨false⟩ → ⟨true⟩ = ⟨false⟩)
    → False := fun hmerge => by
  exact ws2_growth_strict hinf ⟨_, /- the all-plain-true label bisim is not a label-bisim -/ …⟩
  -- delivered form: BehaviorallyIdentifiedL forces equality only if the labels are recoverable; they are not.

/-- **D4 — the honest disclosure (C4, the anti-overclaim pin).** At the PLAIN level the collapse engine
    still merges: growth and the break of the collapse live at the LABELLED level only. Stated so the level
    of growth cannot be silently inflated. -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩

/-- **D5 — the direct repair, the headline contrast (C5).** Series 09's residue moved but never became an
    object (bisimulation-invariant); Series 10's reified relatum EXISTS and its free label does not embed.
    Generation, not relocation — existence differentiates where the moving hole did not. -/
theorem ws2_not_moving_hole {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hinf : ℵ₀ ≤ κ) :
    (∀ h, insp h ≠ residue insp)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws2_residue_distinct dest insp, ws2_growth_strict hinf⟩
```

**D1/D2 are the payoff:** strict growth (D1) certified as a genuine free import (D2, the bookkeeping check discharged). The mathematical work is the transcribed `ws4_label_survives_quotient` / `ws4_free_label_is_import`, re-read as the reified relatum surviving the bisimulation quotient. **D3** breaks the Series 07 collapse at the labelled level. **D4** is the honest disclosure that keeps the level pinned — the plain-level collapse persists, so growth is not plain-strict. **D5** is the headline contrast with Series 09's moving hole. The cross-workstream review (protocol §D) must confirm the edge: WS2's strict growth depends on WS1's `ws1_free_reification` being genuine (routing through the diagonal, not a fresh assumption) — laundered through a fresh-assumption freeness, growth would be asserted, not earned.

## Outcome classes (per charter §7)

- **Discharged (strict internal growth, at the labelled level):** D1, D2, D3, D5 — the reified free relatum does not label-bisimulation-embed, is on the free-import horn, is not merged by `BehaviorallyIdentified`, and differentiates by existence where the moving hole relocated. This is the direct repair of Series 09's moving hole (charter §8.2), at the labelled level.
- **Discharged (the honest disclosure):** D4 — the plain-level collapse persists; the level of growth is pinned.
- **Bookkeeping (the pre-registered honest failure, the cardinal sin, charter §5.5, protocol §0.4):** if a reviewer judges the free label EXTERNAL — that the only non-embedding is at a labelled level the reviewer deems a `List`/index laid beside a plain-bisimulation-constant carrier — then growth is Series 09's moving hole re-hit one level up, and the payoff is **Bookkeeping**, a SERIOUS finding, reported honestly (not buried). The design pre-registers this: WS2's growth is labelled-level, and whether the label is genuine internal carrier structure or an external record is the adjudication WS7 owns. The Series 10 defense: the label IS the reified relatum's relating (it carries the free residue as its `dest`-content), not a side record — but the charter demands this be earned, and if it fails, Bookkeeping is the honest terminus (a success outcome, not a failure).
- **`selfTotalSmuggled` (inherited from WS1):** if WS1's `reify` closed the tower, growth would be into a self-total hold — a design defect, routed to WS7. Not expected (WS1 D3 forecloses it).
- **Partial (pre-registered, charter §5.3):** the *universal* "every reified relatum on every carrier grows strictly" is open; D1 claims it on the `labelLoop` witness, the universal a defended thesis (WS6).
- **Strip test.** Delete **"growth"** / **"tower"** from `ws2_growth_strict` and the statement is the bare **`¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩`** — the Series 09/08 fact that a free label is not label-bisimulation-recoverable (`ws4_label_survives_quotient`). The payoff **survives the strip** as a bisimulation-non-embedding fact — so the *mathematical* content is the free label surviving the quotient, and "growth / a bigger world / the growing self / genuine plurality" is the earned reading. WS2 does **not** claim the strip leaves nothing; it claims the non-embedding is a genuine strict-growth fact at the labelled level and names the interpretive surplus. What the strip does **not** remove is the load-bearing structural gain over Series 09: the reified relatum EXISTS as a carrier element (WS1's section, `dest ∘ reify = id`), so the non-embedding is about a bigger carrier, not a relocated hole — that is the earned repair, and WS7 weighs directly whether the label is internal carrier structure (genuine growth) or an external record (Bookkeeping). This is the single sharpest strip in the series, because it is exactly where the moving-hole re-hit would show.

## Deliverable

`series-10/formal/Series10/ws2.lean`: transcribed collapse engine + import test (README §6); `ws2_growth_strict` (D1), `ws2_growth_is_free_label` (D2), `ws2_history_not_merged` (D3), `ws2_plain_collapse_persists` (D4), `ws2_not_moving_hole` (D5). Axiom check: `#print axioms ws2_growth_strict` reduces through `ws4_label_survives_quotient` to `propext` / the standard three. **Depends on WS1** (`ws1_free_reification` secures the reified relatum's freeness; the ledger records the edge). **The most important build check (protocol §C):** confirm `ws2_growth_strict` proves `Ω_{α+1}` does NOT bisim-embed into `Ω_α` (genuine strict internal growth at the labelled level); if the non-embedding reduces to a lengthening `List`/index while the carrier is bisimulation-constant, the payoff is **Bookkeeping**, Series 09's moving hole re-hit, recorded honestly. This is the payoff the series exists to test; WS7 weighs whether the labelled-level growth is a bigger world or an external record.
