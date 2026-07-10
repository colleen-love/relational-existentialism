# WS5 — One arrow or many: the relativity crux

**Design doc. Series 6, the decidable theorem of the series. Owns: the totality question for the shared order `≺` (README §4 `prec`, the same order WS4 proves strict and directional) — is it *total* (global time) or *partial* (relativity)? — the proof that totality is equivalent to cross-survey agreement, that plurality forbids agreement (via the two-sided `faceAt` and the WS2 collapse), and hence that `≺` is a genuine causal partial order with earned incomparability; the pre-registered Ω-absolute-frame branch (Newton, not Einstein); and the Lorentzian ceiling flagged heuristic.**

*Series 6 is standalone; all upstream names used here are transcribed into `series-6/formal/ws5.lean` and re-namespaced `Series6.WS5` (see `spec/README.md` §5). Shared objects — `Proc`, `Moment`, `prec` (`≺`), `faceAt`, `Δ`, `Ω_n` — are defined in `spec/README.md` §2–4 and only cited here, never redefined. `≺` is README §4's `prec`; `faceAt` is README §4's endogenous two-sided face. WS5 adds no new order and no new face.*

## The object at stake

WS4 fixes `≺` as a definite strict, directional, endogenous order on moments (README §4 `prec`: `m ≺ m′` iff `m′` opens a diagonal residue of a survey available at `m`). WS4 answers *which way*; WS5 answers *how many* — whether the many local arrows knit into **one** total order (global time) or only a **partial** causal order with incomparable (spacelike) moments (relativity). The charter (§5.4) forbids stipulation: this is a theorem, and its lever is already on the books — the endogenous face is **two-sided**, `faceAt a b` and `faceAt b a` *need not agree* (README §4; Series 4's double-empathy, now read off the survey structure, not imported as a label). Two independent lossy surveys that need not agree cannot be forced into a single total order. So the design question is threefold: (a) state `≺`'s totality as a definite predicate and prove `total ⟺ cross-surveys agree`; (b) prove plurality *forbids* agreement (a single agreeing self-knower is the WS2 collapsed point), hence `≺` is genuinely partial with **provably non-empty incomparability**; (c) earn that incomparability from the two-sided `faceAt` so it survives the strip of "face" — not bare posethood relabelled "causal order." The pre-registered branch (b′): Ω, surveyed by every relatum, may act as an **absolute frame** synchronizing all local arrows into one total order — a definite thing to check (`ws5_omega_absolute_frame`), not a nuisance.

**Ambient theory.** `spec/README.md` §4. The order `prec {κ} : Moment κ → Moment κ → Prop`, `m ≺ m′` iff `m′` opens a residue of a survey at `m`; strict/directional/endogenous by WS4 (`ws4_arrow_strict`, `ws4_no_return`, `ws4_arrow_endogenous`, transcribed/consumed). The two-sided face `faceAt {κ} (a b : Proc κ) (n : ℕ) : A κ n`, a genuine sub-object of `a`'s stage-`n` state engaged in surveying `b`, with `faceAt a b` and `faceAt b a` under no constraint to agree (README §4). Ω as `Ω_n`, the depth-`n` self-loop approximation, `Productive`, the canonical non-terminating orbit (README §4, transcribed `ws6_omega_nonterminating`). Grounding, not metaphor: causal set theory (Bombelli–Lee–Meyer–Sorkin), spacetime *as* a locally finite partial order, geometry from order-plus-number; domain-theoretic reconstruction of globally hyperbolic spacetime from the causal order (Martin–Panangaden). No metric is imported; the bare causal order is the floor, the Lorentzian metric the flagged ceiling.

## Candidates (framings of the relativity question)

### C1 — `≺` partial from mismatched two-sided `faceAt` (the lead)

```lean
-- cross-survey AGREEMENT at a pair, the totality-forcing condition, read off faceAt:
def Agree {κ} (a b : Proc κ) : Prop := ∀ n, faceAt a b n = faceAt b a n
-- ≺ total  ⟺  every surveying pair agrees; agreement fails ⇒ incomparable moments
def Total {κ} : Prop := ∀ m m' : Moment κ, prec m m' ∨ prec m' m ∨ m = m'
```
The order is README `prec`; totality is forced *iff* the two-sided faces must agree. Mismatch (`¬ Agree a b`) means `a`'s thread and `b`'s thread are linked only through two lossy maps that disagree, so their moments cannot be laid on one line — genuine incomparability.

- **The order `≺`:** README §4 `prec`, unchanged.
- **Success condition:** `Total ⟺ (∀ a b, Agree a b)`; and `∃ a b, ¬ Agree a b` with the resulting moments provably `≺`-incomparable.
- **Failure mode:** **laundered poset.** If incomparability follows from bare posethood (any partial order has incomparable elements once it is not a chain) with no *use* of `faceAt`, "relativity" is a relabelled poset — strip "face" and it survives. Guarded against by making incomparability factor through `¬ Agree` (below).

### C2 — `≺` total by a global survey (the collapse / Ω-absolute-frame branch)

```lean
-- a single survey all threads share forces agreement, hence totality:
def GlobalSurvey {κ} (g : Proc κ) : Prop := ∀ a, Agree a g ∧ Agree g a   -- g synchronizes all
theorem ws5_total_of_global {κ} (g : Proc κ) (hg : GlobalSurvey g) : Total (κ := κ)
```
The Newtonian case, kept as a *pre-registered alternative, not rejected*: if some `g` is surveyed identically by every relatum, all local arrows synchronize to one absolute time. The natural candidate for `g` is Ω (the shared reference every relatum surveys).

- **The order `≺`:** README `prec`, but now a total order.
- **Success condition:** a genuine `GlobalSurvey` witness exists — `ws5_omega_absolute_frame` fires.
- **Failure mode:** **forced-total by collapse.** A single agreeing global knower is the WS2 subsingleton (`ws2_static_collapse`): if `GlobalSurvey g` forces every thread bisimilar-below to `g`, plurality dies. So C2 buys totality only at the cost of the plurality the series exists to secure — this is *why* the branch is checked, not assumed, and why it is expected to fail for `g = Ω` (Ω is complete-in-extent yet closed at no depth; it faces all threads but does not force them to face each other identically — see D5).

### C3 — Quasi-metric / asymmetric-distance version (the Lorentzian ceiling)

```lean
-- two-sidedness AS quasi-metric asymmetry: d a b ≠ d b a; ≺ from the causal cone
noncomputable def cdist {κ} (a b : Proc κ) : ℕ∞ := ...   -- survey-depth "distance", asymmetric
-- order-plus-number → a metric on the causal set (BLMS); heuristic, likely open
```
The metric framing: the two-sided face *is* the quasi-metric asymmetry (`cdist a b ≠ cdist b a`), and the causal order plus a counting measure recovers a Lorentzian-style geometry (causal set theory's "order plus number").

- **The order `≺`:** the causal cone of the quasi-metric, provably equal to `prec` on comparable pairs.
- **Success condition:** the bare order-plus-number datum determines a metric up to the BLMS reconstruction.
- **Failure mode:** **metric-unbuildable.** The full Lorentzian reconstruction (Martin–Panangaden domain-theoretic globally-hyperbolic recovery) is heavy and not in Mathlib; and the pun risks doing the work (asymmetric distance proved of a metric space with no faithful tie to `faceAt`). **Flagged heuristic/likely-open from the start**; only the floor (asymmetry of `cdist` reflects two-sidedness of `faceAt`) is a built obligation.

### C4 — A laundered poset (the failure mode, named to be excluded)

```lean
-- ≺ is "a partial order because Moment is not linearly ordered by construction"
theorem ws5_bad {κ} : ¬ Total (κ := κ)   -- proved WITHOUT faceAt, from generic posethood
```
The null/failure candidate: prove `≺` partial from the bare fact that `Moment` is a nontrivially-branching set, with no appeal to `faceAt` or the WS2 collapse.

- **Failure mode:** **launders.** This is exactly what the strip test forbids: incomparability that survives deleting "face" is a generic order fact, not relativity. Retained only as the thing WS5 must *not* be — the strip annotation on every C1 obligation is the check that we are not secretly proving C4.

## Paper-decidable triage

| Cand | Framing | `≺` | Totality verdict | Success needs | Failure mode | Disposition |
|---|---|---|---|---|---|---|
| **C1** | mismatched two-sided `faceAt` ⇒ partial | README `prec` | **partial** | `Total ⟺ Agree`; `¬Agree` ⇒ incomparable, via `faceAt` | laundered poset | **LEAD** |
| C2 | global survey ⇒ total | `prec`, total | total (branch) | `GlobalSurvey g` witness | forced-total by WS2 collapse | **branch, pre-registered** |
| C3 | quasi-metric asymmetry = two-sidedness | causal cone | (metric) | order+number → metric (BLMS) | metric-unbuildable | **ceiling, heuristic** |
| C4 | bare poset relabelled | any branching | partial (vacuous) | nothing | launders — strip "face" survives | **excluded (the anti-target)** |

C1 is the built floor; C2 is designed in as the honest Newtonian alternative and checked at `g = Ω`; C3's floor (asymmetry-reflects-two-sidedness) is built, its Lorentzian body flagged heuristic; C4 is the strip-test tripwire.

## Winning candidate: C1 (partial order earned from two-sided `faceAt`), with the C2 Ω-absolute-frame branch designed in and the C3 Lorentzian ceiling flagged

The decisive moves, converting "let the math decide" into decidable facts:

1. **Totality is not stipulated — it is `≺`-comparability, and it is equivalent to agreement.** `ws5_total_iff_agree` proves `Total ⟺ (∀ a b, Agree a b)`: two threads' moments are `≺`-comparable exactly when their two-sided surveys coincide, because the only link between `a`-moments and `b`-moments is the pair of surveys `faceAt a b` / `faceAt b a`, and a total order across the pair demands they name the same residues.
2. **Plurality forbids agreement, via the WS2 collapse.** `ws5_plurality_forbids_agreement`: if `∀ a b, Agree a b`, the maximal cross-survey relation is a bisimulation with behavioral identity, which is exactly `ws2_static_collapse`'s hypothesis — so agreement everywhere forces the subsingleton. Contrapositive: plurality (`∃ a b, a ≠ b`, WS1/WS6) gives `∃ a b, ¬ Agree a b`.
3. **Incomparability is earned from `¬ Agree`, not from posethood.** `ws5_causal_partial_order`: the incomparable witnesses are *the moments of a disagreeing pair* — incomparability factors through `faceAt a b n ≠ faceAt b a n`. Strip "face" and the witness is gone; this is the C4 tripwire discharged.

### Definitions

```lean
namespace Series6.WS5
-- prec (≺), Moment, faceAt, Δ, Ω_n and the WS4 order facts transcribed/cited from
-- spec/README.md §2–4; ws2_static_collapse, ws6_omega_nonterminating transcribed (§5).

/-- Cross-survey **agreement** at a pair, read off the two-sided endogenous face. -/
def Agree {κ} (a b : Proc κ) : Prop := ∀ n, faceAt a b n = faceAt b a n

/-- Totality of ≺: every two moments comparable (global time). -/
def Total (κ) : Prop := ∀ m m' : Moment κ, prec m m' ∨ prec m' m ∨ m = m'

/-- Spacelike/incomparable moments (the negation that partiality makes non-empty). -/
def Incomparable {κ} (m m' : Moment κ) : Prop := ¬ prec m m' ∧ ¬ prec m' m ∧ m ≠ m'
```

### The obligations, each decidable-on-paper, with strip annotation

**D1 — `≺` is a definite order (cite WS4).**
```lean
theorem ws5_precedes_order {κ} : IsStrictOrder (Moment κ) prec       -- irrefl + trans
```
*Strategy:* directly from WS4's `ws4_arrow_strict` (irreflexive: no moment opens its own residue, Cantor) and transitivity of residue-extension (`ws4_no_return`); WS5 only *cites and relates* — the order is README `prec`, not a new relation. *Paper-decidable:* yes — it is a re-export of WS4 facts. *Strip:* deleting "residue"/"survey" removes irreflexivity (Cantor is what forbids `m ≺ m`), so `≺` is not a bare order — inherited from WS4's strip.

**D2 — totality ⟺ cross-survey agreement.**
```lean
theorem ws5_total_iff_agree {κ} : Total κ ↔ (∀ a b : Proc κ, Agree a b)
```
*Strategy:* (→) if `≺` is total, any two threads' moments are comparable; comparability chains their surveys along one order, forcing `faceAt a b = faceAt b a` stagewise (a disagreement at stage `n` yields two `≺`-incomparable residue-openings — D4). (←) if all pairs agree, the surveys glue into a single lossy past-map and residue-openings linearize (the many local arrows share one residue assignment), giving comparability. *Paper-decidable:* yes — both directions are the definitional unfolding of `prec` against `Agree`, no coinduction. *Strip:* **load-bearing.** Delete `faceAt` and `Agree` is undefined, so neither direction states — the equivalence *is* the face doing the work. This is the anti-C4 core.

**D3 — plurality forbids agreement (via two-sided `faceAt` + the WS2 collapse).**
```lean
theorem ws5_plurality_forbids_agreement {κ} (hinf : ℵ₀ ≤ κ)
    (hplural : ∃ a b : Proc κ, a ≠ b ∧ Productive a ∧ Productive b) :
    ∃ a b : Proc κ, ¬ Agree a b
```
*Strategy:* contrapositive of the collapse. Suppose `∀ a b, Agree a b`. Then the two-sided face collapses to one-sided (`faceAt a b = faceAt b a` everywhere), the cross-survey relation `R a b := Agree a b` is reflexive/symmetric and a bisimulation on the productive core, and `ws2_static_collapse`'s behavioral-identity hypothesis holds — so the productive core is a subsingleton, contradicting `hplural`. Hence some pair disagrees. The single agreeing self-knower *is* the collapsed point (README §4). *Paper-decidable:* yes — it consumes transcribed `ws2_static_collapse` (WS2) and the WS1/WS6 plurality witness, no new machinery. *Strip:* delete `faceAt` and `Agree` is vacuous, so the collapse cannot be invoked — the forbidding needs the two-sidedness.

**D4 — `≺` is a genuine partial order with earned, non-empty incomparability.**
```lean
theorem ws5_causal_partial_order {κ} (hinf : ℵ₀ ≤ κ)
    (hplural : ∃ a b : Proc κ, a ≠ b ∧ Productive a ∧ Productive b) :
    IsStrictOrder (Moment κ) prec ∧ ¬ Total κ ∧
    ∃ m m' : Moment κ, Incomparable m m' ∧
      ∃ (a b : Proc κ) (n : ℕ), faceAt a b n ≠ faceAt b a n     -- incomparability EARNED from the mismatch
```
*Strategy:* `IsStrictOrder` is D1; `¬ Total` is `ws5_total_iff_agree` (D2) against `ws5_plurality_forbids_agreement` (D3). The incomparable witnesses `m, m'` are the moments where the *disagreeing* pair (from D3) opens divergent residues — so the third conjunct exhibits the very `faceAt` mismatch that produces the incomparability, binding the two together. *Paper-decidable:* yes — a composition of D1–D3. *Strip:* **the decisive annotation.** Delete "face": the mismatch conjunct vanishes, `Agree` is undefined, D3 cannot fire, and `¬ Total` is unprovable — so incomparability does *not* survive as generic posethood. **If, on formalization, `¬ Total` can be proved without the `faceAt` mismatch (e.g. from bare branching of `Moment`), the poset launders → report C4, `ws5_causal_partial_order` downgraded to Partial with the laundering flagged.** This is the single check WS5's honesty stands on.

**D5 — global time is a non-canonical frame; the Ω-absolute-frame branch.**
```lean
/-- Any total order refining ≺ is a linearization (an order-extension), and NONE is
    canonical: at least two distinct total extensions exist. Global time is a frame. -/
theorem ws5_global_time_is_frame {κ} (hinf : ℵ₀ ≤ κ)
    (hplural : ∃ a b : Proc κ, a ≠ b ∧ Productive a ∧ Productive b) :
    (∃ le : Moment κ → Moment κ → Prop, IsLinearOrder _ le ∧ ∀ m m', prec m m' → le m m')
  ∧ ∃ le₁ le₂, IsLinearOrder _ le₁ ∧ IsLinearOrder _ le₂ ∧
      (∀ m m', prec m m' → le₁ m m') ∧ (∀ m m', prec m m' → le₂ m m') ∧ le₁ ≠ le₂

/-- The pre-registered Newtonian branch: a shared reference surveyed identically by
    all relata is an absolute frame, forcing ≺ total. Checked at g = Ω, expected to
    FAIL to force totality (Ω faces all threads but does not make them agree pairwise). -/
theorem ws5_omega_absolute_frame {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ g : Proc κ, GlobalSurvey g → Total κ)                    -- IF such g exists, Newton
  ∧ ¬ GlobalSurvey (omegaProc κ hinf)                          -- but Ω is NOT one (expected)
```
*Strategy:* first part — every partial order has a total extension (order-extension principle / Szpilrajn; on `Moment` a directed-diagonal linearization), and incomparable spacelike moments (D4) can be ordered either way, giving `le₁ ≠ le₂`; so a global time *exists* but is a *choice*, non-canonical — the causal order is the invariant, global time a frame. Second part — the `GlobalSurvey g → Total κ` implication is `ws5_total_of_global` (C2); the branch is *whether a witness exists*. Checked at `g = Ω`: Ω is complete-in-extent yet closed at no depth (transcribed `ws6_omega_nonterminating`), so it *is* surveyed by every relatum but its self-survey never closes into a shared synchronizing datum — `¬ GlobalSurvey (omegaProc …)` — so Ω does **not** collapse the frame plurality into Newton. *Paper-decidable:* the extension existence is classical (order-extension); the Ω-refutation is a computation on the transcribed non-terminating Ω. *Strip:* the frame-plurality needs D4's earned incomparability; delete "face" and there are no spacelike pairs to reorder, so no two distinct extensions — the non-canonicity is downstream of the two-sidedness.

**D6 — the Lorentzian ceiling (heuristic, floor built).**
```lean
/-- FLOOR (built): the survey-depth quasi-distance is asymmetric exactly because the
    face is two-sided — asymmetry reflects faceAt mismatch, not a metric pun. -/
theorem ws5_cdist_asym_of_face {κ} {a b : Proc κ} (h : ¬ Agree a b) : cdist a b ≠ cdist b a
/-- CEILING (heuristic, likely-open): order-plus-number recovers a Lorentzian metric
    (BLMS / Martin–Panangaden). Stated, not built. -/
theorem ws5_lorentzian {κ} : LorentzianReconstruction (Moment κ) prec := by
  sorry  -- flagged heuristic; not in Mathlib; the honest ceiling per charter §5.4
```
*Strategy:* `ws5_cdist_asym_of_face` ties the quasi-metric asymmetry back to `faceAt` two-sidedness (the C3 floor, so the metric is not an untethered pun); `ws5_lorentzian` is the causal-set order-plus-number reconstruction, explicitly `sorry`/axiom-flagged as heuristic and likely-open, never counted as Discharged. *Paper-decidable:* the floor yes (unfolds `cdist` against `Agree`); the ceiling no — it is the flagged open. *Strip:* the floor's asymmetry *is* the face mismatch; strip "face" and there is no asymmetry to reconstruct from — the ceiling, if ever built, rests on the two-sidedness, not on a bare metric.

## Outcome classes (per charter §7)

- **Discharged (expected):** D1 (`ws5_precedes_order`, cited from WS4), D2 (`ws5_total_iff_agree`), D3 (`ws5_plurality_forbids_agreement`), D4 (`ws5_causal_partial_order` with earned incomparability), D5 first part (`ws5_global_time_is_frame`) — the relativity verdict: `≺` a genuine partial causal order, many local arrows, one causal order, no canonical global time, global time a non-canonical frame.
- **Impossibility proved (a success):** D4's `¬ Total κ` with no canonical linearization *is* the no-absolute-time impossibility — `≺` forced partial, no canonical global-time frame. This is the sharp negative the charter counts as success (README §7, charter §9).
- **The honest Newtonian alternative:** if `ws5_omega_absolute_frame`'s witness clause were to *fire* — a genuine `GlobalSurvey g` exists — `≺` comes back total and time is global/Newtonian, a real reportable result, not a failure. Expected instead: Ω refutes `GlobalSurvey`, so Newton does not return, and the branch closes honestly.
- **Partial (pre-registered):** the Lorentzian ceiling `ws5_lorentzian` open (only the floor `ws5_cdist_asym_of_face` built); flagged heuristic from the start per charter §5.4.
- **Failure to watch (the SERIOUS check):** if `¬ Total` is provable *without* the `faceAt` mismatch — the strip of "face" leaves incomparability intact as generic posethood — then the causal order **launders** (C4), and `ws5_causal_partial_order` is reported Partial with the laundering named. WS7's strip ledger aggregates this.

## Deliverable

`series-6/formal/ws5.lean`: transcribed `prec`, `Moment`, `faceAt`, WS4 order facts, `ws2_static_collapse`, `ws6_omega_nonterminating`, `omegaProc` (self-contained, no cross-series import); `Agree`, `Total`, `Incomparable`, `GlobalSurvey`, `cdist`; `ws5_precedes_order` (D1), `ws5_total_iff_agree` (D2), `ws5_plurality_forbids_agreement` (D3), `ws5_causal_partial_order` (D4), `ws5_global_time_is_frame` + `ws5_omega_absolute_frame` (D5), `ws5_cdist_asym_of_face` + `ws5_lorentzian` (D6, ceiling `sorry`-flagged). **Axiom note:** `#print axioms ws5_causal_partial_order` should reduce to the transcribed `ws2_static_collapse` axiom set (`propext, Classical.choice, Quot.sound`) plus the WS4 order facts and the WS1/WS6 plurality witness — and **must not** depend on `ws5_lorentzian`'s `sorry`. `ws5_global_time_is_frame` additionally uses the order-extension principle (Classical.choice); `ws5_lorentzian` is quarantined behind an explicit `axiom`/`sorry` and is never a dependency of any Discharged theorem.
