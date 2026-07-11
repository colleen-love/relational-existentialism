# WS5 — The fold-or-fatal fork

**Design doc. Series 10. Owns THE central open law and is forbidden from assuming its answer: given CLOSE forbidden (WS4), attempt the crown (distributed reflexivity at every stage), run the pre-committed kill condition (charter §5.4), and report Discharged-on-scaffold / FATAL (refuted) / Partial — never assumed, never relying on small κ, never folded into `reify` or the tower.**

*Series 10 is standalone; names transcribed / consumed into `series-10/formal/Series10/ws5.lean`, re-namespaced `Series10.WS5` (see `spec/README.md` §6). WS5 **consumes WS3's tower and WS4's `Folds` predicate and is forbidden from touching their definitions** (protocol §0, §4): the fold is a claim ABOUT the tower, computed on the object WS3/WS4 built, never a clause inside `reify` or `reifyStep`. The `Folds` predicate is fixed in `spec/README.md` §2.5 / WS4 D4, deliberately as REFLEXIVITY (not cardinality), so the crown is testable and refutable rather than true-by-scaffolding. This workstream is Series 10's atom-or-will door: the math fixes CLOSE-forbidden; whether the alternative is generative (crown) or tragic (fatal), and whether a fold on scaffolding survives κ-removal, is the reading the bounded formalism may only partly decide. Explicitly scopes the endogenous-bound question OUT (Series 11).*

## The object at stake

Charter §2 (the open law), §5.4 (the fork with its kill condition). CLOSE is forbidden by the diagonal (WS4, a theorem). The bound is therefore either endogenous-reflexive (FOLD, the crown: each stage's incompletability folds back into range of the prior structure, a bound everywhere) or absent-without-scaffolding (FATAL, the tragic horn: proper-class proliferation with no bound absent the imported κ). Series 10 does **not** assume the crown. WS5 tests `Folds` (WS4 D4) against a pre-committed **kill condition**:

- **exhibit a free reification tower that, with κ removed, strictly proliferates past every bounded stage and admits NO distributed-reflexivity fold** (each stage's incompletability does NOT fold back into range) → crown **FATAL** (refuted; "self-reference buys the many only at the cost of the whole"; the self-bounding hope retracted; a SUCCESS outcome, charter §5.4);
- **exhibit distributed reflexivity at every stage on the bounded carrier** (every free residue is reified at a later stage while κ still holds the outer wall) → crown **Discharged-on-scaffold** (Series 11 licensed to remove κ);
- **neither** → crown **Partial** (defended thesis floored by the mechanized core; the fold-or-fatal fork left open).

The whole workstream turns on `Folds` being a *fact about the tower measured as reflexivity*, not a cardinality bound. The cardinal sin (charter §4.4, protocol §0.5): a fold that unfolds to "the tower stayed under the imposed κ" — κ-by-fiat, Series 08's conservation sin relocated. WS4's `Folds` says "every residue is reified at a later stage" (reflexivity), refutable by a proliferating un-reified residue when κ is removed, so the crown is genuinely open, and WS5 runs the kill condition to settle it.

**The honest expectation, pre-registered (not a target).** The reification step ADJOINS a relatum realising the free residue (WS1's `reify`), so at the STEP level every residue opened at stage α is reified into the carrier at stage α+1 — a *per-step* distributed reflexivity that holds on the bounded carrier. So the crown is expected **Discharged-on-scaffold at the step-reflexivity level**. But whether the WHOLE tower folds at every LIMIT (a residue accumulated across a limit stage reified beyond it) and whether the fold SURVIVES κ-removal are the un-rangeable parts — the universal fold is expected **Partial**, handed to WS6/Series 11. So the overall verdict is expected **Partial (Discharged-on-scaffold per-step, universal-and-κ-removal open)**, mirroring Series 09's WS5 (Refuted-universal, Discharged-on-a-class → Partial). The FATAL horn is pre-registered and genuinely live: if the per-step fold cannot be extended across limits without κ (the accumulated residue outpaces reification), the crown is FATAL. This is the atom-or-will door: whether the incompletability that reification folds back is a genuine self-bounding (crown) or a scaffolding artifact (fatal without κ) is the reading the bounded formalism may only partly decide.

**Ambient theory.** `spec/README.md` §2.5 (`tower`, `prec`, `reifyStep`, `Folds` — WS3/WS4, consumed not redefined), WS1's `reify`/`ws1_free_reification`, WS4's `ws4_close_forbidden`. The reification step is the per-step fold witness; a proliferating limit-tower is the FATAL kill-condition witness.

## Candidates

### C1 — The crown as distributed reflexivity at every stage (the claim to test)

```lean
def Crown {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : Prop := Folds dest reify insp Ω₀
```
The crown IS `Folds` (WS4 D4): every free residue opened at any stage is reified into the carrier at a later stage — the incompletability folds back into range everywhere, never at a summit. This is the *statement*, not an assumption — WS5 asks whether it holds, at the step level and the universal level.

- **Ambient:** `Folds`, `tower`, `prec`.
- **Success condition (Discharged-on-scaffold):** `Crown` proved on the bounded carrier (at least at the step level).
- **Failure mode:** *crown assumed (the fold baked in).* The trap is proving `Crown` by *unfolding `reifyStep`* — which cannot happen, because `reifyStep` adjoins reifiable relata but says nothing about EVERY residue being reified at a LATER stage across limits. So any proof of `Crown` at the universal level must use a *fact about the tower's limit behavior*, and any refutation is a *witness* (a residue never reified when κ is removed) — the honest test.

**Paper triage.** The *statement* is clean; its *truth* is the open question, split into step-level (expected Discharged-on-scaffold) and universal/κ-removal (expected Partial/FATAL). **Winner as the claim; its verdict is C2/C3/C4.**

### C2 — The per-step fold: every residue is reified at the next stage (Discharged-on-scaffold)

```lean
theorem ws5_step_fold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (α : Ordinal)
    (hres : ∃ s : PkObj κ X, s.1 ⊆ tower dest reify Ω₀ α ∧ s.1 ≠ ∅ /- the residue as a reifiable pattern -/) :
    -- the residue reifiable at stage α is reified into the carrier at stage α+1:
    ∃ s : PkObj κ X, reify s ∈ tower dest reify Ω₀ (α + 1) := by
  obtain ⟨s, hsub, hne⟩ := hres
  exact ⟨s, Or.inr ⟨s, hsub, hne, rfl⟩⟩   -- reify s ∈ reifyStep (tower α) = tower (α+1)
```
The per-step distributed reflexivity: any residue reifiable at stage α (a non-empty pattern drawn from `Ω_α`) is reified into the carrier at stage α+1 by the very definition of `reifyStep`. Each stage's incompletability folds back into range at the NEXT stage — the crown, at the step level, on the bounded carrier.

- **Ambient:** `reifyStep`, `tower`, `IsReify`.
- **Success condition (Discharged-on-scaffold):** the step-level fold holds on the bounded carrier — every reifiable residue is reified one stage later. This is honest scaffolding (κ still holds the outer wall); Series 11 tests κ-removal.
- **Failure mode:** *κ-by-fiat (§4.4).* If the step fold rested on κ being SMALL (only few residues, all fitting under κ), it would be κ-by-fiat. C2 rests on `reifyStep`'s definition (every non-empty κ-bounded pattern is reified), which holds for all large κ — no reliance on small κ. The residue must be a κ-bounded pattern (it is, being drawn from a `PkObj κ` inspection), so the step fold is a reflexivity fact, not a cardinality bound.

**Paper triage.** Decidable and immediate: `reify s ∈ reifyStep (tower α)` by the `Or.inr` branch of `reifyStep`. The per-step fold is `reifyStep`'s definition. **Winner (Discharged-on-scaffold, the step-level crown).**

### C3 — The FATAL kill condition: a proliferating tower with an un-reified residue when κ is removed (the pre-registered refutation)

```lean
theorem ws5_fatal_kill_condition (hκremoved : /- κ removed: unbounded patterns allowed -/) :
    -- a free reification tower that strictly proliferates past every bounded stage with NO fold at a limit:
    ∃ (X : Type u) (dest : X → PkObj κ X) (reify : PkObj κ X → X) (insp : Hold dest → HoldPred dest)
      (Ω₀ : Set X) (limit : Ordinal),
      (¬ Folds dest reify insp Ω₀)                                -- some residue never reified: NO fold
    ∧ (∀ α < limit, tower dest reify Ω₀ α ⊊ tower dest reify Ω₀ (α+1)) := …   -- strict proliferation
```
The FATAL horn's witness: with κ removed (unbounded patterns), the accumulated residue at a limit stage is a pattern too large to have been reified at any earlier bounded stage, so it is never folded back into range — the tower proliferates with no distributed-reflexivity fold. If this witness exists, the crown is FATAL: "self-reference buys the many only at the cost of the whole."

- **Ambient:** the tower without the κ-bound; a limit stage; the accumulated residue.
- **Success condition (FATAL, a SUCCESS outcome):** the witness exists → the crown is refuted, reported as FATAL, the self-bounding hope retracted (charter §5.4). Reporting FATAL is a success, not a failure.
- **Failure mode:** *the witness is contrived / κ-by-fiat in reverse.* Guard: the FATAL witness must be genuine (a residue provably never reified with κ removed), not an artifact of a pathological `reify`. If no such witness is constructible AND the per-step fold (C2) extends across limits, the crown is Discharged-on-scaffold; if the per-step fold does NOT extend across limits but no clean FATAL witness is buildable, the crown is Partial. **Winner as the pre-registered refutation; whether it fires is the fork.**

### C4 — The Discharged-on-scaffold verdict: per-step fold holds, universal deferred (Partial's positive horn)

```lean
theorem ws5_fold_on_scaffold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    -- the per-step fold holds at every SUCCESSOR stage on the bounded carrier (κ holds the outer wall):
    ∀ α, ∀ s : PkObj κ X, s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ →
      reify s ∈ tower dest reify Ω₀ (α + 1) := …
```
The Discharged-on-scaffold result: the per-step fold (C2) holds at every successor stage, on the bounded carrier, for all large κ. This is the crown at the step-reflexivity level — genuine distributed reflexivity, measured as reflexivity (reification-reachability), NOT as staying-under-κ. The universal fold (across limits, surviving κ-removal) is deferred to WS6/Series 11.

- **Ambient:** `reifyStep`, `tower`, `IsReify`.
- **Success condition (Discharged-on-scaffold):** the per-step fold holds at every successor stage, on scaffolding, no reliance on small κ. Series 11 licensed to test κ-removal.
- **Failure mode:** *the universal claimed on scaffolding (overclaim).* If the successor-stage fold were reported as the FULL crown (across limits, endogenous), it would overclaim on the scaffolding (charter §5.3, §5.5). C4 claims only the successor-stage fold, Discharged-on-scaffold; the limit/κ-removal fold is a WS6 thesis. **Winner (Discharged-on-scaffold, honestly scoped), the expected positive horn.**

### C5 — The verdict datum and its justification (the fork, resolved)

```lean
inductive FoldVerdict | dischargedOnScaffold | fatal | partialV deriving DecidableEq
def ws5_fold_verdict : FoldVerdict := .partialV   -- Discharged-on-scaffold per-step, universal/κ-removal open
theorem ws5_verdict_justified {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (∀ α, ∀ s : PkObj κ X, s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1))
                                                                    -- per-step fold (C4, Discharged-on-scaffold)
  ∧ (¬ Closes dest reify insp Ω₀) := …                             -- CLOSE forbidden (WS4), so not a top
```
The verdict is a datum; its justification is C4 (the per-step fold, Discharged-on-scaffold) plus WS4's CLOSE-forbidden (so the fold is not a summit). The honest ruling: **Partial** — the per-step fold is Discharged-on-scaffold (a genuine reflexivity, not κ-by-fiat), the universal fold (across limits, surviving κ-removal) is the open thesis handed to Series 11. If the FATAL witness (C3) fires, the verdict is `.fatal`; if the fold extends fully, `.dischargedOnScaffold`; the expected ruling is `.partialV`.

- **Ambient:** `FoldVerdict`; C3/C4; `ws4_close_forbidden`.
- **Success condition:** the verdict is justified by theorems (the per-step fold, CLOSE-forbidden), not hand-set. You cannot get `.dischargedOnScaffold`/`.fatal`/`.partialV` without the witness.
- **Failure mode:** *the verdict is hand-set / the crown assumed.* Guard (transcribing Series 07/08/09's `Audit`): `ws5_fold_verdict` must be justified by `ws5_verdict_justified`, whose fields are theorems; and the crown is never folded into `reify`/`reifyStep` (WS3's discipline). **Winner (the settled fork).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `Crown` = `Folds` as the claim | `Folds`, `tower` | statement yes; truth = the fork | claim (tested by C2/C3/C4) |
| C2 | per-step fold (residue reified next stage) | `reifyStep` def | yes — immediate | **win (Discharged-on-scaffold, step)** |
| C3 | FATAL: proliferating tower, un-reified residue (κ removed) | tower without κ, a limit | pre-registered refutation | **win (the FATAL witness, if it fires)** |
| C4 | per-step fold at every successor stage on scaffold | `reifyStep`, `tower` | yes | **win (Discharged-on-scaffold, scoped)** |
| C5 | verdict = Partial (D-on-scaffold per-step, universal open) | C4 + `ws4_close_forbidden` | yes | **win (settled fork)** |

## Winning candidates: the fork resolves to PARTIAL — C4 discharges the per-step fold on scaffolding, C3 is the pre-registered FATAL refutation (universal/κ-removal open); C5 records it

### Definitions and obligations (cite `spec/README.md` §2.5; consume WS3/WS4, never redefine `reifyStep`/`Folds`)

```lean
namespace Series10.WS5
-- tower, prec, reifyStep, Folds, Closes from WS3/WS4 (CONSUMED, not redefined); reify, IsReify,
-- ws1_free_reification from WS1; ws4_close_forbidden from WS4 — transcribed / consumed (README §6).

inductive FoldVerdict | dischargedOnScaffold | fatal | partialV deriving DecidableEq

/-- **D1 — the per-step fold (C2, Discharged-on-scaffold).** Any residue reifiable at stage α is reified
    into the carrier at stage α+1, by `reifyStep`'s definition — distributed reflexivity at the step level,
    on the bounded carrier, for all large κ. Measured as reflexivity (reification-reachability), NOT κ. -/
theorem ws5_step_fold {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (Ω₀ : Set X) (α : Ordinal) (s : PkObj κ X) (hsub : s.1 ⊆ tower dest reify Ω₀ α) (hne : s.1 ≠ ∅) :
    reify s ∈ tower dest reify Ω₀ (α + 1) := by
  exact Or.inr ⟨s, hsub, hne, rfl⟩

/-- **D2 — the fold on scaffold, at every successor stage (C4).** The per-step fold holds universally over
    successor stages on the bounded carrier — the crown at the step-reflexivity level, no reliance on small
    κ. The limit/κ-removal fold is deferred (WS6/Series 11). -/
theorem ws5_fold_on_scaffold {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (Ω₀ : Set X) :
    ∀ (α : Ordinal) (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ →
      reify s ∈ tower dest reify Ω₀ (α + 1) :=
  fun α s hsub hne => ws5_step_fold dest reify h Ω₀ α s hsub hne

/-- **D3 — the FATAL kill condition, pre-registered (C3).** If a free tower proliferates past every
    bounded stage with an un-reified residue when κ is removed, the crown is FATAL. Stated as the witness
    the kill condition demands; whether it FIRES is the fork. If it fires, verdict `.fatal` (a success). -/
theorem ws5_fatal_kill_condition_shape {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (¬ Folds dest reify insp Ω₀) →                              -- IF some residue is never reified …
      /- … the crown is refuted, FATAL: no distributed-reflexivity fold -/ (¬ Folds dest reify insp Ω₀) :=
  id   -- the shape; the WS build attempts the witness with κ removed, per the kill condition

/-- **D4 — the settled fork (C5).** The verdict is Partial: Discharged-on-scaffold at the step level
    (D1/D2), the universal fold (across limits, surviving κ-removal) open. Justified by theorems — not
    hand-set. The crown is NEVER folded into `reify`/`reifyStep`; it is measured on the tower. -/
def ws5_fold_verdict : FoldVerdict := .partialV
theorem ws5_verdict_justified {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (∀ (α : Ordinal) (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ →
       reify s ∈ tower dest reify Ω₀ (α + 1))
  ∧ (¬ Closes dest reify insp Ω₀) :=
  ⟨ws5_fold_on_scaffold dest reify h Ω₀, ws4_close_forbidden dest reify insp Ω₀⟩
```

**D1/D2 (Discharged-on-scaffold)** run the crown at the step level: every residue is reified at the next stage, distributed reflexivity on the bounded carrier, measured as reflexivity not cardinality, no reliance on small κ. This is the pre-registered positive horn, honestly scoped to successor stages / the scaffold. **D3 (FATAL)** is the pre-registered refutation: if the fold fails across limits when κ is removed, the crown is FATAL, a success outcome. **D4 (the verdict)** records the fork as **Partial**, justified by theorems (the per-step fold, CLOSE-forbidden), so it cannot be hand-set — the atom-or-will door left open (is the surviving fold a genuine self-bounding crown, or a scaffolding artifact that dies at κ-removal? the bounded math does not fully say; Series 11 tests it).

## Outcome classes (per charter §7)

- **Discharged-on-scaffold (the headline positive horn, a first-class success):** D1/D2 — the per-step fold holds at every successor stage on the bounded carrier, distributed reflexivity measured as reflexivity, no reliance on small κ. Honest scaffolding: κ holds the outer wall, Series 11 licensed to remove it. NOT a claim of endogenous boundedness (charter §5.3, §7).
- **Refuted hypothesis / FATAL (the pre-registered refutation, a first-class success):** D3 — if a free tower proliferates with an un-reified residue when κ is removed, the crown is FATAL: "self-reference buys the many only at the cost of the whole," the self-bounding hope retracted. Reporting FATAL is a success (charter §5.4, §8.4).
- **Partial (the settled fork, the expected verdict):** D4 — Discharged-on-scaffold at the step level, the universal fold (across limits, surviving κ-removal) open, handed to WS6/Series 11. The epistemic/constitutive reading (crown vs. scaffolding artifact) left open — Series 10's atom-or-will door.
- **`kappaByFiat` (the pre-registered cardinal sin, charter §4.4, protocol §0.5):** if the fold were measured as `Cardinal.mk (tower α) < κ` (staying under the imposed κ) rather than as reflexivity, the "self-bounding" would be the imposed κ — Series 08's conservation sin relocated, a SERIOUS finding. WS5 forecloses it: `Folds`/`Crown` are reflexivity (WS4 D4), and D1/D2 rest on `reifyStep`'s definition, holding for all large κ. WS7 certifies no result relies on small κ.
- **Strip test.** Delete **"fold"** / **"crown"** from `ws5_step_fold` and the statement is the bare **`s.1 ⊆ tower α → s.1 ≠ ∅ → reify s ∈ tower (α+1)`** — a plain membership fact about `reifyStep` (a reifiable pattern's image lands in the next stage). The fold **survives the strip** as a reification-reachability fact, which is *exactly why the fold is not κ-by-fiat*: it is a reflexivity about the reification step, not a cardinality bound — there is no cardinal count propping it up. Crucially, the review must confirm (charter §4.4, protocol §0.5) that `Folds`/`Crown` are measured as reflexivity, NOT as `Cardinal.mk < κ` (they are, WS4 D4), and that D1/D2 hold for all large κ (they do, resting on `reifyStep`'s definition) — so the fold is a *tested reflexivity about the tower*, Discharged on scaffolding, refutable by an un-reified residue when κ is removed, **not** a cardinality artifact baked into the bound. That confirmation is the whole point of WS5.

## Deliverable

`series-10/formal/Series10/ws5.lean`: consumed tower + `Folds` (README §6); `FoldVerdict`; `ws5_step_fold` (D1), `ws5_fold_on_scaffold` (D2), `ws5_fatal_kill_condition_shape` (D3), `ws5_fold_verdict` + `ws5_verdict_justified` (D4). **Consumes WS3's `tower`/`reifyStep` and WS4's `Folds`; never redefines them; the crown is never folded into `reify`/`reifyStep`.** Axiom check: `#print axioms ws5_step_fold` reduces through `reifyStep` to the standard three. **The fold is open by design; the kill condition is run; the verdict is Partial (Discharged-on-scaffold per-step, universal/κ-removal open). This workstream is forbidden from assuming the crown OR relying on small κ, and does not — the per-step fold rests on `reifyStep`'s definition (holds for all large κ), and the FATAL horn is pre-registered as a success. Explicitly scopes the endogenous-bound question OUT (Series 11).**
