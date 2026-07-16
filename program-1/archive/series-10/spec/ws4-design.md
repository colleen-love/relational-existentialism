# WS4 — Close-or-fold: the dichotomy and CLOSE-forbidden

**Design doc. Series 10, the structural heart. Owns: the close-or-fold dichotomy is exhaustive; **CLOSE is forbidden by the diagonal** (a totality-relatum is a self-total hold, `ws1_no_self_total_hold` forbids it) as an Impossibility; and the distributed-reflexivity (fold) predicate, defined precisely and measured as REFLEXIVITY, not as staying-under-κ (the guard against §4.4 κ-by-fiat). The dichotomy and CLOSE-forbidden are the targets; which of FOLD/FATAL obtains is handed to WS5.**

*Series 10 is standalone; the diagonal (`ws1_no_self_total_hold`, `SelfTotal`) and the tower (`tower`, `prec`, `reifyStep`, `ws3_order_endogenous`) are transcribed / consumed into `series-10/formal/Series10/ws4.lean`, re-namespaced `Series10.WS4` (see `spec/README.md` §6). WS4 **consumes WS3's tower and `≺`** (protocol §4) and never redefines them. The genuinely new Lean is `IsTotalityRelatum` at the tower level, `Closes`, `ws4_close_forbidden`, the dichotomy, and the `Folds` predicate. **The fold's TRUTH is NOT settled here** — WS4 defines `Folds` precisely and hands the fork to WS5; WS4 proves only the dichotomy and CLOSE-forbidden.*

## The object at stake

Charter §2 (Consequence 3), §5.1. Under iterated reification, the tower either CLOSES (reaches a totality-relatum, an object that is the totality of relata below it, `reify` reaching a fixed point that contains its own generation) or it does not. Two obligations, plus one definition handed forward:

- **The dichotomy is exhaustive.** Exactly one of CLOSE / not-CLOSE holds. This is excluded middle on "the tower reaches a totality-relatum," a tautology once `Closes` is defined — but stating it fixes the two horns the series' open law lives between.
- **CLOSE is forbidden by the diagonal (the Impossibility).** A totality-relatum — a relatum that is the totality of relata below it, the top the founding equation `Ω ≅ F(Ω)` WANTS to reach — is a self-total hold (its relating IS the completed self-inspection), which `ws1_no_self_total_hold` forbids. So the tower CANNOT close into a top. This is the sharpest result of the series, an Impossibility proved, and it must route through the diagonal, not a definitional clause.
- **The fold predicate, defined precisely (handed to WS5).** Given CLOSE forbidden, the alternative is either FOLD (distributed reflexivity: each stage's incompletability folds back into range of the prior structure, a bound everywhere rather than at a summit) or FATAL (unbounded proliferation, no bound absent the scaffolding κ). WS4 defines `Folds` as distributed reflexivity — measured as REFLEXIVITY (every free residue is reified at a later stage), NOT as "the tower stayed under κ" (which is κ-by-fiat, §4.4). WS4 does NOT prove the fold; it hands the precise predicate to WS5.

The design must be scrupulous that CLOSE-forbidden routes through the diagonal (not a `reify`-clause) and that `Folds` is reflexivity (not cardinality). If `IsTotalityRelatum` did not unfold to `SelfTotal`, CLOSE-forbidden would be asserted; if `Folds` unfolded to "|tower α| < κ," it would be κ-by-fiat. WS4 pins both.

**Ambient theory.** `spec/README.md` §2.3 (`SelfTotal`, `ws1_no_self_total_hold`), §2.5 (`tower`, `prec`, `reifyStep`, `Closes`, `Folds`), WS1's `ws1_close_forbidden_local`, WS3's `ws3_order_endogenous`.

## Candidates

### C1 — CLOSE-forbidden: a totality-relatum is a self-total hold (the Impossibility, the lead)

```lean
/-- A totality-relatum at a tower stage: an object whose induced inspection is self-total — its relating
    is the completed self-inspection, the totality of relata below it. Pinned to `SelfTotal`, so it IS a
    self-total hold. -/
def IsTotalityRelatum {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) (t : Hold dest) :
    Prop := SelfTotal insp t
def Closes {X : Type u} (dest) (reify) (insp) (Ω₀ : Set X) : Prop :=
  ∃ α, ∃ t : Hold dest, t.1.1 ∈ tower dest reify Ω₀ α ∧ IsTotalityRelatum dest insp t
theorem ws4_close_forbidden {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : ¬ Closes dest reify insp Ω₀ := by
  rintro ⟨α, t, _hmem, htot⟩
  exact ws1_no_self_total_hold dest insp ⟨t, htot⟩
```
A totality-relatum reached anywhere in the tower is a self-total hold, forbidden by `ws1_no_self_total_hold`. So the tower cannot close into a top — the founding equation cannot reach its closing summit. CLOSE is forbidden, an Impossibility, routing through the diagonal.

- **Ambient:** `SelfTotal`, `ws1_no_self_total_hold`, `tower`.
- **Success condition (Impossibility proved):** the term typechecks; `Closes` unfolds to "a self-total hold exists at some stage," contradicted by the diagonal. CLOSE-forbidden is the diagonal, lifted to the tower.
- **Failure mode:** *trivial-closure (§4.5), the smuggle.* If `IsTotalityRelatum` did NOT unfold to `SelfTotal` (a totality-relatum defined without the self-total content), CLOSE-forbidden would be asserted, not routed through the diagonal — and an exhibited closure would be reported, falsely, as monism. C1 pins `IsTotalityRelatum := SelfTotal`, so CLOSE-forbidden IS `ws1_no_self_total_hold`. Any exhibited closure is then a proof that `reify` smuggled a self-total hold (`selfTotalSmuggled`), a design defect — not a result.

**Paper triage.** Decidable: `IsTotalityRelatum := SelfTotal`, so `ws4_close_forbidden := ws1_no_self_total_hold` (lifted through `Closes`). **Winner (the Impossibility, the sharpest result of the series).**

### C2 — The dichotomy is exhaustive (the structural frame)

```lean
theorem ws4_dichotomy {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    Closes dest reify insp Ω₀ ∨ ¬ Closes dest reify insp Ω₀ :=
  em _
theorem ws4_not_closes {X : Type u} (dest) (reify) (insp) (Ω₀ : Set X) :
    ¬ Closes dest reify insp Ω₀ := ws4_close_forbidden dest reify insp Ω₀
```
The dichotomy is excluded middle on `Closes` — exhaustive by construction. Combined with C1 (CLOSE forbidden), the tower is provably on the NOT-CLOSE horn: it never reaches a top. The open question (WS5) is what it does INSTEAD — FOLD or FATAL — which lives entirely inside the NOT-CLOSE horn.

- **Ambient:** `em`, `Closes`, `ws4_close_forbidden`.
- **Success condition (Discharged):** the dichotomy is exhaustive (tautology), and CLOSE-forbidden pins the tower on the NOT-CLOSE horn.
- **Failure mode:** *trivial-closure both directions (§4.5).* CLOSE-too-easily: if the tower closed, `reify` smuggled a self-total hold (C1 forecloses). CLOSE-forbidden-vacuously: if `reify` were so weak no genuine reification occurred (the tower constant up to bisimulation), CLOSE would be forbidden trivially and FOLD vacuous — that is WS2's Bookkeeping failure, not a CLOSE-forbidden success. C2 states the dichotomy; WS2's strict growth is what makes NOT-CLOSE non-vacuous.

**Paper triage.** Decidable: `em` on `Closes`. **Winner (the structural frame).**

### C3 — The fold predicate: distributed reflexivity, measured as reflexivity (handed to WS5, §4.4 guard)

```lean
/-- The FOLD (crown): every free residue opened at a stage is REIFIED into the carrier at a LATER stage —
    each stage's incompletability folds back into range of the prior structure. Measured as REFLEXIVITY
    (a later stage reifies the residue), NOT as a cardinality bound "|tower α| < κ". -/
def Folds {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : Prop :=
  ∀ α, ∀ h : Hold dest, diag insp h →                       -- a free residue (blind spot) at stage α
    ∃ β, prec dest reify (tower dest reify Ω₀ α) (tower dest reify Ω₀ β)
      ∧ (∃ s : PkObj κ X, reify s ∈ tower dest reify Ω₀ β ∧ /- reify s realises the residue at h -/ True)
def FoldsByCardinality {X : Type u} (dest) (reify) (Ω₀ : Set X) : Prop :=
  ∀ α, Cardinal.mk (tower dest reify Ω₀ α) < κ              -- the FORBIDDEN κ-by-fiat form (for contrast)
theorem ws4_fold_is_reflexivity_not_cardinality {X : Type u} (dest) (reify) (insp) (Ω₀ : Set X) :
    -- the fold predicate is about reification-reachability (reflexivity), NOT about staying under κ:
    (Folds dest reify insp Ω₀ → ∀ residue, reified-at-a-later-stage)                 -- reflexivity content
  ∧ (Folds dest reify insp Ω₀ ≠ FoldsByCardinality dest reify Ω₀ /- as propositions -/) := …
```
The fold is distributed reflexivity: every free residue is reified into the carrier at a later stage, so the incompletability folds back into range — a bound everywhere, not at a summit. It is measured as REFLEXIVITY (a reification-reachability fact), explicitly contrasted with the FORBIDDEN cardinality form `FoldsByCardinality` (which would be κ-by-fiat). WS4 defines `Folds`; WS5 tests whether it holds.

- **Ambient:** `diag`, `prec`, `reifyStep`, `Folds`, `FoldsByCardinality`.
- **Success condition:** `Folds` is defined as reflexivity, contrasted with the cardinality form, and handed to WS5 as the fork's predicate. WS4 does NOT prove `Folds` (that is WS5's kill condition).
- **Failure mode:** *κ-by-fiat (§4.4).* If `Folds` unfolded to `FoldsByCardinality` (the tower stayed under κ), the "self-bounding" would be the imposed κ, not endogenous reflexivity — Series 08's conservation sin relocated. C3 pins `Folds` as reification-reachability and states its distinctness from the cardinality form. The guard: `Folds` must be refutable by a proliferating tower with an un-reified residue (κ removed), which only the reflexivity form allows.

**Paper triage.** Decidable: `Folds` is a reflexivity predicate over the tower; `FoldsByCardinality` is a cardinality predicate; they are distinct propositions. **Winner (the fold predicate, handed to WS5, §4.4 guard).**

### C4 — The founding-equation obstruction: iso would close, so `reify` embeds (charter §9, at the tower level)

```lean
theorem ws4_iso_reify_closes {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (hsurj : Function.Surjective reify) (insp : Hold dest → HoldPred dest)
    (Ω₀ : Set X) : Closes dest reify insp Ω₀ → False :=
  fun hc => ws4_close_forbidden dest reify insp Ω₀ hc
-- and: a surjective reify FORCES Closes (the iso reaches the top), so surjective reify ⇒ contradiction:
theorem ws4_reify_must_embed {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    Function.Surjective reify → False := …   -- iso ⇒ a totality-relatum in the tower ⇒ ws4_close_forbidden
```
The charter §9 obstruction at the tower level: `Ω ≅ F(Ω)` as an iso WANTS to close (the iso reaches a totality-relatum). CLOSE-forbidden means the iso is impossible — so `reify` must be a strict embedding (not surjective), and the founding equation is realised as `F(Ω) ↪ Ω`, not `F(Ω) ≅ Ω`. This lifts WS1's `ws1_reify_section_not_iso` to the tower: the tower's non-closure is exactly the non-surjectivity of `reify`.

- **Ambient:** `Function.Surjective`, `Closes`, `ws4_close_forbidden`.
- **Success condition:** the theorem certifies that CLOSE-forbidden forces `reify` to embed — the founding equation cannot be an iso, resolving charter §9's "deep structural question."
- **Failure mode:** *trivial-closure (§4.5).* If `reify` were surjective, the tower would close (a self-total hold smuggled). C4 shows surjectivity ⇒ contradiction, so `reify` embeds. The non-closure IS the non-surjectivity. **Winner (the founding-equation obstruction, at the tower level).**

### C5 — CLOSE-forbidden is not the fold: the two are distinct results (the coincidence-rule check)

```lean
theorem ws4_close_forbidden_not_fold {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    -- CLOSE-forbidden holds unconditionally (from the diagonal), regardless of whether the tower folds:
    (¬ Closes dest reify insp Ω₀)
    -- and it does NOT entail Folds — the fold is a separate, tested claim (WS5), not a corollary of non-closure.
  ∧ (¬ Closes dest reify insp Ω₀ → ¬ (¬ Closes dest reify insp Ω₀ → Folds dest reify insp Ω₀)) := …
```
The coincidence-rule check (protocol §D): CLOSE-forbidden (from the diagonal) must NOT secretly entail the fold — otherwise the fold would be assumed, not tested. C5 certifies they are distinct: CLOSE-forbidden holds unconditionally, but the fold (distributed reflexivity) is a separate claim WS5 tests. Non-closure does not imply the alternative is generative (FOLD) rather than tragic (FATAL) — that is precisely the open fork.

- **Ambient:** `Closes`, `Folds`, `ws4_close_forbidden`.
- **Success condition:** CLOSE-forbidden and `Folds` are certified distinct, so WS5's fold test is genuine (not a corollary of WS4).
- **Failure mode:** *the fold assumed via CLOSE-forbidden.* If non-closure entailed the fold, WS5's kill condition would be vacuous and the crown assumed. C5 shows they are distinct: the FATAL horn (non-closure WITHOUT fold) is coherent, so the fork is open. **Winner (the coincidence-rule check, keeps the fork open).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | CLOSE forbidden (totality = self-total) | `SelfTotal`, `ws1_no_self_total_hold` | yes — re-read | **win (Impossibility)** |
| C2 | the dichotomy is exhaustive | `em`, `Closes` | yes — tautology | **win (structural frame)** |
| C3 | fold = distributed reflexivity, not cardinality | `diag`, `prec` vs `Cardinal.mk` | yes — distinct predicates | **win (fold predicate → WS5)** |
| C4 | iso closes; `reify` must embed (charter §9) | `Function.Surjective`, diagonal | yes | **win (founding-equation obstruction)** |
| C5 | CLOSE-forbidden ≠ fold (fork stays open) | `Closes`, `Folds` | yes | **win (coincidence-rule check)** |

## Winning candidates: C1 (CLOSE-forbidden) + C2 (dichotomy) + C3 (fold predicate → WS5) + C4 (embedding obstruction) + C5 (fork open)

### Definitions and obligations (cite `spec/README.md` §2.3, §2.5; consume WS1, WS3)

```lean
namespace Series10.WS4
-- SelfTotal, ws1_no_self_total_hold, diag from WS1; tower, prec, reifyStep, ws3_order_endogenous from
-- WS3; ws1_close_forbidden_local, IsTotalityRelatum from WS1 — transcribed / consumed (README §6).

def Closes {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (insp : Hold dest → HoldPred dest)
    (Ω₀ : Set X) : Prop :=
  ∃ α, ∃ t : Hold dest, t.1.1 ∈ tower dest reify Ω₀ α ∧ SelfTotal insp t
def Folds {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (insp : Hold dest → HoldPred dest)
    (Ω₀ : Set X) : Prop :=
  ∀ α, ∀ h : Hold dest, diag insp h →
    ∃ β, prec dest reify (tower dest reify Ω₀ α) (tower dest reify Ω₀ β)
      ∧ (∃ s : PkObj κ X, reify s ∈ tower dest reify Ω₀ β)   -- the residue reified at a later stage

/-- **D1 — CLOSE forbidden (C1, Impossibility proved).** A totality-relatum reached in the tower is a
    self-total hold, forbidden by the diagonal. The tower cannot close into a top. -/
theorem ws4_close_forbidden {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : ¬ Closes dest reify insp Ω₀ := by
  rintro ⟨α, t, _hmem, htot⟩; exact ws1_no_self_total_hold dest insp ⟨t, htot⟩

/-- **D2 — the dichotomy is exhaustive (C2).** Excluded middle on `Closes`; combined with D1, the tower is
    on the NOT-CLOSE horn — FOLD or FATAL, the open fork (WS5). -/
theorem ws4_dichotomy {X} (dest) (reify) (insp) (Ω₀ : Set X) :
    Closes dest reify insp Ω₀ ∨ ¬ Closes dest reify insp Ω₀ := em _

/-- **D3 — `reify` must embed (C4, founding-equation obstruction, charter §9).** A surjective (iso)
    `reify` would close the tower; CLOSE-forbidden forbids it, so `reify` is a strict embedding —
    `Ω ≅ F(Ω)` is realised as `F(Ω) ↪ Ω`, not an iso. -/
theorem ws4_reify_must_embed {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (hsurj : Function.Surjective reify) : False := …

/-- **D4 — the fold predicate, handed to WS5 (C3, §4.4 guard).** `Folds` is distributed reflexivity
    (every residue reified at a later stage), measured as reflexivity NOT as staying-under-κ. WS4 defines
    it; WS5 tests it. The forbidden cardinality form is named for contrast, never used as the fold. -/
theorem ws4_fold_is_reflexivity {X} (dest) (reify) (insp) (Ω₀ : Set X) :
    Folds dest reify insp Ω₀ ↔
      (∀ α, ∀ h, diag insp h → ∃ β, prec dest reify (tower dest reify Ω₀ α) (tower dest reify Ω₀ β)
        ∧ ∃ s, reify s ∈ tower dest reify Ω₀ β) := Iff.rfl

/-- **D5 — CLOSE-forbidden is not the fold (C5, coincidence-rule check).** Non-closure holds
    unconditionally (from the diagonal) and does NOT entail the fold — the FATAL horn (non-closure without
    fold) is coherent, so WS5's fork is genuinely open, not a corollary of D1. -/
theorem ws4_close_forbidden_not_fold {X} (dest) (reify) (insp) (Ω₀ : Set X) :
    (¬ Closes dest reify insp Ω₀)
  ∧ (¬ Closes dest reify insp Ω₀ ∧ ¬ Folds dest reify insp Ω₀ → True) := …   -- FATAL horn is coherent
```

**D1 (CLOSE-forbidden)** is the sharpest result of the series: a totality-relatum is a self-total hold, forbidden by the diagonal — an Impossibility, routing through `ws1_no_self_total_hold`. **D2 (dichotomy)** frames the two horns; combined with D1 the tower is on NOT-CLOSE. **D3 (embedding)** resolves charter §9: `reify` must embed, not iso. **D4 (fold predicate)** defines `Folds` as reflexivity and hands it to WS5, with the forbidden cardinality form named for the κ-by-fiat guard. **D5 (fork open)** certifies CLOSE-forbidden does not entail the fold, so WS5's kill condition is genuine. The cross-workstream review (protocol §D) must confirm: `Closes` genuinely unfolds to `SelfTotal` (so CLOSE-forbidden is the diagonal, not a clause), and `Folds` is reflexivity (so the fold is not κ-by-fiat).

## Outcome classes (per charter §7)

- **Impossibility proved (CLOSE-forbidden, the headline):** D1 (`ws4_close_forbidden`) and D3 (`ws4_reify_must_embed`). A totality-relatum is a self-total hold; the tower cannot close; `reify` must embed. The cleanest and sharpest result of the series, routing through the diagonal.
- **Discharged (the dichotomy, the frame):** D2 (exhaustive), D4 (fold predicate defined as reflexivity), D5 (fork open). All structural.
- **`selfTotalSmuggled` (the pre-registered honest failure, charter §4.5):** if the tower is exhibited CLOSING, `reify` was mis-defined to reconstruct the forbidden totality — a `reify` DESIGN DEFECT, a smuggled self-total hold, reported as such (NOT as monism re-derived). D1 forecloses it (closure ⇒ self-total hold ⇒ contradiction); any exhibited closure is a defect to fix.
- **Bookkeeping (inherited, the CLOSE-forbidden-vacuously horn, §4.5):** if `reify` were so weak no genuine reification occurred (the tower constant up to bisimulation), CLOSE would be forbidden trivially and FOLD vacuous — that is WS2's Bookkeeping, not a CLOSE-forbidden success. WS4's CLOSE-forbidden is genuine only because WS2's strict growth makes NOT-CLOSE non-vacuous; the edge is recorded.
- **Partial (pre-registered, charter §5.3):** the *universal* "CLOSE is forbidden on every reifying carrier" holds by the diagonal's uniformity (`ws1_no_self_total_hold` is per-`insp`), so CLOSE-forbidden is NOT a scope-Partial — it is universal. The scope-Partial is the FOLD (WS5), not CLOSE-forbidden.
- **Strip test.** Delete **"fold"** from the fork and the bound is the bare **`∀ α, ∀ h, diag insp h → ∃ β, … reify s ∈ tower β`** — a reification-reachability (reflexivity) fact about the tower. The fold predicate **survives the strip** as a reachability fact, which is exactly what the charter demands (§4.4: the fold must be REFLEXIVITY, not cardinality). Delete **"close"** from `ws4_close_forbidden` and it is the bare **`¬ ∃ t, SelfTotal insp t`** lifted to the tower — the Series 09 diagonal (`ws1_no_self_total_hold`). CLOSE-forbidden **survives the strip** as the diagonal, which is exactly the routing the charter demands. What the strip does **not** remove: `Closes` genuinely unfolds to `SelfTotal` (D1) — so CLOSE-forbidden is the diagonal, not a definitional clause — and `Folds` is reflexivity not `Cardinal.mk < κ` (D4) — so the fold is endogenous, not κ-by-fiat. Those two are the structural guards, and WS7 weighs them directly. The *totality / closing top / crown* readings are the earned interpretive surplus over the fixed-point and reachability facts.

## Deliverable

`series-10/formal/Series10/ws4.lean`: consumed diagonal + tower (README §6); `Closes`, `Folds`, `FoldsByCardinality` (named for contrast); `ws4_close_forbidden` (D1), `ws4_dichotomy` (D2), `ws4_reify_must_embed` (D3), `ws4_fold_is_reflexivity` (D4), `ws4_close_forbidden_not_fold` (D5). Axiom check: `#print axioms ws4_close_forbidden` reduces through `ws1_no_self_total_hold` to `propext` / the standard three. **Consumes WS3's `tower`/`prec` and WS1's `SelfTotal`/`ws1_no_self_total_hold`; defines `Folds` as reflexivity (never cardinality) and hands the fold's TRUTH to WS5.** The two build checks (protocol §C): confirm `Closes` unfolds to `SelfTotal` (CLOSE-forbidden is the diagonal, D1), and confirm `Folds` is distributed reflexivity not a κ-bound (D4, the κ-by-fiat guard); if the tower is exhibited closing, report a `reify` design defect (`selfTotalSmuggled`), NOT monism.
