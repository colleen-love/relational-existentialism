# WS3 — The engine: incompleteness as fuel

**Design doc. Series 6, the signature crux. Owns: the diagonal time-step `Δ` (the successor of a state IS the residue its own self-survey missed), the engine identity `fixed-point-free = incompleteness = non-termination`, the recovery of Ω as the canonical non-terminating orbit, and the one obligation the whole series turns on — that the diagonal *genuinely drives* the process (strip "diagonal" and `Δ` loses its definition), on pain of reporting Trivialized.**

*Series 6 is standalone; all Series 4 names used here are transcribed into `series-6/formal/ws3.lean` and re-namespaced `Series6.WS3` (see `spec/README.md` §5). Shared objects (`Approx`, `trunc`, `Proc`, `Productive`, `Δ`, `Moment`, `prec`, `Ω_n`) are defined in `spec/README.md` §2–§4 and only cited here.*

## The object at stake

The charter (§5.2) stakes the program on one identity: fixed-point-freeness is a single fact with three readings — incompleteness (spatially, no object surveys itself, the Series 4 Cantor/Lawvere diagonal), non-termination (temporally, no state is at rest), and productivity (constructively, the residue is always available as the next stage). WS3 must (a) build the time-step `Δ : Proc κ → Proc κ` so that the successor of a state *is* the residue of its failed self-survey — literally, not by a naming convention; (b) prove the triple identity as one theorem, not three loosely-associated facts; (c) recover Ω as `Δ`'s canonical non-terminating orbit, the state that recurs while its moment strictly advances; and (d) pass the strip test — delete "diagonal"/"residue" from the statement and `Δ`'s definition must collapse, or the engine is painted on and WS3 reports **Trivialized** (charter §5.2, §7). Obligation (d) is not a check appended to the work; it is the work. A `Δ` that survives the strip is decoration.

**Ambient theory.** `spec/README.md` §2–§4: the plain carrier `νPk κ`; the final ω-chain `A κ n` with truncations `trunc` (the founded past-map); `Proc κ` un-quotiented, stagewise identity; `Productive x` (every bud opens eventually) as *genuine global atomlessness*; **moments** `Moment κ` (a state at a survey-depth, a pair `(x, n)`), on which fixed-point-freeness lives — forced by Ω, which recurs as a *state* while its *moment* advances. The self-survey at stage `n` is a map from stage-`n` states to their stage-`n` predicates; by the transcribed finite Cantor/Lawvere diagonal `ws6_lawvere_incomplete` it is not surjective — there is a residue `d_n` it misses. `Δ` opens, at each stage, the bud carrying `d_n`.

## Candidates

### C1 — `Δ` literally = residue-opening on `Proc` (the lead)

```lean
/-- The stage-n self-survey: states at depth n to their depth-n predicates. -/
def survey {κ} (x : Proc κ) (n : ℕ) : A κ n → (A κ n → Prop)
/-- Cantor residue: the predicate `survey x n` provably omits (ws6_lawvere_incomplete). -/
noncomputable def residue {κ} (x : Proc κ) (n : ℕ) : A κ (n+1)      -- the missed element, as a stage-(n+1) bud-opening
/-- The time-step: successor at stage n+1 IS the opened residue of the survey at n. -/
noncomputable def Δ {κ} (x : Proc κ) : Proc κ :=
  ⟨fun n => Nat.rec (x.1 0) (fun k _ => residue x k) n, by …⟩       -- (Δ x).1 (k+1) := residue x k
```
`Δ` has no independent definition: `(Δ x)` at stage `n+1` is *defined as* the residue-opening of `x`'s stage-`n` survey. There is no arithmetic of states underneath onto which "residue" is later mapped.

- **Ambient `F` / the fixed-point-free map:** `F = P_κ` on the final chain; the fixed-point-free map is the survey itself — `survey x n` is a map into its own predicate space with a Cantor diagonal, so it is non-surjecting *by construction*.
- **Success condition:** `Δ` is total and productive; no *moment* is a `Δ`-fixed point (`(x,n) = Δ·(x,n)` is impossible, from Cantor); the three readings are one theorem; strip test passes because `residue` is the only definiens.
- **Failure mode (named):** none of the three trivialization traps applies *by construction* — but the price is that `residue` must be shown well-defined as a genuine stage-`(n+1)` element (the Cantor witness must land as an *actual opened bud*, not an abstract "missed predicate"). If the missed predicate cannot be realized as a concrete `A κ (n+1)` element, C1 stalls (routed to C4's typed fallback).

**Paper triage.** Decidable-on-paper and the intended shape: the strip test is a *syntactic* fact here (delete `residue` and `Δ`'s recursion has no successor clause — it fails to typecheck, not merely fails to be interesting), which is exactly what charter §5.2 demands. The one live obligation is realizing the Cantor residue as a concrete bud-opening; `ws6_lawvere_incomplete` gives the *element* missed, and `Approx`'s `(n+1)`-layer is where a fresh bud opens, so the realization is a computation on the transcribed diagonal (D2 below). **Winner, conditional on that realization.**

### C2 — `Δ` by independent corecursion, diagonal related by a theorem (the PAINTED-ON trap, rejected)

```lean
noncomputable def step {κ} : Proc κ → Proc κ := Proc.corec someTransition   -- defined ELSEWHERE
theorem step_is_diagonal {κ} (x) : step x = Δ_residue x                     -- "and it happens to be the residue"
```
Define the dynamics by any convenient corecursion `step`, then *prove* it coincides with residue-opening.

- **Ambient `F` / fpf map:** whatever `someTransition` chooses; the diagonal enters only in the *theorem* `step_is_diagonal`, not the *definition*.
- **Success condition:** would be that `step_is_diagonal` holds.
- **Failure mode (named): painted-on.** Even if `step_is_diagonal` is provable, `step` is defined without the diagonal, so stripping "diagonal"/"residue" from the codebase leaves `step` intact and fully dynamical — the engine is vocabulary applied to an independently-specified evolution. This is precisely the Series 3 attention trap and the Series 5 grade-shift Trivialization (charter §5.2, §7). A *provable coincidence theorem is not enough*; the coincidence rule (charter §7) requires the definitional and forced forms be distinct-and-equal, but here the "forced" form is not forced — it is the decorated one.

**Paper triage.** **Reject, and name it as the trap.** The tell is decidable-on-paper: if `Δ` has any definiens that typechecks after `residue`/`survey` are deleted, we are in C2. WS3's discipline is to forbid exactly this — `Δ` must have *no* fallback definition. Retained only as the negative pole the strip test is built to detect (it is the shape WS7 audits against).

### C3 — Metric contraction (WS1's C4 fallback: fixed-point-free = non-contractive-completion)

```lean
def bstep {κ} : (νPk κ).X → (νPk κ).X → ℝ≥0∞      -- behavioural distance (WS1 C4)
-- Δ as a contraction on an INCOMPLETE space; fixed-point-freeness = Banach fails (no completeness)
noncomputable def Δmetric {κ} : CauchySeqIncomplete κ → CauchySeqIncomplete κ
```
The engine identity read metrically: incompleteness of the space = no fixed point of the contraction (Banach needs completeness), non-termination = non-convergence.

- **Ambient `F` / fpf map:** the behavioural pseudometric contraction; fixed-point-freeness is literal (Banach's hypothesis fails on the refused completion).
- **Success condition:** the contraction is manifestly fixed-point-free; the triple identity reads off metric incompleteness.
- **Failure mode (named): the pun does the work.** "Non-termination" as metric non-convergence may have no faithful tie back to the *relating* — the residue-as-successor becomes a statement about distances, not about the survey missing an element, and the strip test now targets "metric"/"Cauchy" rather than "diagonal", which is a *different* load-bearing word. Risk that `Δmetric` is fixed-point-free for analytic reasons unrelated to the diagonal.

**Paper triage.** Strong and Lean-tractable (Mathlib has contractions, Cauchy, completion), and the fixed-point-freeness is beautiful and literal — but it relocates the primitive from relating to distance, so residue-as-successor is harder to make literal (WS1 records exactly this). **Pre-registered typed fallback:** if C1's `Δ` cannot realize the residue as a concrete bud (D2 stalls), escalate to C3, where fixed-point-freeness is guaranteed by incompleteness of the metric space, and pay the price that the strip test moves to "metric". Not the lead.

### C4 — Löb / guarded-fixpoint phrasing (`▷`, the topos-of-trees reading)

```lean
-- Löb:  (▷P → P) → P.  The successor clause `(Δ x).later := residue (survey x)` is a
-- guarded self-reference; the guarded fixed point EXISTS because the survey is under ▷.
def Δlob {κ} : Proc κ → Proc κ := guardedFix (fun later x => openResidue (survey x) later)
```
The charter's headline interpretation (§5.2, §10): the provability diagonal `(▷P → P) → P` is exactly what turns self-reference into productive temporal unfolding; `Δ` is the guarded fixed point of "open the residue of your own survey, later".

- **Ambient `F` / fpf map:** a guarded endofunctor on `Set^{ℕᵒᵖ}`; Löb induction is the fixed-point-free-diagonal made productive.
- **Success condition:** the guarded fixpoint exists and *is* residue-opening under `▷`; incompleteness (Löb's antecedent never discharges to a completed `P`) = non-termination = productivity, in one modality.
- **Failure mode (named): unbuilt infrastructure.** Mathlib has no topos of trees / `▷` / Löb; building it is heavy (WS1 C3 records this). The identity would be gorgeous but the Lean cost is a from-scratch guarded-recursion library.

**Paper triage.** *Conceptually the deepest phrasing of the engine — Löb IS the fixed-point-free diagonal driving time — but formally the same `Δ` as C1* (a guarded fixed point over the chain `A κ n` restricted to global elements is a `Proc κ`, WS1 C3). **Decision: build C1 (explicit residue recursion over ℕ-indexed threads); import the Löb reading as interpretation only** (the `▷`/Löb prose motivates why the recursion is productive, but is not a Lean dependency). Series-4 R2-over-R3 again: take the encoding that keeps the strip test a syntactic fact in plain Lean.

## Winning candidate: C1 (`Δ` literally = residue-opening on `Proc`), with C4's Löb reading as interpretation and C3 as typed fallback

The decisive move, converting the trivialization crux to a syntactic fact: **`Δ` has no definiens but the residue.** Its successor clause is `(Δ x).1 (n+1) := residue x n`, and `residue` is `ws6_lawvere_incomplete`'s missed element realized as a stage-`(n+1)` bud-opening. There is no state-arithmetic underneath. So "strip diagonal/residue" is not "delete a comment" — it deletes the recursion's successor clause, and `Δ` fails to elaborate. That is what "genuinely drives" means, made checkable.

### Definitions

```lean
namespace Series6.WS3
-- Approx, trunc, Proc, Productive, Moment, prec, Ω_n as in spec/README.md §2–§4.
-- transcribed: ws6_lawvere_incomplete (Cantor/Lawvere diagonal), ws6_omega_nonterminating,
-- omegaState (Series 4).

/-- Stage-n self-survey and its provably-missed element (the residue). -/
def survey {κ} (x : Proc κ) (n : ℕ) : A κ n → (A κ n → Prop)
noncomputable def residue {κ} (x : Proc κ) (n : ℕ) : A κ (n+1)      -- realizes ws6_lawvere_incomplete

/-- The diagonal time-step: successor stage IS the opened residue. No other definiens. -/
noncomputable def Δ {κ} (x : Proc κ) : Proc κ

/-- Successor on moments; a Δ-fixed moment would be a closed self-model. -/
def stepM {κ} : Moment κ → Moment κ := fun ⟨x, n⟩ => ⟨Δ x, n+1⟩
```

### The obligations, each a signature + strategy + paper-decidable verdict

**D1 — the triple identity `ws3_fpf_eq_incompleteness_eq_nontermination`.**
```lean
theorem ws3_fpf_eq_incompleteness_eq_nontermination {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) :
    (∀ m : Moment κ, stepM m ≠ m)                     -- fixed-point-free (no moment at rest)
  ↔ (∀ n, ¬ Function.Surjective (survey x n))         -- incompleteness (Cantor: survey misses d_n)
  ∧ (∀ n, ¬ Function.Surjective (survey x n)) ↔ Productive (Δ x)   -- = non-termination/productivity
```
*Strategy:* not three theorems glued — one chain. Left-to-right: a moment at rest `stepM ⟨x,n⟩ = ⟨x,n⟩` forces `Δ x` to agree with `x` at stage `n+1`, i.e. the survey's residue is already present, i.e. `survey x n` is surjective — contradicting `ws6_lawvere_incomplete`. So fixed-point-freeness and non-surjectivity are the *same* fact viewed on moments vs. on the survey. Non-surjectivity ↔ productivity: the missed element `residue x n` is exactly a bud that `Δ` opens at `n+1`, so "survey always misses" *is* "a bud always opens", i.e. `Productive (Δ x)`. The middle equivalence is definitional once `Δ`'s successor clause is `residue`. *Paper-decidable:* yes — each arrow consumes `ws6_lawvere_incomplete` and the definition of `Δ`; no new coinduction. This is the engine identity as literally one iff-chain.

**D2 — `ws3_residue_is_successor` (Δ literally opens the residue).**
```lean
theorem ws3_residue_is_successor {κ} (x : Proc κ) (n : ℕ) :
    (Δ x).1 (n+1) = residue x n                         -- the successor stage IS the missed element
  ∧ Opened ((Δ x).1 (n+1)) (theBud (survey x n))        -- the opened bud carries d_n
```
*Strategy:* the first conjunct is `rfl` (it is `Δ`'s successor clause). The load-bearing content is realizing `residue x n` as a concrete `A κ (n+1)`: `ws6_lawvere_incomplete` yields a predicate omitted by `survey x n`; the diagonal witness is transcribed as an *element* `d_n`, and `Approx`'s `(n+1)`-layer opens a bud carrying `d_n` (the previous stage had it as an unopened bud). *Paper-decidable:* yes — a direct computation on the transcribed diagonal; the only work is the element-realization (if it stalls, escalate to C3, charter §9).
- *Failure recorded if it were to fail:* if `d_n` cannot be realized as a concrete opened bud (only as an abstract missed predicate), `Δ`'s successor clause is ill-defined on `Proc` — escalate to C3 (metric), where fixed-point-freeness needs no element-realization.

**D3 — `ws3_omega_orbit` (Ω the canonical non-terminating orbit).**
```lean
theorem ws3_omega_orbit {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ n, (Δ (omegaProc κ hinf)).1 n = (omegaProc κ hinf).1 n)   -- Ω recurs AS A STATE
  ∧ (∀ n : ℕ, stepM ⟨omegaProc κ hinf, n⟩ ≠ ⟨omegaProc κ hinf, n⟩)  -- yet its MOMENT strictly advances
  ∧ Productive (omegaProc κ hinf)                                    -- the pure clock never halts
```
*Strategy:* Ω = `{Ω}` faces all of itself, so its survey is complete *in extent* — the residue at each stage is again the self-loop's own bud, so `Δ` returns Ω *as a state* (first conjunct, from `ws6_omega_nonterminating`: complete-in-extent). But the *moment* `⟨Ω, n⟩` advances to `⟨Ω, n+1⟩ ≠ ⟨Ω, n⟩` because the survey-depth strictly increases — closed at no depth (second conjunct). This is exactly why fixed-point-freeness must live on *moments*: the state Ω is a `Δ`-recurrence, the moment Ω is not. Productivity from `ws1_omega_process`. *Paper-decidable:* yes — direct computation on transcribed `omegaState`/`ws6_omega_nonterminating`. Ω is the canonical orbit: the one state where residue = self, so the clock ticks with no change of state — the pure clock.

**D4 — `ws3_diagonal_drives` (the strip test — load-bearing).**
```lean
/-- The coincidence: Δ is genuinely driven by the diagonal. Stated as: Δ's defining
    equation is residue-opening, and NO transition satisfying the successor law exists
    without the survey — deleting `residue`/`survey` leaves `Δ` with no definiens. -/
theorem ws3_diagonal_drives {κ} (x : Proc κ) :
    (∀ n, (Δ x).1 (n+1) = residue x n)                          -- Δ = residue-opening (definitional form)
  ∧ (∀ step : Proc κ → Proc κ,                                  -- forced form: any transition meeting
       (∀ y n, IsSuccResidue (step y) y n) → step = Δ)          --   the successor-law IS Δ (uniqueness)
```
*Strategy:* first conjunct is D2 (definitional form). Second is the *forced* form the coincidence rule demands (charter §7): any `step` whose successor at each stage is the survey-residue of the previous is *equal to* `Δ` — the residue-law pins the transition uniquely, so there is no independent dynamics for the diagonal to be "painted onto". **The strip test, mechanized:** deleting `residue`/`survey` deletes `IsSuccResidue`, and the forced-form statement no longer typechecks — so the theorem *cannot even be stated* without the diagonal, which is the strongest possible form of "strip and it collapses". This is *not* C2's `step_is_diagonal` (a coincidence between two independently-defined things); here the forced form quantifies over *all* transitions and shows the residue-law admits exactly one, so `Δ` is not one choice decorated with diagonal-vocabulary but the *unique* residue-driven map. *Paper-decidable:* the definitional half is `rfl`; the uniqueness half is a stagewise induction using `proc_ext` (WS1) — agreement at stage `0` plus the shared successor-law forces agreement at every stage. **Trivialized is triggered iff** this uniqueness fails, i.e. iff some `step ≠ Δ` also satisfies the successor-law (meaning the law does *not* pin the dynamics and `Δ` carried private content), *or* iff `Δ` retains a definiens after `residue` is deleted.

### Why C1 and not C2/C3/C4

C2 is the trap itself — a provable `step_is_diagonal` over an independently-defined `step` is exactly painted-on, and the strip leaves `step` standing; forbidden. C3 (metric) is the typed fallback: fixed-point-freeness is guaranteed by incompleteness of the refused completion, but the strip test moves to "metric"/"Cauchy" and residue-as-successor is no longer literal — taken only if D2's element-realization stalls. C4 (Löb) is the same `Δ` as C1 with unbuilt infrastructure; its `▷`/Löb story is the interpretation that explains *why* the residue-recursion is productive, kept as prose. The design principle (Series 4 R2-over-R3, WS1 C2): **take the encoding on which the strip test is a syntactic fact — `Δ` with no definiens but the residue — and hold the metric setting as the typed fallback.**

## Outcome classes (per charter §7)

- **Discharged:** D1–D4 on C1. `ws3_fpf_eq_incompleteness_eq_nontermination` as one iff-chain; `ws3_residue_is_successor` by `rfl` + diagonal realization; `ws3_omega_orbit`; `ws3_diagonal_drives` with the uniqueness (forced) form proved and the strip a syntactic fact.
- **Impossibility proved:** reachable if the Cantor residue *cannot* be realized as a concrete opened bud on `Proc` (only as an abstract missed predicate) — a sharp negative for the thread encoding, escalating to C3 (metric), where fixed-point-freeness needs no element-realization. Not expected: the finite diagonal yields an element, and `Approx`'s layers open buds.
- **Partial — definitional-only:** if `ws3_diagonal_drives`'s *definitional* half holds (`Δ = residue-opening`) but the *forced/uniqueness* half is not proved (some other residue-respecting transition might exist), the engine is delivered on its definitional form only — reported Partial with the uniqueness as the named open obligation, per the coincidence rule. This is the honest halfway house short of Trivialized.
- **Trivialized (the real risk, named exactly):** triggered iff **`Δ` is defined independently and the diagonal is only related by a provable theorem** (the C2 shape — `step` corecursed elsewhere, `step_is_diagonal` proved, strip leaves `step` intact), *or* iff the uniqueness form fails so the residue-law does not pin the transition (`∃ step ≠ Δ` satisfying the successor-law), *or* iff `Δ` retains any definiens after `residue`/`survey` are deleted. Any of these means the engine is painted on; WS3 reports **Trivialized** and hands the finding to WS7. Returning this honestly is a program success (charter §7, §8).

## Deliverable

`series-6/formal/ws3.lean`: transcribed diagonal machinery (`ws6_lawvere_incomplete`, `ws6_omega_nonterminating`, `omegaState`; carrier `Approx`, `trunc`, `Proc`, `Productive` from WS1; `Moment`, `stepM`); `survey`, `residue`, `Δ`; `ws3_fpf_eq_incompleteness_eq_nontermination` (D1), `ws3_residue_is_successor` (D2), `ws3_omega_orbit` (D3), `ws3_diagonal_drives` (D4 — the strip test, load-bearing); the C3 metric fallback typed but unbuilt. Axiom check: `#print axioms Δ` must show `residue`/`survey` (hence `ws6_lawvere_incomplete`) in the dependency cone — a `Δ` whose axiom print does *not* mention the diagonal is painted on and fails the deliverable. `#print axioms ws3_diagonal_drives` on the standard three plus the transcribed diagonal.
