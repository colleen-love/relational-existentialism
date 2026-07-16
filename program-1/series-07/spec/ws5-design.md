# WS5 — The limit-atomlessness loophole

**Design doc. Series 07. Owns: the ONE real escape from the Import Theorem — relaxing ingredient (3) from every-moment to limit atomlessness, with transient atoms at the finite stages (the metric / Cauchy route) — characterized as a genuine relaxation (not a counterexample) and adjudicated by the pre-registered fork: a genuine atomless plural world, or import-in-time.**

*Series 07 is standalone; names transcribed into `series-07/formal/Series07/ws5.lean`, re-namespaced `Series07.WS5` (see `spec/README.md` §6). The carrier — `Proc`, `allNonempty`, `Productive`, `omegaProc`, `proc_ext`, `allNonempty_unique`, `ws1_productive_unique` — is **already built** in Series 06 `ws1.lean` (`ws1_no_productive_plurality` is exactly this loophole's negative twin); WS5 cites it, never redefines it. The loophole structure is fixed in `spec/README.md` §6 ("The loophole structure (WS5)"); the metric home echoes Series 06's typed-but-unbuilt C4 fallback.*

## The object at stake

The Import Theorem (WS2) is airtight only for **every-moment** atomlessness (`Productive` = `∀ n, allNonempty κ n (x.1 n)`). The charter (§4.3, §5.3) names the single relaxation that is neither an import (drop 1) nor an intensional ghost (drop 2): let the **finite** stages of a process carry leaves — genuine atoms, `∃ n, ¬ allNonempty κ n (x.1 n)` — and demand atomlessness only of the refused **limit**. This is a real drop of ingredient (3), the one way to keep plain relating *and* plurality. WS5 must (a) prove it is a *relaxation, not a hole*: any plurality of limit-atomless processes is distinguished by a finite-stage leaf, a transient atom — so it never contradicts WS2, which quantified over every-moment atomlessness; and (b) **adjudicate the pre-registered fork**: is "atomless in the limit, plural via transient atoms" a genuine atomless plural world (headline weakens to *impossible except in the limit*), or is the transient leaf just an atom paid in installments (Import Theorem stands unqualified)? Either verdict is terminal and valid (charter §5.5, §6 WS5).

The every-moment-vs-limit line is the whole object. WS2 owns one side (`ws1_productive_unique`: every-moment atomless ⇒ unique ⇒ collapse); WS5 owns the other and shows it does not escape the atom, only defers it. The line is sharp in Lean: `Productive x` is `∀ n, allNonempty κ n (x.1 n)`; limit-atomlessness *negates the `∀`* while keeping atomlessness at the limit — `(∃ n, ¬ allNonempty κ n (x.1 n))` at the finite stages. WS2's theorem consumes the `∀`; WS5's escape survives precisely by dropping it, and the question is whether dropping it buys a genuinely atomless plural world or only relocates the atom into the stages that the `∀` used to forbid.

Note the exact duality with Series 06: `ws1_no_productive_plurality` is this loophole's negative twin — it proves that *every-moment*-atomless plurality is impossible on `Proc` (the `∀`-strong `Productive`), which is precisely the case WS5 does *not* touch. WS5 works one quantifier weaker, on the threads Series 06's negation excludes, and inherits `allNonempty_unique` — the very engine that killed productive plurality — now as the engine that *forces the transient atom*. The same uniqueness fact both closes the every-moment door and pins the leaf at the finite stage; WS5 does not re-prove it, it re-aims it.

**Ambient theory.** `spec/README.md` §2 (the four ingredients; `SHNE`; `HereditarilyAtomless`) and the §6 loophole structure. The carrier is Series 06's finite-approximation process: `Proc κ = { x : (n:ℕ) → Approx κ n // ∀ n, trunc κ n (x (n+1)) = x n }`, `allNonempty κ n s`, `Productive x`, `omegaProc hinf`, `proc_ext`, and the load-bearing `allNonempty_unique` (the only hereditarily-nonempty depth-`n` approximation is `omegaApprox hinf n`). Concrete home for the fork's positive horn: the behavioral pseudometric / Cauchy-in-an-incomplete-space (Mathlib `Metric`, `CauchySeq`), the Lawvere "quality as distance" reading; Banach needs completeness, so a contraction on the incomplete leafy subspace is fixed-point-free — the echo of Series 06's C4 fallback, now the loophole itself.

## Candidates

### C1 — Limit-atomlessness relaxes (3); plurality via transient finite-stage leaves (the lead)

```lean
theorem ws5_limit_reintroduces_leaves (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n))
```
Any two DISTINCT processes differ at a finite stage (`proc_ext`), and that stage necessarily carries a leaf in at least one — because an every-moment-atomless stage is UNIQUE (`allNonempty_unique`: both atomless at `n` ⇒ both `= omegaApprox hinf n` ⇒ equal there).

- **Ambient:** `Proc κ`; the finite-stage-leaf predicate `¬ allNonempty κ n (·)`; the uniqueness engine `allNonempty_unique`.
- **Success condition:** the term typechecks — the distinguisher between any two processes is a finite-stage leaf (a transient atom). Hence limit-atomlessness is a *relaxation* of (3), never a counterexample to WS2.
- **Failure mode:** none structural — it is `proc_ext` + `allNonempty_unique`, both transcribed and machine-checked in Series 06. The only risk is downstream: that "differ at a stage with a leaf" is too weak to force the *adjudication* verdict (checked in C3/C4).

**Paper triage.** Decidable-on-paper and essentially proved: contrapositive of `allNonempty_unique` threaded through `proc_ext`. This is the theorem that turns the loophole from "a hole in WS2" into "a documented relaxation of ingredient (3)". **Winner (the characterization).**

### C2 — The metric / Cauchy encoding as the concrete witness

```lean
def bdist (x y : Proc κ) : ℝ≥0∞ :=            -- behavioral (ultra)distance: 2^{-(first n where x.1 n ≠ y.1 n)}
theorem ws5_metric_transient_atoms (hinf : ℵ₀ ≤ κ) :
    ∃ σ : ℕ → Proc κ,
      (∀ k, ∃ n, ¬ allNonempty κ n ((σ k).1 n))            -- each σ k is LEAFY (limit-atomless candidate)
      ∧ (Function.Injective σ)                              -- plurality
      ∧ Filter.Tendsto (fun k => bdist (σ k) (omegaProc hinf)) Filter.atTop (nhds 0)  -- → the atomless Ω
```
The concrete home for the fork's positive horn: a family `σ_k` of distinct **leafy** threads (each agreeing with Ω through depth `k`, then leafing out at depth `k+1`), all converging behaviorally to the unique atomless `omegaProc`. Distinct because their finite stages differ; leafy at every finite stage; atomless only in the refused limit. Banach's fixed-point needs completeness, so the "descend one level" contraction on the leafy subspace (whose only fixed point, Ω, is *absent*) is fixed-point-free — Series 06's C4 made literal.

The construction discipline (why the family is compatible, not free): `Proc`'s `trunc` constraint propagates difference *upward* only (`trunc κ n (x.1 (n+1)) = x.1 n`, so agreement at `n+1` forces agreement at `n`), which is exactly what lets a thread agree with Ω through depth `k` and *then* diverge — `σ_k.1 m = omegaApprox hinf m` for `m ≤ k`, and at `k+1` a leaf element (an empty-successor node) trunc-ing onto `omegaApprox hinf k`. The behavioral distance is the ultrametric `2^{-(first-difference stage)}`, so `bdist (σ_k) (omegaProc) = 2^{-(k+1)} → 0`: the family is Cauchy for Ω without containing Ω. The Lawvere reading is that "quality is distance to Ω", and the loophole is precisely the *incompleteness* of the leafy subspace — the atomless limit is the one point completion would add and the world refuses to reach.

- **Ambient:** the behavioral ultrametric `bdist` on `Proc` (Mathlib `Metric` / `EMetric`, `CauchySeq`, `Filter.Tendsto`); the incomplete leafy subspace `{x | ∃ n, ¬ allNonempty κ n (x.1 n)}`.
- **Success condition:** the witness family exists — distinct, leafy, converging to Ω — so limit-atomless plurality is *realized*, not merely permitted.
- **Failure mode:** **non-convergence / the pun does the work.** Risk (Series 06's own C4 caution) that "atomless in the limit" is proved of a metric space with no faithful tie back to relating; or that `σ_k` cannot be built compatibly (the `trunc` constraint forces `σ_k.1 m = omegaApprox hinf m` for `m ≤ k`, and the leaf at `k+1` must trunc onto `omegaApprox hinf k` — constructible, but fiddly).

**Paper triage.** The *existence* of leafy plurality is decidable-and-easy: leafy threads are NOT subject to `allNonempty_unique` (they fail its hypothesis), so unlike productive threads they are many — the profinite thread space minus the single point Ω. The metric *packaging* (`bdist`, `CauchySeq`, `Tendsto`) is Mathlib-tractable but is build labor. **Winner (the concrete witness), with the `CauchySeq` packaging flagged as build-owed; the bare existence-of-leafy-plurality is the paper-certain core.**

### C3 — The "genuine escape" reading (the fork's positive horn)

```lean
-- LoopholeVerdict.genuineEscape : the limit is genuinely atomless; NO single object carries a
-- PERMANENT atom; every leaf is healed above. Privileging the limit as the object, the world is
-- atomless AND plural — the Import Theorem's headline weakens to "impossible EXCEPT in the limit".
theorem ws5_genuine_escape_horn (hinf : ℵ₀ ≤ κ) :
    (∃ σ : ℕ → Proc κ, Function.Injective σ ∧ ∀ k, ∃ n, ¬ allNonempty κ n ((σ k).1 n))
      → HeadlineWeakens                                    -- "impossible except in the limit"
```
Success condition: if the limit point is the ontologically real object and its finite approximations are mere scaffolding, then a plural family converging to an atomless limit *is* an atomless plural world. Failure mode (its own defeat, and the reason it is not the lead): **no finite moment is atomless** — `ws5_limit_reintroduces_leaves` says the distinction lives entirely in the leafy finite stages, never in the atomless limit, where all the `σ_k` coincide (with Ω). The plurality is invisible to the atomless limit and visible only where the atoms are.

**Paper triage.** Coherent and terminal-if-chosen (charter §5.5: "the loophole may be the real world"). It is the horn WS5 must keep open and honestly flag, but it privileges the limit over the moments against the theorem's own diagnostic (the distinguisher is always a moment-bound atom). **Retain as the pre-registered alternative verdict, not the designed-toward one.**

### C4 — The "import-in-time" reading (the fork's negative horn) — designed toward

```lean
-- LoopholeVerdict.importInTime : the transient leaves are atoms paid in INSTALLMENTS. The
-- plurality's distinguisher is PROVABLY always a finite-stage leaf (ws5_limit_reintroduces_leaves)
-- — a genuine atom at a genuine (finite) moment — so plurality is bought with an atom, deferred
-- but not escaped. The Import Theorem stands UNQUALIFIED.
theorem ws5_import_in_time_horn (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n)) :=
  ws5_limit_reintroduces_leaves hinf x y hxy
```
Success condition: the distinction between any two limit-atomless processes factors through a finite-stage atom — so it is an import (an atom in the carrier), merely distributed over the stages rather than carried permanently. Failure mode: **the transient atoms aren't forced** — if a plurality of limit-atomless processes could differ *without* any finite-stage leaf, the distinction would live in the pure atomless limit and the horn would collapse into C3. But `allNonempty_unique` forecloses exactly that: two every-moment-atomless stages coincide, so a difference *requires* a leaf.

**Paper triage.** The horn is `ws5_limit_reintroduces_leaves` re-read as a verdict: the plurality is provably atom-carried at finite moments. This is the reading consistent with the program's predicted headline (`spec/README.md` §5: `importForced`), and its strip test (below) is decisive. **Winner (the designed-toward verdict); C3 retained as the honest, terminal alternative.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | distinct limit-atomless ⇒ finite-stage leaf | `proc_ext`, `allNonempty_unique` | yes — contrapositive of a built lemma | **win (characterization)** |
| C2 | leafy plurality converging to Ω exists | `bdist`, `CauchySeq`, `Tendsto` | existence yes; metric packaging build-owed | **win (witness)** |
| C3 | genuine escape → headline weakens | limit-as-object | coherent, terminal-if-chosen | pre-registered alt |
| C4 | import-in-time → theorem unqualified | `ws5_limit_reintroduces_leaves` | yes — it IS C1 as a verdict | **win (verdict)** |

## Winning candidates: C1 (characterization) + C2 (witness) discharge; the fork resolves to C4 (import-in-time), C3 flagged terminal

### Definitions and obligations (cite `spec/README.md` §2/§6; `Proc`/`allNonempty` from Series 06 `ws1.lean`)

```lean
namespace Series07.WS5
-- Proc, Approx, trunc, allNonempty, Productive, omegaProc, omegaApprox, proc_ext,
-- allNonempty_unique, ws1_productive_unique — transcribed (README §6, Series 06 ws1.lean).

/-- Limit-atomlessness: finite stages carry a leaf, but the process is a Cauchy witness for
    the atomless Ω. The finite-stage clause is `∃ n, ¬ allNonempty κ n (x.1 n)` (README §6). -/
def LimitAtomless (hinf : ℵ₀ ≤ κ) (x : Proc κ) : Prop :=
  (∃ n, ¬ allNonempty κ n (x.1 n)) ∧ Filter.Tendsto (fun n => bdist x (omegaProc hinf) ) _ _  -- limit is Ω

inductive LoopholeVerdict | genuineEscape | importInTime
```

**D1 — the loophole is a relaxation, not a counterexample.** `ws5_limit_reintroduces_leaves` (C1).
*Strategy:* `rw [proc_ext] at hxy; push_neg` gives `n` with `x.1 n ≠ y.1 n`; `by_contra` the disjunction, `push_neg` to `allNonempty κ n (x.1 n) ∧ allNonempty κ n (y.1 n)`, rewrite both by `allNonempty_unique hinf n` to `omegaApprox hinf n`, contradicting `x.1 n ≠ y.1 n`. *Paper-decidable:* yes — a five-line consequence of two transcribed lemmas.
*Strip annotation (delete "transient/finite-stage"):* the conclusion becomes bare `∃ n, ¬ allNonempty κ n (x.1 n) ∨ …` — a **genuine leaf, a genuine atom**, at a genuine finite moment. The leaf **survives** the strip: it is not a definitional artifact of the word "transient" but a forced atom. This is precisely what makes the loophole a real relaxation of (3) and drives the C4 verdict.

**D2 — the concrete metric witness.** `ws5_metric_transient_atoms` (C2).
*Strategy:* build `σ_k` by `σ_k.1 m = omegaApprox hinf m` for `m ≤ k`, and at `k+1` a leaf element trunc-ing onto `omegaApprox hinf k`, extended compatibly above; `bdist (σ_k) (omegaProc hinf) = 2^{-(k+1)} → 0`; injectivity from first-difference-stage. *Paper-decidable:* the *existence of distinct leafy threads* is yes-and-immediate (they escape `allNonempty_unique`); the `CauchySeq`/`Tendsto` packaging is Mathlib-routine but build-owed. *Strip annotation:* delete "finite-stage" from "leafy" and each `σ_k` becomes atomless — but then `allNonempty_unique` forces `σ_k = omegaProc` for all `k`, killing injectivity. The leaf is load-bearing for the plurality; strip it and the plurality collapses (Series 06's `ws1_no_productive_plurality`). Non-circular: the finite-stage leaf is what the plurality *is*.

**D3 — the adjudication (the pre-registered fork).** `ws5_loophole_adjudication` (C3 vs C4).
```lean
def ws5_loophole_adjudication : LoopholeVerdict := .importInTime
theorem ws5_adjudication_justified (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n)) :=
  ws5_limit_reintroduces_leaves hinf x y hxy
```
*Strategy:* the verdict is a datum; its justification is D1 re-read — every distinction between limit-atomless processes is carried by a finite-stage atom, so the plurality is bought with an atom (deferred, not escaped): `importInTime`. *Paper-decidable:* the justification is D1 (yes); the *choice* of horn is a philosophical adjudication, made against the diagnostic that no atomless moment ever carries the distinction. *Strip annotation:* strip "transient/in-time" and the verdict reads "plurality carried by an atom" — plain drop-(1)/(3) import; the temporal dressing adds nothing the strip removes, which is exactly why import-in-time, not genuine escape, is the honest reading.

The fork is genuine and both horns are terminal, so WS5 does not pretend the adjudication is a theorem — it is a *ruling on a theorem*. The theorem (`ws5_limit_reintroduces_leaves`) is horn-neutral: it says the plurality lives in the leafy finite stages and nowhere else. The two horns disagree only on what to call that fact. **Import-in-time** reads a leaf at moment `n` as an atom that was paid — the process *did* have an atom, at that moment, and "healed only in a limit the world never reaches" (charter §4.3) is not payment refunded but payment made on the installment plan. **Genuine escape** reads the same leaf as scaffolding of an object that *is* its limit, where the limit is atomless and the finitely-many atoms are artifacts of a presentation, not features of the thing. WS5 designs toward import-in-time because the theorem's own witness is moment-bound: the atomless limit is a *single point* (all `σ_k` meet Ω there), so it is not where the plurality is, and a world's plurality cannot live in the one place it is atomless. That asymmetry — plurality everywhere the atoms are, unity where they are healed — is the report WS7 should weigh.

## Outcome classes (per charter §7)

- **Discharged:** D1 (`ws5_limit_reintroduces_leaves` — the loophole is a relaxation, not a counterexample; a five-line consequence of transcribed `proc_ext` + `allNonempty_unique`).
- **Discharged / Partial:** D2 (`ws5_metric_transient_atoms`) — the existence of leafy plurality converging to Ω is Discharged; the full `CauchySeq`/`Metric` packaging is Partial (Mathlib-routine, build-owed, per Series 06's typed-but-unbuilt C4).
- **The pre-registered FORK (D3), both terminal and valid:**
  - **import-in-time (designed toward, `ws5_loophole_adjudication := .importInTime`):** the transient leaves are atoms paid in installments; the plurality's distinguisher is provably always a finite-stage atom (D1); the **Import Theorem stands unqualified** (`importForced`, `spec/README.md` §5).
  - **genuine escape (`.genuineEscape`, C3, retained honestly):** if the atomless limit is privileged as the object, the world is atomless-and-plural and the **headline weakens** from "impossible" to "impossible except in the limit" — still strong, honestly flagged (charter §5.5).
- **Strip test (aggregate to WS7):** deleting "transient/finite-stage" leaves a forced genuine atom (D1) and collapses the plurality (D2) — the leaf is load-bearing and non-circular, not a rigged qualifier.
- **Routed to WS7 (the verdict input):** WS5 hands WS7 a *designed-toward* ruling (import-in-time) plus the horn-neutral theorem it rests on. If WS7's aggregate audit judges the atomless-limit-as-object reading legitimate, it may adopt `.genuineEscape` and the program headline weakens to "impossible except in the limit" — a re-pointing WS5 pre-authorizes and does not treat as a defeat (charter §5.5, §9). The designed default is import-in-time, aligning WS5 with the predicted `importForced` (`spec/README.md` §5); WS5 states the case for it but leaves the terminal choice to WS7's circularity audit.

## Deliverable

`series-07/formal/Series07/ws5.lean`: transcribed carrier (`Proc`, `allNonempty`, `Productive`, `omegaProc`, `proc_ext`, `allNonempty_unique`, `ws1_productive_unique` — README §6); `LimitAtomless`, `LoopholeVerdict`; `ws5_limit_reintroduces_leaves` (D1), `ws5_metric_transient_atoms` (D2, metric packaging typed, `CauchySeq` core owed), `ws5_loophole_adjudication` + `ws5_adjudication_justified` (D3). Axiom check: `#print axioms ws5_limit_reintroduces_leaves` reduces through `allNonempty_unique` / `proc_ext` to the standard `propext` / `Classical.choice` / `Quot.sound` (axiom-clean in Series 06).
