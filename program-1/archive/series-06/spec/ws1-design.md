# WS1 — The process and its gate

**Design doc. Series 06, blocking workstream. Owns: the process carrier `Proc` over the plain carrier `νPk`, its notion of sameness (stagewise, un-quotiented), the gate on which the whole program is conditional (the process exists, keeps plurality, and does not collapse to the limit's behavioral identity), and the recovery of Ω as the self-knowing-that-never-closes.**

*Series 06 is standalone; all Series 04/05 names used here are transcribed into `series-06/formal/ws1.lean` and re-namespaced `Series06.WS1` (see `spec/README.md` §5). Shared objects (`Approx`, `trunc`, `Proc`, `Productive`, `Ω_n`) are defined in `spec/README.md` §2 and only cited here.*

## The object at stake

The charter (§3) proves that any *finished* object over `νPk` that is genuinely globally atomless collapses to Ω. The escape (§5) is to build a **process** — a compatible thread of founded approximations — and keep it *un-quotiented*, so the distinction the completed object destroys survives in the founded history. The design question is which encoding of "the process over `νPk`" (a) **exists** as a genuine type, (b) carries a **notion of sameness that keeps plurality** yet is not so fine that everything is trivially distinct, (c) **does not collapse** under the productivity (global-atomlessness) demand, and (d) recovers **Ω = {Ω}** as a genuine productive inhabitant — the non-terminating self-loop.

The gate (a)+(b)+(c) is existential for the program (charter §9). Every candidate is triaged first on a decidable-on-paper version of it.

**Ambient theory.** `spec/README.md` §2: base carrier `νPk κ` (plain, unlabelled — the honestly atom-free carrier); functor `F = P_κ`; the final ω-chain `A κ n` with truncations `trunc`; `Proc κ = { x : ∀ n, A κ n // ∀ n, trunc (x (n+1)) = x n }` with stagewise identity. No labels `Q`, by the §3 sharpening: an imported label would forfeit genuine atomlessness before the process starts.

## Candidates

### C1 — Terminal coalgebra itself (`νPk`), no process at all

```lean
def World1 (κ) : Type u := (νPk κ).X            -- the finished object
```
The null candidate: keep the Series 04 carrier, hope plurality survives global atomlessness.

- **Sameness:** bisimulation = identity (`bisim_eq`).
- **Success condition:** the hereditarily-nonempty subcarrier is plural.
- **Failure mode:** **collapse.** `ws2_grounded_core_subsingleton` — the hereditarily-nonempty subcarrier of `νPk` is a subsingleton `{Ω}`. Genuine global atomlessness gives exactly one object.

**Paper triage.** Decidable-on-paper and decided against: this *is* the Static Collapse (`ws2_collapse`). Reject; it is the object WS2 refutes, retained only as the baseline the process must beat.

### C2 — Stagewise process, un-quotiented thread (`Proc κ`, stagewise identity) — the lead

```lean
def Proc (κ) : Type u := { x : (n:ℕ) → A κ n // ∀ n, trunc κ n (x (n+1)) = x n }
-- identity: x = y ↔ ∀ n, x.1 n = y.1 n   (NOT quotiented by bisimulation)
```
The world is the compatible thread of founded approximations; sameness is stagewise; we never take the terminal-coalgebra quotient.

- **Ambient `F`:** the final ω-chain of `P_κ`; each `A κ n` founded; `Proc` is its limit *as a set of threads*, kept before any behavioral quotient.
- **Success condition:** `Proc` exists; distinct productive threads exist (plurality); Ω recovered; no collapse.
- **Failure mode:** **either trivial or collapsing.** If stagewise identity secretly equals bisimulation on productive threads, plurality collapses (the C1 failure returns one level up); if it is *too* fine (every thread distinct for spurious reasons), plurality is cheap and WS6's achievement launders. The gate is exactly: *is there a productive plurality that is neither collapsed nor spurious?*

**Paper triage.** The decidable-on-paper gate has two halves. **(i) Non-collapse:** two productive threads that differ at some finite stage are stagewise-distinct *by construction* — and, crucially, the maximal-relation bisimulation argument that collapses `νPk` (`ws2_collapse`) **cannot be run on `Proc`**, because a "bisimulation on `Proc`" would have to respect the founded-stage structure, and the founded stages genuinely differ; the collapse needs the completed (leaf-free) object, which `Proc` refuses to be. Checkable by inspection: the collapse proof consumes `bisim_eq` on `(νPk).X`; `Proc` has no such identity. **(ii) Non-triviality:** stagewise identity is *coarser* than raw function equality where it should be (compatible threads that agree at all stages are equal) and *finer* than bisimulation (threads with the same limit but different founded history are distinct). This is the "carry a distinction the snapshot can't see" of the charter, made a decidable structural fact. **Winner**, subject to exhibiting the productive plurality concretely (routed to WS6) and Ω (D3 below).

### C3 — Guarded / topos-of-trees object (`Set^{ℕᵒᵖ}` with the later modality)

```lean
-- the presheaf n ↦ A κ n with restriction trunc; the "later" modality ▷ shifts the index
structure Tree (κ) where obj : ∀ n, A κ n ; restr : ∀ n, trunc κ n (obj (n+1)) = obj n
```
The charter's lead phrasing: `Proc` *is* a global element of the topos of trees, and the "later" modality `▷` is time; Löb's theorem is the diagonal generating the process.

- **Ambient `F`:** a guarded functor on `Set^{ℕᵒᵖ}`; the terminal object is not collapsed as in `Set`.
- **Success condition:** the guarded fixed point exists (Löb); bisimulation-in-the-topos keeps plurality.
- **Failure mode:** **non-existence of the machinery in Lean.** Mathlib has no topos of trees / later modality; building it is heavy, and the guarded-fixed-point apparatus (Löb induction) would have to be developed from scratch.

**Paper triage.** *Conceptually the lead, formally the same object as C2.* A global element of the topos of trees `Set^{ℕᵒᵖ}` restricted to the chain `A κ n` **is exactly** a `Proc κ` (a compatible thread), and stagewise identity is equality of global elements. So C3 and C2 denote the same carrier; C3 adds the topos vocabulary (`▷`, Löb) that motivates WS3's engine but requires unbuilt Lean infrastructure. **Decision: build C2 (plain ℕ-indexed threads) as the carrier; import the topos-of-trees reading as interpretation only** (the `▷`/Löb story is prose for WS3, not a Lean dependency). This is the Series-04 "R2 over R3" move: take the encoding that keeps the gate decidable in plain Lean.

### C4 — Metric completion / Cauchy-non-convergent (Lawvere-enriched)

```lean
-- put the behavioural (bisimulation) pseudometric on νPk; the process is a
-- Cauchy sequence in an INCOMPLETE space (the completion is refused)
def bdist (κ) : (νPk κ).X → (νPk κ).X → ℝ≥0∞      -- behavioural distance
```
The world is a Cauchy-but-non-convergent family; distance-0-is-identity bites only at the refused limit. Asymmetric (quasi-)metric encodes the two-sided face.

- **Ambient `F`:** the coalgebra with its behavioural pseudometric (Mathlib metric spaces).
- **Success condition:** an incomplete space where the diagonal contraction is fixed-point-free (Banach needs completeness).
- **Failure mode:** **the pun does the work, not the coalgebra.** Risk that "atomless" (metric incompleteness) is proved of a metric space with no faithful tie back to the relating — WS3's engine-drive strip fails.

**Paper triage.** *Strong and Lean-tractable (Mathlib has metric spaces, Cauchy, completion, contractions), and beautiful* — metric incompleteness = fixed-point-free contraction = the engine identity, literally; asymmetric distance = the two-sided face (WS5). But it changes the primitive from relating to distance, and the residue-as-successor (WS3) is harder to make literal in a metric than in the thread encoding. **Pre-registered alternative:** if C2's `Δ` cannot be made literal (WS3 strip fails on the thread encoding), escalate to C4, where the contraction is manifestly fixed-point-free. Retained as WS1's typed fallback, not the lead.

### C5 — Pro-object (final chain as a diagram in `Pro(Set)`)

```lean
-- the world is the DIAGRAM n ↦ A κ n, an object of the pro-category, not its limit
```
Sameness is pro-isomorphism; the world is the diagram, never the limit.

- **Failure mode:** **no pro-category in Mathlib**; and pro-isomorphism of the *constant-shape* chain reduces to stagewise agreement, i.e. C2 again, so it buys nothing C2 lacks while costing infrastructure.

**Paper triage.** Reduces to C2 for our chain (the abstract pro-object over `ℕ` with mono-ish restrictions is presented by its threads). **Reject as carrier; retain "the world is the diagram, not the limit" as the interpretive gloss** shared with C3.

## Winning candidate: C2 (stagewise un-quotiented process over `νPk`), with C3's topos reading as interpretation and C4 as the typed fallback

The decisive moves, converting the existential gate to decidable facts:

1. **Refuse the behavioral quotient.** The collapse (`ws2_collapse`) *is* the passage to bisimulation-identity on the completed object; `Proc` never takes it, so the collapse has no carrier to fire on. Non-collapse is not proved against the collapse — it is that the collapse's hypothesis (`bisim_eq` on a finished `X`) is simply absent.
2. **Keep sameness stagewise.** Finer than bisimulation (history-distinguishing), coarser than raw intensional junk (compatible threads agreeing everywhere are equal). Plurality lives exactly in the gap.

### Definitions

```lean
namespace Series06.WS1
-- Approx, trunc, Proc, Productive, Ω_n as in spec/README.md §2 (transcribed carrier machinery:
-- PkObj, PkMap, νPk, bisim_eq, omegaState, ws2_collapse, ws6_omega_nonterminating).

/-- Stagewise identity is decidable-shaped: agreement at every finite stage. -/
theorem proc_ext {κ} (x y : Proc κ) : x = y ↔ ∀ n, x.1 n = y.1 n

/-- Ω as a process: the depth-n truncation of the self-loop. -/
noncomputable def omegaProc (κ) (hinf : ℵ₀ ≤ κ) : Proc κ :=
  ⟨fun n => omegaApprox κ hinf n, omega_compat κ hinf⟩
```

### The obligations, each decidable-on-paper

**D1 — `Proc` exists and stagewise identity is well-behaved.**
```lean
theorem ws1_process_exists {κ} : Nonempty (Proc κ)
theorem ws1_stagewise_id {κ} (x y : Proc κ) : x = y ↔ ∀ n, x.1 n = y.1 n     -- proc_ext
```
*Strategy:* `Proc` is a subtype of a Π-type; nonempty via `omegaProc` (D3). `proc_ext` is `Subtype.ext_iff` + `funext`. *Paper-decidable:* yes — pure type formation, no coinduction.

**D2 — the gate: the process keeps plurality and does not collapse.**
```lean
/-- The collapse hypothesis is absent: there is no `bisim_eq`-style identity on `Proc`
    forcing productive threads equal. Stated as: stagewise identity is strictly coarser
    than "equal limit" and strictly finer than "bisimilar", so two productive threads
    differing at a finite stage are distinct. -/
theorem ws1_no_collapse {κ} (hinf : ℵ₀ ≤ κ)
    (x y : Proc κ) (n : ℕ) (h : x.1 n ≠ y.1 n) : x ≠ y
theorem ws1_productive_plurality {κ} (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y            -- witness routed to WS6
```
*Strategy:* `ws1_no_collapse` is immediate from `proc_ext` (differ at a stage ⇒ not stagewise-equal ⇒ not equal) — the whole point is that this needs *no* refutation of a bisimulation, because `Proc` carries none. The productive plurality **witness** (two productive threads differing at a finite stage) is built in WS6 from the diagonal engine (WS3); WS1 states it and consumes the WS6 witness. *Paper-decidable:* the non-collapse half is a one-line consequence of `proc_ext`; the plurality half is a forward obligation to WS6 (the honest dependency, tracked in `charter-status.md`).
- *Failure recorded if it were to fail:* if the only productive threads turn out stagewise-equal to `omegaProc` (i.e. Ω is the unique productive thread, the C1 collapse resurfacing one level up), the gate fails — Impossibility proved for the stagewise encoding, escalate to C4 (metric), where distinct Cauchy sequences are manifestly available.

**D3 — Ω recovered as the non-terminating self-loop.**
```lean
theorem ws1_omega_process {κ} (hinf : ℵ₀ ≤ κ) : Productive (omegaProc κ hinf)
theorem ws1_omega_nonclosing {κ} (hinf : ℵ₀ ≤ κ) :
    -- complete in extent at every stage, yet closed at no stage (transcribed ws6_omega_nonterminating)
    ∀ n, omegaApprox κ hinf n ≠ trunc κ n (omegaApprox κ hinf (n+1)) → False  -- compatibility
    ∧ (∀ n, ∃ bud, IsBud (omegaApprox κ hinf n) bud)                          -- a bud at every stage: never closes
```
*Strategy:* `omegaApprox` is `omegaState` truncated to depth `n`; productivity because the self-loop's single bud opens at every stage (transcribed `ws6_omega_nonterminating`); compatibility by `trunc` on the self-singleton. *Paper-decidable:* yes — a direct computation on the transcribed `omegaState`.

### Why C2 and not C3/C4

C3 (topos of trees) denotes the *same* carrier as C2 but needs unbuilt Lean infrastructure; its value is the `▷`/Löb interpretation for WS3, kept as prose. C4 (metric) is the strong fallback and is genuinely Lean-tractable, but changes the primitive from relating to distance and makes WS3's residue-as-successor harder to render literal; taken only if C2's `Δ` cannot be made to drive (WS3 strip). The design principle (Series 04 R2-over-R3, Series 05 C2): **take the encoding that keeps the gate a one-line consequence of the carrier's own structure, and hold the richer settings as typed fallbacks.**

## Outcome classes (per charter §7)

- **Discharged:** D1–D3 on C2; `ws1_no_collapse` from `proc_ext`, `omegaProc` productive, plurality witness consumed from WS6.
- **Impossibility proved:** reachable only if Ω is the *unique* productive thread under stagewise identity — the collapse resurfacing — a sharp negative escalating to C4. Not expected: the diagonal (WS3) manufactures distinct productive residue-threads.
- **Partial:** carrier delivered, productive-plurality witness flagged as the WS6/WS3 forward dependency (the honest open, exactly as Series 05 WS1 flagged its colimit-functor fallback).

## Deliverable

`series-06/formal/ws1.lean`: transcribed carrier machinery (self-contained); `Approx`, `trunc`, `Proc`, `Productive`, `omegaProc`, `omegaApprox`; `ws1_process_exists` + `ws1_stagewise_id` (D1), `ws1_no_collapse` + `ws1_productive_plurality` [WS6-witnessed] (D2), `ws1_omega_process` + `ws1_omega_nonclosing` (D3); the C4 metric fallback typed but unbuilt. Axiom check: `#print axioms ws1_no_collapse` should reduce to `proc_ext` (`propext`, `Quot.sound` at most).

---

## BUILD FINDING (2026-07-10, routed here per protocol §2 Phase C) — the gate returns Impossibility on C2

The build realized C2 concretely as `Approx κ 0 = PUnit`, `Approx κ (n+1) = PkObj κ (Approx κ n)`,
`Proc κ = { x : ∀ n, Approx κ n // ∀ n, trunc n (x (n+1)) = x n }`, with `Productive` the honest
hereditary-non-emptiness liveness (`allNonempty`). Two structural facts, both machine-checked, sink
the productive-plurality half of the gate:

1. **Every `Approx κ n` is finite** (`approx_finite`): a tower of exponentials `2 ↑↑ n`. (This is a
   *bonus* for WS3 — the Cantor residue realizes as a concrete stage-`(n+1)` element via `toPk`.)
2. **Hereditary non-emptiness forces a unique value** (`allNonempty_unique`): the only hereditarily
   nonempty depth-`n` approximation is `omegaApprox κ n`.

Together: **Ω is the unique productive thread** (`ws1_productive_unique`), so
`ws1_productive_plurality` is FALSE — its negation `ws1_no_productive_plurality` is the theorem. The
design's D2 pre-registered exactly this failure clause ("if the only productive threads turn out
stagewise-equal to `omegaProc` … the gate fails — Impossibility proved for the stagewise encoding,
escalate to C4"). This is the Static Collapse (WS2) reappearing inside every founded approximation:
the un-quotiented process does NOT, by itself, keep atomless plurality — because plurality was never
destroyed by the *quotient* alone but by the finiteness-plus-hereditary-non-emptiness of the founded
stages, which the un-quotiented thread inherits.

**Disposition (no signature retargeted).** `ws1_no_collapse`, `proc_ext`, `ws1_process_exists`,
`ws1_omega_process` are Discharged as designed. The gate is reported **Impossibility proved** for C2,
and the pre-registered carrier-home escalation (**C4 metric completion**, where distinct Cauchy
sequences give genuine atomless plurality, or the guarded/topos-of-trees home) is the fallback, owed
to a future session. The downstream plurality-dependent payoffs (WS4 endogenous arrow, WS5 earned
relativity, WS6 achievement/one-engine) inherit this and are reported Partial/Impossibility with the
obstruction precise — never relabelled. See `charter-status.md` (Closed log, 2026-07-10).
