# WS6 — Globally atomless and plural, and the one-engine unification

**Design doc. Series 6, the headline workstream. Owns: the achievement the whole series is for — the process over the plain carrier `νPk` exhibited as genuinely globally atomless *and* plural, plurality carried by endogenous time; the one-engine unification (groundlessness and plurality issue from the single diagonal residue, not from a conjunction); no view from nowhere (inhabited, not surveyed); and the transport of the two carrier-independent Series 4 incompletenesses, re-read as the engine.**

*Series 6 is standalone; all Series 4 names used here are transcribed into `series-6/formal/ws6.lean` and re-namespaced `Series6.WS6` (see `spec/README.md` §5). Shared objects — `Proc`, `Productive`, `Δ`, the residue, `faceAt`, `Ω_n`/`omegaProc` — are defined in `spec/README.md` §2–§4 and in WS1/WS3, and only cited here.*

## The object at stake

The charter (§3) proves that no finished object over `νPk` is both genuinely globally atomless and plural: completion is the obstruction. WS1 built the escape — `Proc`, the un-quotiented stagewise process — and stated `ws1_productive_plurality` as a *forward obligation to WS6*. WS3 built the engine — `Δ`, whose successor is the diagonal residue. WS6 is where the two meet and the bill comes due. Four things must be delivered on the same object: (1) **the achievement** — a *concrete* productive plurality over `νPk`, two threads that never merge, distinguished by nothing but their founded history (`ws6_atomless_and_plural`); (2) **the unification** — that groundlessness (no completion ⇒ no atom) and plurality (each residue ⇒ a new distinction) are the *same* residue mechanism, not two facts conjoined (`ws6_one_engine`); (3) **no view from nowhere**, earned from the inhabited/surveyed asymmetry and surviving the anti-laundering strip (`ws6_no_view_from_nowhere`); (4) the **inherited incompleteness** re-read as engine (`ws6_incompleteness_inherited`).

The signature risk is named at the outset (charter §5.5, §5.6, §9): the unification may be a **conjunction** — groundlessness proved one way, plurality another, then `And`-ed. Series 4's WS7 ("one finitude") and Series 5's verdict ("one double-unboundedness") both had to downgrade a claimed reduction to a conjunction. WS6 pre-registers the same pressure and the honest fallback (`payoffsEstablished`), and stakes the whole coincidence on a single shared residue lemma.

**Ambient theory.** `spec/README.md` §2–§4. Carrier `νPk κ` (plain, unlabelled — the honestly atom-free carrier, §2); process `Proc κ` with stagewise identity (§2, WS1); `Productive` (§2) as the liveness form of genuine global atomlessness — *every bud opens*, no imported atom, no label alphabet, no index. The engine `Δ` and the **residue** `d_n` of the non-surjective stage-`n` self-survey (§3, WS3, on the transcribed Cantor diagonal `ws6_lawvere_incomplete`). The endogenous two-sided `faceAt` (§4). Ω as `omegaProc`, the canonical non-terminating orbit (§4, `ws6_omega_nonterminating`).

## Candidates — the unification `ws6_one_engine`

### C1 — Groundlessness and plurality proved separately, then conjoined (the conjunction trap)

```lean
theorem ws6_groundlessness_sep {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (h : Productive x) :
    ∀ n b, IsBud (x.1 n) b → ∃ m, n < m ∧ Opened (x.1 m) b        -- no leaf (from Productive alone)
theorem ws6_plurality_sep {κ} (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y            -- built by any two threads
theorem ws6_one_engine_C1 {κ} (hinf : ℵ₀ ≤ κ) := ⟨ws6_groundlessness_sep, ws6_plurality_sep⟩
```
- **Success condition:** both conjuncts hold — trivially, they do.
- **Failure mode:** **conjunction, not derivation.** Nothing ties the two: groundlessness comes from `Productive`, plurality from an unrelated witness; `Δ` and the residue appear in *neither* essentially. Strip "diagonal" and both survive. This is exactly the reading the coincidence rule (charter §7) forbids to report `Discharged`; it forces **`payoffsEstablished`**. Retained as the **honest pre-registered fallback**, per §5.6.

### C2 — Both derived from one residue lemma (the genuine coincidence) — the lead

```lean
/-- The single engine fact (WS3, on the transcribed Cantor diagonal): at every state
    and stage the self-survey misses a residue `d`, which is (a) NOT in the surveyed
    image — a bud left open — and (b) DIFFERENT from the survey's own prediction. -/
theorem residue_spec {κ} (x : Proc κ) (n : ℕ) :
    let d := residue x n
    (IsBud (x.1 n) d ∧ ¬ Surveyed x n d)                          -- (a) not completed ⇒ opens ⇒ no atom
  ∧ (Δ x |>.1 (n+1) ≠ predicted x n)                              -- (b) residue ≠ self-as-predicted ⇒ new distinction
theorem ws6_one_engine {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (n : ℕ) :
    ∃ d, d = residue x n
       ∧ (¬ Surveyed x n d → NoAtomAt x n)                         -- groundlessness, from THIS d
       ∧ (¬ Surveyed x n d → Branches x (Δ x) n)                   -- plurality, from THIS d
```
- **Success condition:** the *same* `d = residue x n` witnesses both — the non-completion that forbids the atom and the branch that makes the new distinction are one element, one Cantor step.
- **Failure mode:** **the two uses of `d` don't actually share the lemma** — if `NoAtomAt` really only needs `Productive` (not properness of the survey) and `Branches` really only needs two distinct threads (not the residue), then `residue` is decoration on top of C1 and the coincidence launders back to a conjunction. The decidable test (below): both consequents must *consume* `residue_spec` with the residue not eliminable.

### C3 — The achievement witness (consumed by WS1's `ws1_productive_plurality`)

```lean
/-- The concrete productive plurality: Ω's orbit, and the thread that at stage N opens
    the diagonal RESIDUE bud instead of Ω's self-loop bud. They branch at N, never merge. -/
noncomputable def residueThread {κ} (hinf : ℵ₀ ≤ κ) (N : ℕ) : Proc κ
theorem ws6_atomless_and_plural {κ} (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, Productive x ∧ Productive y ∧ x ≠ y
      ∧ (∃ N, x.1 N ≠ y.1 N ∧ ∀ n < N, x.1 n = y.1 n)             -- distinct, differing at a FOUNDED stage N
```
- **Success condition:** `omegaProc` and `residueThread N` are both productive and stagewise-distinct at `N` — distinguished by *diagonal-residue history*, no label, no index.
- **Failure mode:** **spurious plurality.** If `residueThread` is distinct for a reason unrelated to the engine (arbitrary intensional difference), plurality is cheap and the achievement launders — the WS1-D2 "too fine" horn. The residue-branch must be a *productive* thread whose difference from Ω is exactly an opened residue, so the distinguisher is endogenous time.

## Candidates — no view from nowhere `ws6_no_view_from_nowhere`

### NV-A — "The limit does not exist" (the launder)

```lean
theorem ws6_no_view_A {κ} (x : Proc κ) (h : Productive x) :
    ¬ ∃ ω : (νPk κ).X, ∀ n, (surveyAt ω n) = x.1 n                 -- no νPk point completes the thread
```
- **Failure mode:** **laundered.** This is `Proc`'s refusal of the terminal-coalgebra quotient (WS1) relabelled. Strip "inhabited/survey" and it is a bare non-existence-of-limit fact — true, but it carries no inhabited/surveyed *asymmetry*; it is the charter's severe anti-laundering target (§5.5). Reject as the statement; it is what the real theorem must *not* reduce to.

### NV-B — The inhabited/surveyed asymmetry, load-bearing — the lead

```lean
/-- A **survey** is a completed vantage: a map presenting the trajectory as one founded
    object at some depth. The past-map `trunc` (coarsening) is a total, deterministic,
    many-to-one FUNCTION; residue-opening (the future) is one-to-many, NOT a function. -/
theorem ws6_no_view_from_nowhere {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (h : Productive x) :
    (∀ n (σ : Survey x n), ¬ Faithful σ ∧ Missed σ = residue x n)   -- every vantage misses the SAME residue
  ∧ IsFunction (pastMap x) ∧ ¬ IsFunction (futureMap x)            -- lossy-one-way asymmetry is load-bearing
```
- **Success condition:** no depth-`n` survey `σ` is faithful, and *what it misses is the residue* `residue x n` — so no-view factors through the engine, not through mere limit-refusal; and the coarsening/residue asymmetry (`trunc` a function, residue-opening not) is what forbids the completed vantage.
- **Failure mode:** **survey not load-bearing.** If `Faithful σ` fails for a reason independent of the residue (e.g. cardinality, or "depth-`n` can't see depth `n+1`" — a triviality), the strip passes and NV-B collapses to NV-A. The decidable strip: delete `residue`/`faceAt`, and `¬ Faithful` must lose its proof.

## Paper-decidable triage

| Cand. | Target | Decidable-on-paper check | Verdict |
|---|---|---|---|
| C1 | `ws6_one_engine` | both conjuncts trivially hold; residue appears in neither | **fallback** — forces `payoffsEstablished` |
| C2 | `ws6_one_engine` | both consequents consume `residue_spec`; `residue` not eliminable from either | **lead**, conditional on the shared-lemma test |
| C3 | `ws6_atomless_and_plural` | `residueThread N` productive; differs from `omegaProc` at founded `N` by an opened residue | **build** (the WS1 witness) |
| NV-A | `ws6_no_view` | strip "survey" ⇒ bare "no limit" | **reject** (the launder itself) |
| NV-B | `ws6_no_view` | strip `residue`/`faceAt` ⇒ `¬ Faithful` loses its proof | **lead**, conditional on the strip |

## Winning candidates: C2 (shared residue lemma) + C3 (the witness) + NV-B (load-bearing no-view)

The decisive move is to route **all three payoffs through one lemma**, `residue_spec` (WS3): the Cantor residue `d_n` is at once the bud-not-yet-opened (groundlessness), the branch-point (plurality), and the miss of every survey (no-view). If they share `residue_spec` essentially, the unification is a *coincidence theorem*, not a conjunction; if any one detaches, that payoff reports honestly and the unification downgrades.

### Definitions (cite `spec/README.md` §2–§4; WS1, WS3)

```lean
namespace Series6.WS6
-- Proc, Productive, Δ, residue, faceAt, omegaProc, omegaApprox as in README §2–§4 /
-- WS1 / WS3 (transcribed: PkObj, PkMap, νPk, ws6_lawvere_incomplete, ws6_omega_nonterminating,
-- omegaState). No labels Q, by the §3 sharpening.

/-- `x` and `y` first differ at founded stage `N`: a genuine branch in endogenous time. -/
def Branches {κ} (x y : Proc κ) (N : ℕ) : Prop := x.1 N ≠ y.1 N ∧ ∀ n < N, x.1 n = y.1 n

/-- No atom at stage `n`: the state is not a completed self-survey, so a bud remains. -/
def NoAtomAt {κ} (x : Proc κ) (n : ℕ) : Prop := ∃ b, IsBud (x.1 n) b ∧ ¬ Surveyed x n b
```

### The obligations, each with strategy, paper-decidability, and coincidence/strip annotation

**A1 — `ws6_incompleteness_inherited`: the two Series 4 results transported and re-read as engine.**
```lean
theorem ws6_incompleteness_inherited {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) :
    (∀ n, ¬ Surjective (selfSurvey x n))                          -- Cantor/Lawvere, transported
  ∧ (Productive (omegaProc κ hinf)
      ∧ ∀ n, ∃ b, IsBud (omegaApprox κ hinf n) b)                 -- Ω complete-in-extent, closed-at-no-depth
```
*Strategy:* first conjunct is `ws6_lawvere_incomplete` applied to the stage-`n` survey (transcribed, carrier-independent); second is `ws6_omega_nonterminating` re-expressed as `omegaProc` productivity + a bud at every depth. The *re-reading* is that `residue x n := ` the witness of non-surjectivity — so this theorem is where the walls become the source term. *Paper-decidable:* yes — both are transcribed facts re-typed on `Proc`. *Coincidence note:* this supplies `residue`; it is the hinge every later theorem consumes.

**A2 — `ws6_groundlessness_from_diagonal`: no completion ⇒ no atom.**
```lean
theorem ws6_groundlessness_from_diagonal {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (n : ℕ) :
    ¬ Surveyed x n (residue x n) → NoAtomAt x n
```
*Strategy:* the residue `d_n` is a bud (in the state, un-opened at `n`) that the survey did not reach; an atom would be a bud surveyed-and-closed forever, i.e. a completed self-survey — which `residue_spec`(a) forbids. So `NoAtomAt` is `⟨residue x n, ...⟩`. *Paper-decidable:* yes, one application of `residue_spec`. *Strip:* delete "diagonal/residue" and the antecedent is contentless — the theorem needs the *specific* missed element, not `Productive` in the abstract. This is what distinguishes it from C1's `ws6_groundlessness_sep`.

**A3 — `ws6_plurality_from_diagonal`: each residue ⇒ a new distinction.**
```lean
theorem ws6_plurality_from_diagonal {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (n : ℕ) :
    Branches x (openResidue x n) (n+1)                            -- opening d_n branches at n+1
      ∧ Productive (openResidue x n)
```
*Strategy:* `openResidue x n` agrees with `x` below `n+1` and opens `d_n` at `n+1`; because `d_n ≠ predicted x n` (`residue_spec`(b)) the two differ exactly at `n+1` — the diagonal manufactures a thing differing from itself-as-predicted. Productivity of the branch from WS3's productivity of `Δ`-orbits. *Paper-decidable:* yes. *Strip:* delete "residue" and `Branches` has no witness — plurality here is *made by* the diagonal, not two arbitrary threads.

**A4 — `ws6_one_engine`: the coincidence (same residue, both fruits).** *(signature crux.)*
```lean
theorem ws6_one_engine {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (n : ℕ) :
    ∃ d, d = residue x n
       ∧ (¬ Surveyed x n d → NoAtomAt x n)                        -- A2, from THIS d
       ∧ Branches x (openResidue x n) (n+1)                       -- A3, from THIS d
```
*Strategy:* exhibit the single `d = residue x n` and discharge both consequents by A2/A3, whose proofs *both* consume `residue_spec` on the same `d`. The theorem's content is not the conjunction of A2 and A3 but that **one element** discharges both — groundlessness and plurality are two readings of one Cantor step. *Paper-decidable:* the shared-lemma test — inspect that neither consequent's proof term can be rebuilt without `residue_spec d`. *Coincidence note (the whole risk):* if inspection shows A2 secretly only needs `Productive` or A3 only needs "two threads", the shared `d` is cosmetic and this **downgrades to C1** — report `ws6_one_engine` **Partial — definitional-only**, forced form (a substantive independent characterization of "same mechanism") named open, verdict `payoffsEstablished`. This is pre-registered, not a surprise.

**A5 — `ws6_atomless_and_plural`: THE achievement.**
```lean
theorem ws6_atomless_and_plural {κ} (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, Productive x ∧ Productive y
      ∧ (∃ N, Branches x y N)                                     -- distinct at a founded stage
      ∧ (∀ z ∈ ({x, y} : Set (Proc κ)), ∀ n b, IsBud (z.1 n) b → ∃ m, n < m ∧ Opened (z.1 m) b)
```
*Strategy:* `x := omegaProc`, `y := residueThread N` (= `openResidue omegaProc N`); both productive (A3 + WS1-D3 `ws1_omega_process`); `Branches x y N` from A3; the last conjunct is `Productive` for both, unfolded. The distinguisher is the **founded history**, endogenously generated by `Δ` — no label alphabet, no index, no weight. This *is* the witness `ws1_productive_plurality` consumes (WS1-D2). *Paper-decidable:* yes — assembled from A3 and `ws1_omega_process`. *Strip:* delete endogenous time (the founded history) and `x`, `y` have nothing to differ by — over `νPk` the static collapse (`ws2_collapse`) fires. The theorem *needs* the process; that is the point of the whole series.

**A6 — `ws6_no_view_from_nowhere`: inhabited, not surveyed.**
```lean
theorem ws6_no_view_from_nowhere {κ} (hinf : ℵ₀ ≤ κ) (x : Proc κ) (h : Productive x) :
    (∀ n (σ : Survey x n), ¬ Faithful σ ∧ Missed σ = residue x n)
  ∧ IsFunction (pastMap x) ∧ ¬ IsFunction (futureMap x)
```
*Strategy:* any completed vantage `σ` at depth `n` is a survey, hence non-surjective by A1, and *what it misses is `residue x n`* — so no-view is the engine's residue, not limit-refusal. `pastMap := trunc` is a total many-to-one function; `futureMap` (residue-opening) is one-to-many (A3 gives ≥2 continuations from one state), so not a function. *Paper-decidable:* yes — A1 for non-faithfulness, `trunc` totality for the past-map, A3 for the future-map's multivaluedness. *Strip (severe, charter §5.5):* delete `residue`/`faceAt` and `¬ Faithful` loses its proof — the residue is what the survey misses, so the inhabited/surveyed asymmetry is load-bearing and the theorem does **not** reduce to NV-A ("no limit"). If, on inspection, `¬ Faithful` survives the strip (misses for a depth/cardinality reason), report **Partial — laundered**, no-view demoted to NV-A.

## Outcome classes (per charter §7)

- **Discharged:** A1 (transported), A2, A3, A5 (the achievement — the WS1 witness delivered), A6 with a surviving strip.
- **Discharged with coincidence theorem (the headline):** A4 `ws6_one_engine` *iff* the shared-lemma test passes — both consequents provably consume `residue_spec` on one `d`. Verdict `oneDiagonal` (routed to WS7).
- **Partial — definitional-only (pre-registered, the signature fallback):** if the shared-lemma test fails, A4 downgrades — groundlessness and plurality proved (A2, A3) but their unification is C1's conjunction; verdict **`payoffsEstablished`**, the forced "same-mechanism" form named open. Expected pressure, per Series 4/5.
- **Partial — laundered:** if A6's strip fails, no-view demotes to the "no limit" fact (NV-A), flagged honestly.
- **Trivialized risk:** if A2/A3 turn out not to need `Δ` at all (the residue eliminable everywhere), the engine is painted on and WS6 hands WS7 a **Trivialized** input — a sharp negative that is itself a program success.

## Deliverable

`series-6/formal/ws6.lean`: transcribed `ws6_lawvere_incomplete`, `ws6_omega_nonterminating`, `omegaState`, `ws2_collapse` (self-contained); `Branches`, `NoAtomAt`, `Survey`/`Faithful`/`Missed`, `pastMap`/`futureMap`, `openResidue`, `residueThread`, `residue`/`residue_spec` (consumed from WS3); `ws6_incompleteness_inherited` (A1), `ws6_groundlessness_from_diagonal` (A2), `ws6_plurality_from_diagonal` (A3), `ws6_one_engine` (A4), `ws6_atomless_and_plural` (A5, exported as the `ws1_productive_plurality` witness), `ws6_no_view_from_nowhere` (A6). Axiom check: `#print axioms ws6_atomless_and_plural` should reduce through `residue_spec` and `ws1_omega_process` to the standard three (`propext, Classical.choice, Quot.sound`); `#print axioms ws6_one_engine` must show the *same* `residue_spec` dependency in both consequents — the machine-checkable form of the coincidence.
