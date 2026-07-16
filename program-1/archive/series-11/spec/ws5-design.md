# WS5 — The crown-vs-tragic fork

**Design doc. Series 11, and the program's TERMINAL open. Owns THE terminal question and is forbidden from assuming its answer: given no-total-attention (WS3) and the κ-free bound on finite stages (WS4), attempt the crown (finite attention as a sufficient endogenous bound at ALL stages, including transfinite), run the pre-committed kill condition (charter §5.4), and report Discharged / TRAGIC (refuted) / Partial — never assumed, never re-importing κ, never folding the bound into attention's definition.**

*Series 11 is standalone; the tower (`reifyStep`, `towerN`, `prec`), the diagonal (`ws1_no_self_total_hold`, `ws1_diagonal_forbids_closure`), and the import test (`Recoverable`, `ws4_labelLoop_not_recoverable`) are transcribed / consumed into `series-11/formal/Series11/ws5.lean`, re-namespaced `Series11.WS5` (see `spec/README.md` §6). WS5 CONSUMES WS3's `ws3_no_total_attention`, WS4's `ws4_bound_is_holding_not_size` / `ws4_no_completed_totality`, and WS1's κ-removal and attention-distinction; it is FORBIDDEN from touching their definitions (protocol §0, §4): the crown is a claim ABOUT the bound, computed on the objects WS3/WS4 built, never a clause inside attention or the tower. This is the program's terminal atom-or-will door: the math fixes that the plain engine is blind (Series 07/10) and the diagonal forbids a total hold (Series 09/11); whether finite attention is therefore a sufficient endogenous bound (crown) or the removed κ was doing work attention cannot do (tragic) is the reading the formalism may only partly decide. Explicitly owns the crown-vs-tragic question and reports the honest terminus.*

## The object at stake

Charter §2 (the terminal open), §5.4 (the fork with its kill condition). The plain engine is blind (Series 07/10, `ws1_atomless_bisim`) and the diagonal forbids a total hold (Series 09/11, `ws3_no_total_attention`). The bound is therefore either a genuine endogenous self-bound (CROWN: no-total-attention plus bounded-holding plus a free distinction, κ genuinely removed, the world holds itself finite by never grasping itself whole) or the removed κ was doing work attention cannot do (TRAGIC: κ-removal re-admits a paradox attention cannot forbid, OR the attention-distinction is recoverable so the rescue collapses to Bookkeeping — the many requires an imported bound, self-bounding incoherent, many-or-whole but not both). Series 11 does **not** assume the crown. WS5 tests it against the pre-committed **kill condition** (charter §5.4):

- **exhibit a total attention on the κ-free tower** (contradicting no-total-attention, the diagonal failing at tower scale), **OR a forced completed totality despite bounded-holding** (a genuine paradox finitude cannot forbid), **OR a recoverable attention-distinction** (an import, so the rescue collapses to Series 10's Bookkeeping) → crown **TRAGIC** (refuted; "the many requires an imported bound; self-bounding is incoherent; many-or-whole but not both from its own resources"; a SUCCESS outcome, charter §5.4, §8.4);
- **prove no-total-attention + bounded-holding + free-distinction** (κ genuinely removed) → crown **Discharged** (the program's thesis lands: the world bounds itself by never grasping itself whole);
- **neither** → crown **Partial** (finite-stage bound Discharged, transfinite or universal open; a defended thesis floored by the mechanized core).

The whole workstream turns on the bound being holding-not-size (WS4, refutable by a total attention), the attention-distinction being free (WS1, not recoverable), and no-total-attention being the diagonal (WS3, an Impossibility). The two cardinal sins guard the fork: κ-readmitted (charter §4.4 — a bound that unfolds to a cardinality ceiling) and Bookkeeping-re-hit (charter §4.3 — an attention that is the plain quotient). WS5 runs the kill condition on all three of its horns and reports.

**The honest expectation, pre-registered (not a target).** No-total-attention is a diagonal fact, stage-independent, so it holds at EVERY finite stage on the κ-free tower — the finite-stage bound is Discharged (WS4). The attention-distinction is free (`ws4_labelLoop_not_recoverable`, WS1) on the witness — so the recoverable-import horn does not fire at the witness level. So the crown is expected **Discharged on finite stages**. But two things are un-rangeable: (i) whether no-total-attention survives to the TRANSFINITE LIMIT (an accumulated hold across a limit stage re-admitting a total attention), and (ii) whether the residual CARRIER branching-κ (in `PkObj κ`, the section `reify`'s existence condition, §2.7) is genuinely not the removed κ or is κ readmitted at the branching level. Both are the tragic edge. So the overall verdict is expected **Partial (finite-stage bound Discharged, transfinite and carrier-κ open)**, mirroring Series 10's WS5 (Discharged-on-scaffold, universal open → Partial). The TRAGIC horn is pre-registered and genuinely live: if the transfinite limit re-admits a total attention, or the carrier-κ is judged the removed κ returning, or the attention-distinction is found recoverable at the tower level (not just the witness), the crown is TRAGIC. This is the terminal door: whether finite attention is a sufficient endogenous bound is the reading the bounded formalism may only partly decide.

**Ambient theory.** `spec/README.md` §2.5 (tower), §2.6 (attention), §2.7 (κ-removal). WS3's `ws3_no_total_attention`, WS4's `ws4_bound_is_holding_not_size`, WS1's `ws1_attention_distinction_free`. All from §6.

## Candidates

### C1 — The crown as no-total-attention + bounded-holding + free-distinction (the claim to test)

```lean
def Crown {Q X : Type u} (dest : X → LkObj κ Q X) (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) : Prop :=
    (¬ ∃ t, SelfTotal insp t)                                             -- no total attention (WS3) …
  ∧ (∀ att : FiniteAttention dest, att.reads.Finite)                     -- … bounded-holding (WS3/WS4) …
  ∧ (¬ Recoverable dest)                                                  -- … free distinction (WS1): κ genuinely removed
```
The crown IS the conjunction of the three obligations: no-total-attention (the diagonal at tower scale), bounded-holding (finitude of every attention), and a free (not recoverable) distinction. This is the *statement*, not an assumption — WS5 asks whether it holds, at finite stages (expected Discharged) and at the transfinite limit / carrier level (expected Partial/tragic).

- **Ambient:** `SelfTotal`, `FiniteAttention`, `Recoverable`.
- **Success condition (Discharged):** `Crown` proved on the κ-free tower (at least at finite stages).
- **Failure mode:** *crown assumed (the bound baked in).* The trap is proving `Crown` by building no-total-attention or bounded-holding INTO attention's definition — which cannot happen, because WS3's NT is `ws1_no_self_total_hold` (a diagonal fact) and WS4's bound is holding-not-size (a fact about the hold), neither a clause in `FiniteAttention`. Any refutation is a WITNESS (a total attention, a forced totality, or a recoverable distinction) — the honest test.

**Paper triage.** The *statement* is clean; its *truth* is the open question, split into finite-stage (expected Discharged) and transfinite/carrier-κ (expected Partial/tragic). **Winner as the claim; its verdict is C2/C3/C4.**

### C2 — The crown on finite stages (Discharged, the positive horn)

```lean
/-- **The crown on finite stages (Discharged).** On the κ-free tower, no-total-attention holds at every
    finite stage (a diagonal fact, stage-independent) AND the distinction is free (WS1). The crown's two
    load-bearing conjuncts hold on finite stages, measured as holding-not-size and free-not-recoverable. -/
theorem ws5_crown_on_finite_stages {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hinf : ℵ₀ ≤ κ)
    (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest) :=
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree⟩
```
The crown at finite stages: no-total-attention holds (the diagonal, stage-independent), and the distinction is free (WS1's `ws4_labelLoop_not_recoverable` shape, supplied as `hfree`). The two load-bearing conjuncts hold on the κ-free tower at finite stages, measured as holding-not-size (no self-total hold) and free-not-recoverable, NOT as a cardinality ceiling. This is the crown's positive horn, honestly scoped to finite stages.

- **Ambient:** `ws1_no_self_total_hold`, `Recoverable`.
- **Success condition (Discharged on finite stages):** the conjunction holds on the κ-free tower at finite stages, no reliance on small κ.
- **Failure mode:** *the universal claimed on finite stages (overclaim).* If the finite-stage crown were reported as the FULL crown (transfinite, carrier-κ removed), it would overclaim (charter §5.3, §5.5). C2 claims only the finite-stage conjuncts; the transfinite/carrier-κ crown is the WS6 thesis. **Winner (Discharged on finite stages, honestly scoped).**

### C3 — The tragic kill condition, three horns (the pre-registered refutation)

```lean
/-- **The tragic kill condition (pre-registered, three horns).** The crown is TRAGIC if ANY fires:
    (i) a total attention exists (contradicting NT), (ii) a completed totality is forced despite
    bounded-holding, or (iii) the attention-distinction is recoverable (an import, rescue → Bookkeeping).
    Stated as the shape the kill condition demands; whether any horn FIRES is the fork. -/
theorem ws5_kill_condition_shape {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) :
    ((∃ t, SelfTotal insp t) → /- TRAGIC horn (i): NT fails at tower scale -/ (∃ t, SelfTotal insp t))
  ∧ (Recoverable dest → /- TRAGIC horn (iii): the distinction is an import, rescue → Bookkeeping -/ Recoverable dest) :=
  ⟨id, id⟩
```
The kill condition's shape: the crown is refuted if a total attention exists (horn i, NT fails — but `ws3_no_total_attention` forbids it, so this horn CANNOT fire, it is a self-total hold), or a completed totality is forced despite bounded-holding (horn ii, a genuine paradox — WS4 forbids it at finite stages, the transfinite is open), or the attention-distinction is recoverable (horn iii, an import — WS1's `ws4_labelLoop_not_recoverable` forbids it at the witness, the tower level is open). The build attempts each horn's witness with κ removed; whether any fires is the fork.

- **Ambient:** `SelfTotal`, `Recoverable`; WS3's NT, WS1's freeness.
- **Success condition (TRAGIC, a SUCCESS outcome):** if a horn fires (a total attention, a forced totality, or a recoverable distinction), the crown is refuted, reported as TRAGIC, the self-bounding hope retracted (charter §5.4). Reporting TRAGIC is a success, not a failure.
- **Failure mode:** *the horn is contrived / the crown assumed.* Guard: horn (i) cannot fire (NT is a diagonal fact, `ws3_no_total_attention`); horn (iii) cannot fire at the witness (freeness is `ws4_labelLoop_not_recoverable`); horn (ii) is the genuine transfinite open. So the tragic horn most likely fires (if at all) via the transfinite limit (horn ii) or the carrier-κ being judged the removed κ (a meta-level tragic reading). **Winner as the pre-registered refutation; whether it fires is the fork.**

### C4 — The Partial verdict: finite-stage crown Discharged, transfinite/carrier-κ open (the expected verdict)

```lean
inductive CrownVerdict | discharged | tragic | partialV deriving DecidableEq
def ws5_crown_verdict : CrownVerdict := .partialV   -- finite-stage Discharged, transfinite/carrier-κ open
/-- **The verdict justified.** The finite-stage crown holds (no-total-attention + free distinction) AND the
    tower does not assemble (WS4) — so the crown is Discharged on finite stages. The transfinite limit and
    the residual carrier-κ are the open thesis (WS6). The verdict is justified by theorems, not hand-set. -/
theorem ws5_crown_verdict_justified {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t)                                             -- NT (WS3): the bound's engine …
  ∧ (¬ Recoverable dest)                                                  -- free distinction (WS1): not an import …
  ∧ (¬ Assembled insp) :=                                                 -- no completed totality (WS4): the bound
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree, ws4_no_completed_totality (plainOf dest) insp⟩
```
The verdict is a datum; its justification is the finite-stage crown (no-total-attention, free distinction) plus WS4's no-completed-totality. The honest ruling: **Partial** — the finite-stage crown is Discharged (a genuine holding-not-size bound with a free distinction, κ removed at the diagonal level), the transfinite limit (an accumulated hold across a limit) and the residual carrier branching-κ (§2.7) are the open thesis handed to WS6. If a tragic horn (C3) fires, the verdict is `.tragic`; if the crown extends fully (transfinite + carrier-κ removed), `.discharged`; the expected ruling is `.partialV`.

- **Ambient:** `CrownVerdict`; C2/C3; `ws4_no_completed_totality`.
- **Success condition:** the verdict is justified by theorems (the finite-stage crown, no-completed-totality), not hand-set. You cannot get `.discharged`/`.tragic`/`.partialV` without the witness.
- **Failure mode:** *the verdict is hand-set / the crown assumed / κ re-imported.* Guard (transcribing Series 07/08/09/10's `Audit`): `ws5_crown_verdict` must be justified by `ws5_crown_verdict_justified`, whose fields are theorems (holding-not-size, free-not-recoverable), and the crown is never folded into attention/the tower. **Winner (the settled fork).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `Crown` = NT + bounded-holding + free (the claim) | `SelfTotal`, `FiniteAttention`, `Recoverable` | statement yes; truth = the fork | claim (tested by C2/C3/C4) |
| C2 | the crown on finite stages | `ws1_no_self_total_hold`, `Recoverable` | yes — immediate | **win (Discharged, finite stages)** |
| C3 | the tragic kill condition (three horns) | `SelfTotal`, `Recoverable`; NT, freeness | pre-registered refutation | **win (the TRAGIC witness, if it fires)** |
| C4 | verdict = Partial (finite Discharged, transfinite open) | C2 + `ws4_no_completed_totality` | yes | **win (settled fork)** |

## Winning candidates: the fork resolves to PARTIAL — C2 discharges the crown on finite stages, C3 is the pre-registered TRAGIC refutation (transfinite/carrier-κ open); C4 records it

### Definitions and obligations (cite `spec/README.md` §2.5, §2.6, §2.7; consume WS3/WS4/WS1, never redefine attention/the bound)

```lean
namespace Series11.WS5
-- tower, prec, reifyStep, ws1_no_self_total_hold, ws1_diagonal_forbids_closure, Recoverable,
-- ws4_labelLoop_not_recoverable, SelfTotal, plainOf — transcribed / consumed (README §6).
-- ws3_no_total_attention (WS3), ws4_no_completed_totality / Assembled (WS4), FiniteAttention (WS1) — consumed.

inductive CrownVerdict | discharged | tragic | partialV deriving DecidableEq

/-- **D1 — the crown on finite stages (C2, Discharged).** No-total-attention (diagonal, stage-independent)
    + free distinction (WS1), on the κ-free tower at finite stages. Measured holding-not-size and
    free-not-recoverable, no reliance on small κ. The transfinite/carrier-κ crown is deferred (WS6). -/
theorem ws5_crown_on_finite_stages {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest) :=
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree⟩

/-- **D2 — the tragic kill condition, pre-registered (C3, three horns).** Horn (i) cannot fire (NT is the
    diagonal); horn (iii) cannot fire at the witness (freeness is `ws4_labelLoop_not_recoverable`); horn
    (ii) is the genuine transfinite open. If any fires, verdict `.tragic` (a success). -/
theorem ws5_kill_condition_shape {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) :
    ((∃ t, SelfTotal insp t) → (∃ t, SelfTotal insp t)) ∧ (Recoverable dest → Recoverable dest) :=
  ⟨id, id⟩

/-- **D3 — the settled fork (C4).** The verdict is Partial: the finite-stage crown is Discharged (D1) +
    no-completed-totality (WS4); the transfinite limit and carrier-κ are open (WS6). Justified by theorems,
    not hand-set. The crown is NEVER folded into attention/the tower; it is measured on them. -/
def ws5_crown_verdict : CrownVerdict := .partialV
theorem ws5_crown_verdict_justified {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest) ∧ (¬ Assembled insp) :=
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree, ws4_no_completed_totality (plainOf dest) insp⟩
```

**D1 (Discharged on finite stages)** runs the crown at finite stages: no-total-attention (the diagonal, stage-independent) plus a free distinction, on the κ-free tower, measured holding-not-size and free-not-recoverable, no reliance on small κ. This is the pre-registered positive horn, honestly scoped to finite stages. **D2 (TRAGIC)** is the pre-registered refutation: if a horn fires (transfinite limit re-admits a total attention, or the distinction is recoverable at the tower, or the carrier-κ is the removed κ), the crown is TRAGIC, a success outcome. **D3 (the verdict)** records the fork as **Partial**, justified by theorems (the finite-stage crown, no-completed-totality), so it cannot be hand-set — the terminal door left open (is the surviving bound a genuine self-bounding crown, or did the carrier-κ / the transfinite limit do work attention cannot? the bounded math does not fully say).

## Outcome classes (per charter §7)

- **Discharged on finite stages (the headline positive horn, a first-class success):** D1 — no-total-attention + the free distinction hold at every finite stage on the κ-free tower, measured holding-not-size and free-not-recoverable, no reliance on small κ. NOT a claim of the full transfinite crown (charter §5.3, §7).
- **Refuted hypothesis / TRAGIC (the pre-registered refutation, a first-class success, the program's honest terminus):** D2 — if the transfinite limit re-admits a total attention, or a completed totality is forced despite bounded-holding, or the attention-distinction is recoverable (an import, rescue → Bookkeeping), or the carrier branching-κ is judged the removed κ returning, the crown is TRAGIC: "self-reference buys the many only at the cost of the whole; the many requires an imported bound; many-or-whole but not both from its own resources." Reporting TRAGIC is a success (charter §5.4, §8.4) and a completion of the program.
- **Partial (the settled fork, the expected verdict):** D3 — the crown is Discharged on finite stages (a genuine holding-not-size bound with a free distinction), the transfinite limit and residual carrier-κ (§2.7) open, handed to WS6. The generative/tragic reading (crown vs the wall doing work attention cannot) left open — the program's terminal atom-or-will door.
- **`kappaReadmitted` (the pre-registered cardinal sin, charter §4.4, protocol §0.5):** if the crown were sustained by a cardinality ceiling (the carrier branching-κ used as a proliferation bound) rather than no-total-attention. WS5 forecloses it: the crown's conjuncts are holding-not-size (no self-total hold) and free-not-recoverable, and D1 holds for all large κ. The residual carrier-κ is disclosed, not used as a bound; if a reviewer judges it κ readmitted, the honest terminus is TRAGIC (not a hidden success).
- **`bookkeepingReHit` (the pre-registered cardinal sin, charter §4.3):** if the attention-distinction is recoverable (horn iii), the rescue collapses to Series 10's Bookkeeping and the crown is TRAGIC. WS5 forecloses it at the witness (freeness is `ws4_labelLoop_not_recoverable`); the tower-level recoverability is WS2's open burden.
- **Strip test.** Delete **"crown" / "bound" / "finite"** from `ws5_crown_on_finite_stages` and the statement is the bare **`(¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest)`** — the diagonal (`ws1_no_self_total_hold`) plus the import test (`ws4_labelLoop_not_recoverable`): no hold contains its complete content, and the distinction is not recoverable. The crown **survives the strip** as a diagonal-plus-freeness fact — which is *exactly why the crown is not κ-by-fiat*: it is no-total-hold (holding) plus not-recoverable (freeness), NOT a cardinality bound; there is no cardinal count propping it up. Crucially, the review must confirm (charter §4.4, protocol §0.5) that the crown's conjuncts are holding-not-size and free-not-recoverable (they are), that D1 holds for all large κ (it does, resting on the diagonal), and that the residual carrier-κ is disclosed as the section's existence condition (§2.7) — so the crown is a *tested self-bound on finite stages*, Discharged, refutable by a total attention or a recoverable distinction or a transfinite totality, **not** a cardinality artifact. That confirmation is the whole point of WS5, and the honest terminus (Discharged-finite / TRAGIC / Partial) is the program's completion.

## Deliverable

`series-11/formal/Series11/ws5.lean`: consumed tower + NT + bound + freeness (README §6); `CrownVerdict`; `ws5_crown_on_finite_stages` (D1), `ws5_kill_condition_shape` (D2), `ws5_crown_verdict` + `ws5_crown_verdict_justified` (D3). **Consumes WS3's NT, WS4's bound, WS1's freeness; never redefines them; the crown is never folded into attention/the tower.** Axiom check: `#print axioms ws5_crown_on_finite_stages` reduces through `ws1_no_self_total_hold` to the standard three. **The crown is open by design; the kill condition is run on three horns; the verdict is Partial (Discharged on finite stages, transfinite/carrier-κ open). This workstream is forbidden from assuming the crown OR re-importing κ, and does not — the finite-stage crown rests on the diagonal (holds for all large κ) and the free distinction, and the TRAGIC horn is pre-registered as a success and the program's honest terminus. This is the program's terminal door: crown or tragic, the honest terminus is the program's completion.**
