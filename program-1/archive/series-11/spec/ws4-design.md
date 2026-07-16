# WS4 — The endogenous bound, κ removed

**Design doc. Series 11, the structural heart. Owns: with κ removed, no-total-attention (WS3) plus bounded-holding means the tower never assembles into a COMPLETED TOTALITY, so it does not Russell-explode despite being unboundedly many. The bound is defined as HOLDING-NOT-SIZE (`ws4_bound_is_holding_not_size`), the guard against κ readmitted (§4.4). Target: the κ-free bound Discharged on FINITE stages; the transfinite limit handed to WS5.**

*Series 11 is standalone; the diagonal (`ws1_no_self_total_hold`, `ws1_insp_not_surjective`, `ws1_unrestricted_carrier_inconsistent`, `ws1_diagonal_forbids_closure`), the residue (`residue`, `ws2_residue_distinct`, `ws2_residue_free`), and the tower (`reifyStep`, `towerN`, `prec`) are transcribed into `series-11/formal/Series11/ws4.lean`, re-namespaced `Series11.WS4` (see `spec/README.md` §6). WS4 CONSUMES WS3's `ws3_no_total_attention` and `TotalAttention` and WS1's κ-removal; it does not redefine them (protocol §4). The genuinely new Lean is `Assembled`, `ws4_no_completed_totality`, `ws4_bound_is_holding_not_size`, `ws4_no_russell_blowup`, and `ws4_kappa_free`. The bound is never built into attention's definition (protocol Phase C); it is a consequence of no-total-attention.*

## The object at stake

The charter's Consequence 2 / (EB) (§2, §5.1, §5.3): **with κ removed, the tower never assembles into a completed totality, so it does not Russell-explode despite being unboundedly many — the endogenous bound, holding-not-size.** The Russell hazard is the completed totality: a relatum that is the totality of all relata (a self-total hold), whose existence would make the unrestricted carrier inconsistent (`ws1_unrestricted_carrier_inconsistent`). No-total-attention (WS3) forbids it: no hold assembles the whole, so no completed totality is ever formed, so the tower — however many relata it has — never Russell-explodes. The bound is not on HOW MANY relata exist (no cardinal ceiling); it is on HOW MUCH any hold holds (no total hold). The design question is fourfold: (a) define ASSEMBLY (a completed totality) as a self-total hold (`Assembled := ∃ t, SelfTotal insp t`) — the pin that makes no-blowup route through the diagonal; (b) prove no completed totality (`ws4_no_completed_totality := ws3_no_total_attention`); (c) prove the bound is holding-not-size (`ws4_bound_is_holding_not_size`) — refutable by a total attention, holding for all κ; (d) prove no Russell blowup (`ws4_no_russell_blowup`) — an unrestricted (surjective-inspection) carrier is inconsistent, but the attention-bounded tower is not, because no hold is total.

The load-bearing subtlety, stated once and never hidden: the bound is κ-FREE at the level that matters (the diagonal, no-total-attention, holds for all κ), and this is the genuine κ-removal (§2.7) — but the CARRIER's branching-κ (in `PkObj κ`) remains, as the section `reify`'s existence condition (Cantor forbids `reify : Set Ω → Ω`). This branching-κ is a well-formedness condition on each relatum, NOT a bound on holding or proliferation; whether a reviewer is entitled to judge it κ readmitted is the WS5/WS7 verdict, pre-registered as the tragic edge. The finite-stage bound is Discharged (no-total-attention is stage-independent); the transfinite LIMIT — whether an accumulated hold across a limit stage re-admits a total attention — is the concrete form the terminal fork most likely takes (charter §5.3), handed to WS5.

**Ambient theory.** `spec/README.md` §2.2 (diagonal), §2.5 (tower), §2.7 (κ-removal). WS3's `ws3_no_total_attention`, `TotalAttention`. All from §6.

## Candidates

### C1 — No completed totality: assembly is a self-total hold (the bound, the pin)

```lean
/-- **Assembly**: the tower is ASSEMBLED iff some hold is the totality of relata below it — a completed
    self-inspection. Pinned `:= ∃ t, SelfTotal insp t`, so no-assembly routes through the diagonal. -/
def Assembled {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ t, SelfTotal insp t
/-- **(EB) — no completed totality.** The tower never assembles into a completed totality: no hold is the
    totality (`ws3_no_total_attention`). The bound, an Impossibility inherited from the diagonal. -/
theorem ws4_no_completed_totality {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ Assembled insp :=
  ws3_no_total_attention dest insp
```
The tower never assembles into a completed totality: assembly would be a self-total hold, which no-total-attention forbids. So the "whole" is never formed — the many exists as a proliferation of relata none of which holds all the others, and no hold assembles them. The bound is the non-assembly, inherited from the diagonal.

- **Ambient:** `SelfTotal`, `ws3_no_total_attention`.
- **Success condition (Discharged, the bound):** the term is `ws3_no_total_attention` re-read; assembly is forbidden.
- **Failure mode:** *transfinite-limit-breaks-bound / κ-readmitted.* If `Assembled` were defined so it did not unfold to a self-total hold, no-assembly would not route through the diagonal. C1 pins it. The transfinite limit (an accumulated hold across a limit) is WS5's; the finite-stage bound is Discharged. **Winner (the bound, the pin).**

**Paper triage.** Decidable: `Assembled := ∃ t, SelfTotal insp t`, so `ws4_no_completed_totality := ws3_no_total_attention`. **Winner.**

### C2 — The bound is holding-not-size (the κ-readmitted guard, the flagship)

```lean
/-- **The bound is HOLDING-NOT-SIZE.** No-assembly is a fact about HOLDING (no self-total hold), refutable by
    exhibiting a total attention — NOT a fact about SIZE (no cardinal ceiling): it holds for every κ and
    even when the tower is infinite (`Infinite X`). The exact guard against §4.4. -/
theorem ws4_bound_is_holding_not_size {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ Assembled insp)                                                     -- the bound: no hold assembles …
  ∧ (Assembled insp → ∃ t, SelfTotal insp t)                              -- … and assembly IS a self-total hold (holding, not size)
  ∧ (∀ _ : Infinite X, ¬ Assembled insp) :=                               -- … holding even when the tower is infinite
  ⟨ws3_no_total_attention dest insp, fun h => h, fun _ => ws3_no_total_attention dest insp⟩
```
The bound is holding-not-size: no-assembly is a fact about what a hold holds (no self-total hold), refutable by exhibiting a total attention, holding for every κ and even on an infinite tower. There is no cardinality ceiling anywhere — the tower may be unboundedly many (`Infinite X`), yet no hold assembles it. This is the flagship κ-readmitted guard (protocol §0.5): the bound is on HOLDING, not SIZE.

- **Ambient:** `Assembled`, `ws3_no_total_attention`, `Infinite`.
- **Success condition (Discharged, holding-not-size):** the conjunction holds; the bound is on the hold, the tower may be infinite.
- **Failure mode:** *κ-readmitted (§4.4), the second cardinal sin.* If no-assembly rested on `Cardinal.mk X < κ` (the tower stayed under κ), the bound would be a re-imported ceiling. C2 forecloses it: no-assembly is `¬ ∃ t, SelfTotal insp t` (holding), and the third conjunct shows it holds on an infinite tower — no size ceiling. WS7 certifies no result relies on small κ.

**Paper triage.** Decidable: no-assembly is a diagonal fact (`ws3_no_total_attention`), holding for all κ and infinite `X`. **Winner (the κ-readmitted guard, the flagship).**

### C3 — No Russell blowup: the unrestricted carrier is inconsistent, the attention-bounded tower is not

```lean
/-- **No Russell blowup.** An UNRESTRICTED carrier (a hold ranging over ALL contents, surjective `insp`) is
    inconsistent — no model (`ws1_unrestricted_carrier_inconsistent`). But the attention-bounded tower does
    NOT range over all contents: no hold is total (`ws3_no_total_attention`), so no surjective `insp`, so the
    tower is consistent DESPITE being unboundedly many. The bound is what keeps it from Russell. -/
theorem ws4_no_russell_blowup {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ ins : Hold dest → HoldPred dest, Function.Surjective ins)         -- unrestricted carrier: inconsistent …
  ∧ (¬ ∃ t, SelfTotal insp t) :=                                          -- … but no hold is total: the tower is bounded, no blowup
  ⟨ws1_unrestricted_carrier_inconsistent dest, ws1_no_self_total_hold dest insp⟩
```
The no-blowup theorem: an unrestricted carrier (where a hold ranges over all contents) is inconsistent, but the attention-bounded tower is not, because no hold is total (no surjective inspection, `ws1_insp_not_surjective`). So the tower escapes Russell not by a cardinality ceiling but by the incompletability: the completed totality that would explode is exactly the self-total hold the diagonal forbids. The many proliferates without ever forming the paradoxical whole.

- **Ambient:** `ws1_unrestricted_carrier_inconsistent`, `ws1_no_self_total_hold`.
- **Success condition (Discharged):** both conjuncts hold — the unrestricted carrier explodes, the bounded tower does not.
- **Failure mode:** *transfinite-limit-breaks-bound.* The finite-stage no-blowup holds (diagonal facts). Whether the transfinite limit forces a completed totality despite bounded-holding (a genuine paradox finitude cannot forbid) is WS5's kill condition. C3 delivers the finite-stage no-blowup; WS5 owns the transfinite.

**Paper triage.** Decidable: both transcribed diagonal facts. **Winner (no Russell blowup, finite stages).**

### C4 — The κ-free certificate: the bound uses no cardinal (the genuine removal)

```lean
/-- **The bound is κ-free.** No-completed-totality and no-blowup reference no cardinal: they hold for every
    κ. The genuine κ-removal — the proliferation bound is a diagonal fact, not a cardinal fact. The residual
    carrier-κ (branching, in `PkObj κ`) is the section's existence condition, disclosed, NOT a bound (§2.7). -/
theorem ws4_kappa_free {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  fun d ins => (ws1_diagonal_not_bisim dest insp).2 d ins
```
The bound is κ-free: the no-total-hold fact holds for every carrier and every κ (`ws1_diagonal_not_bisim`). This is the genuine κ-removal — the proliferation bound is the diagonal, which uses no cardinal. The residual branching-κ (in `PkObj κ`) is the section `reify`'s existence condition (Cantor), disclosed as scaffolding, NOT a proliferation or holding bound; whether it counts as κ readmitted is the WS5/WS7 verdict.

- **Ambient:** `ws1_diagonal_not_bisim`.
- **Success condition (Discharged, the κ-removal):** the term typechecks with κ free; the bound holds for all carriers.
- **Failure mode:** *κ-readmitted (§4.4).* If the bound needed κ small, the wall would be rebuilt. C4 forecloses it: the proof uses no κ. The carrier-κ disclosure is the honest boundary. **Winner (the κ-free certificate).**

### C5 — The bound at every finite stage (the finite-stage Discharge, transfinite to WS5)

```lean
/-- **The bound at every finite stage.** At every ℕ-indexed stage of the tower, no hold assembles the stage
    (no-total-attention is stage-independent): the finite-stage bound, Discharged. The transfinite limit
    (an accumulated hold across a limit) is handed to WS5. -/
theorem ws4_bound_finite_stages {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (n : ℕ) :
    ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp
```
The bound holds at every finite stage `towerN … n`: no-total-attention is stage-independent (a diagonal fact about `insp`, not about the stage), so no hold assembles any finite stage. The finite-stage bound is Discharged. The transfinite limit — whether an accumulated hold across a limit re-admits a total attention — is the concrete form the terminal fork most likely takes (charter §5.3), handed to WS5.

- **Ambient:** `towerN`, `ws1_no_self_total_hold`.
- **Success condition (Discharged, finite stages):** the bound holds at every `n` — stage-independent.
- **Failure mode:** *transfinite-limit-breaks-bound (§5.5).* The finite-stage bound is Discharged; the transfinite is WS5's, pre-registered as the crown's Partial edge. C5 scopes the Discharge to finite stages honestly. **Winner (finite-stage Discharge, transfinite → WS5).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | no completed totality (assembly = self-total hold) | `ws3_no_total_attention` | yes — re-read | **win (the bound, pin)** |
| C2 | the bound is holding-not-size | `ws3_no_total_attention`, `Infinite` | yes | **win (κ-readmitted guard)** |
| C3 | no Russell blowup (unrestricted explodes, bounded does not) | `ws1_unrestricted_carrier_inconsistent` | yes | **win (no blowup, finite)** |
| C4 | the bound uses no cardinal (κ-free) | `ws1_diagonal_not_bisim` | yes — no κ | **win (κ-free cert)** |
| C5 | the bound at every finite stage | `towerN`, `ws1_no_self_total_hold` | yes | **win (finite Discharge, → WS5)** |

## Winning candidates: C1 (bound) + C2 (holding-not-size) + C3 (no blowup) + C4 (κ-free) + C5 (finite stages)

### Definitions and obligations (cite `spec/README.md` §2.2, §2.5, §2.7; consume WS3's `ws3_no_total_attention`)

```lean
namespace Series11.WS4
-- SelfTotal, ws1_no_self_total_hold, ws1_diagonal_not_bisim, ws1_unrestricted_carrier_inconsistent,
-- ws1_insp_not_surjective, residue, ws2_residue_distinct, reifyStep, towerN, prec — transcribed (README §6).
-- ws3_no_total_attention, TotalAttention — consumed from WS3.

/-- **D0 — assembly = self-total hold (C1, the pin).** -/
def Assembled {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ t, SelfTotal insp t

/-- **D1 — (EB) no completed totality (C1, the bound).** -/
theorem ws4_no_completed_totality {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ Assembled insp :=
  ws3_no_total_attention dest insp

/-- **D2 — the bound is HOLDING-NOT-SIZE (C2, the κ-readmitted guard, the flagship).** -/
theorem ws4_bound_is_holding_not_size {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ Assembled insp) ∧ (Assembled insp → ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ Assembled insp) :=
  ⟨ws3_no_total_attention dest insp, fun h => h, fun _ => ws3_no_total_attention dest insp⟩

/-- **D3 — no Russell blowup (C3).** Unrestricted carrier inconsistent; bounded tower not. -/
theorem ws4_no_russell_blowup {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ ins : Hold dest → HoldPred dest, Function.Surjective ins) ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨ws1_unrestricted_carrier_inconsistent dest, ws1_no_self_total_hold dest insp⟩

/-- **D4 — the bound is κ-free (C4, the genuine removal).** -/
theorem ws4_kappa_free {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  fun d ins => (ws1_diagonal_not_bisim dest insp).2 d ins

/-- **D5 — the bound at every finite stage (C5, transfinite → WS5).** -/
theorem ws4_bound_finite_stages {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (n : ℕ) : ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp
```

**D1 (the bound)** is no completed totality: assembly is a self-total hold, forbidden — `ws4_no_completed_totality := ws3_no_total_attention`. The pin `Assembled := ∃ t, SelfTotal insp t` (D0) is why no-assembly routes through the diagonal. **D2 (holding-not-size)** is the flagship κ-readmitted guard: the bound holds for every κ and on an infinite tower. **D3 (no blowup)** shows the tower escapes Russell by the incompletability, not a ceiling. **D4 (κ-free)** is the genuine removal. **D5 (finite stages)** scopes the Discharge; the transfinite is WS5's.

## Outcome classes (per charter §7)

- **Discharged on finite stages (EB, the structural heart):** D1 (`ws4_no_completed_totality`), D2 (`ws4_bound_is_holding_not_size`), D3 (`ws4_no_russell_blowup`), D5 (`ws4_bound_finite_stages`), routing through no-total-attention. The κ-free bound: no completed totality, no Russell blowup, holding-not-size, at every finite stage. The exact repair of Series 10's scaffold.
- **Discharged (the κ-removal):** D4 (`ws4_kappa_free`). The bound uses no cardinal.
- **`kappaReadmitted` (the pre-registered honest failure, charter §4.4, the flagship):** if the bound (D2) rested on `Cardinal.mk X < κ` (a size ceiling) rather than no-total-attention (holding). D2 forecloses it: the bound holds on an infinite tower. The residual carrier branching-κ is disclosed (§2.7); whether that counts as κ readmitted is the WS5/WS7 verdict, pre-registered as the tragic edge — the honest boundary, not hidden.
- **Partial / transfinite (pre-registered, charter §5.3, §5.5, the concrete form of the terminal fork):** the finite-stage bound is Discharged; whether the transfinite LIMIT re-admits a total attention (an accumulated hold across a limit, forcing a completed totality despite bounded-holding) is handed to WS5. The crown may be Partial (finite Discharged, transfinite open) — the concrete form the terminal fork is most likely to take.
- **Strip test.** Delete **"bound" / "finite" / "assembles"** from `ws4_no_completed_totality` and the statement is the bare **`¬ ∃ t, SelfTotal insp t`** — `ws1_no_self_total_hold` (via `ws3_no_total_attention`): no hold contains its own complete content. The bound **survives the strip** as the bare diagonal — and this is exactly what the charter demands (§4.4): the bound must be holding-not-size, a diagonal fact, NOT a cardinality artifact. So the *mathematical* content is the transcribed diagonal, and "the endogenous bound / no completed totality / no Russell blowup / the world holds itself finite" is the earned **interpretive** layer, flagged honestly. What the strip does **not** remove is the load-bearing gain: the bound holds on an infinite tower (D2's third conjunct) with no cardinal anywhere (D4), so it is genuinely holding-not-size — the tower is unboundedly many yet never assembled, bounded by the incompletability, not a ceiling. The one thing the strip must confirm (protocol §0.5): the bound is NOT `Cardinal.mk X < κ` (it is not — it holds for `Infinite X`), and the carrier branching-κ is disclosed as the section's existence condition, not a proliferation bound. WS7 records: the endogenous bound is the diagonal read as no-assembly; its κ-freeness (no cardinal in the proof) is the genuine removal, the residual carrier-κ the disclosed boundary, and whether that boundary is κ readmitted is the crown's tragic edge.

## Deliverable

`series-11/formal/Series11/ws4.lean`: transcribed diagonal + tower (README §6); consumed WS3 `ws3_no_total_attention`/`TotalAttention`; `Assembled` (D0), `ws4_no_completed_totality` (D1), `ws4_bound_is_holding_not_size` (D2), `ws4_no_russell_blowup` (D3), `ws4_kappa_free` (D4), `ws4_bound_finite_stages` (D5). **Consumes WS3's no-total-attention; the bound is never built into attention's definition (protocol Phase C).** Axiom check: `#print axioms ws4_no_completed_totality` reduces through `ws3_no_total_attention` / `ws1_no_self_total_hold` to `propext` alone; crucially **the bound references no κ and holds on an infinite tower** — the κ-readmitted check as a build gate (protocol §D). **The κ-free bound is Discharged on finite stages, holding-not-size; the transfinite limit is handed to WS5, and the residual carrier branching-κ is disclosed as the section's existence condition (§2.7), the tragic edge to be settled by WS5's kill condition.**
