# WS3 — No total attention (the bound's engine)

**Design doc. Series 11, the diagonal at tower scale, the bound's engine, and the cleanest result of the series. Owns: `(NT)` no finite attention holds the whole tower — a total attention is a self-total hold at tower scale, forbidden by the diagonal `ws1_no_self_total_hold`, an Impossibility; `(NL)` attention reads full relata, never leaves (`SHNE` preserved, `ws3_reify_preserves_SHNE`); and bounded-holding derived ENDOGENOUSLY (finitude of the reading), the guard against κ-readmitted (§4.4). The bound (EB) and the crown are NOT attempted here — WS4/WS5's.**

*Series 11 is standalone; the diagonal spine (`Hold`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `ws1_diagonal_not_bisim`, `ws1_insp_not_surjective`, `ws1_unrestricted_carrier_inconsistent`), the reification tower and (NL) preservation (`reifyStep`, `towerN`, `ws3_reify_preserves_SHNE`), and `SHNE` are transcribed into `series-11/formal/Series11/ws3.lean`, re-namespaced `Series11.WS3` (see `spec/README.md` §6). WS3 CONSUMES WS1's `FiniteAttention` and defines `TotalAttention` on it. The genuinely new Lean is `TotalAttention`, `ws3_no_total_attention`, `ws3_attention_reads_full_relata`, `ws3_bounded_holding_endogenous`, and `ws3_no_total_attention_kappa_free`. This is the first Lean file of the series in spirit (charter §6, protocol Phase C): build attention and no-total-attention early as the seed the bound runs on.*

## The object at stake

The charter's (NT) (§2 Consequence 2, §3): **no finite attention holds the whole tower — a total attention is a self-total hold at tower scale, which the diagonal forbids.** This is the bound's engine: what prevents the completed totality is not a cardinality ceiling but the incompletability, distributed across the tower. A "total attention" is a hold whose reading is the totality of contents below it — the completed self-inspection — which is exactly `SelfTotal insp t`, forbidden by `ws1_no_self_total_hold`. So no-total-attention is the diagonal, re-read at the scale of attention on the tower, an Impossibility. The design question is threefold: (a) define TOTAL attention as a self-total hold (`TotalAttention := SelfTotal`) — the pin that makes NT route through the diagonal, not a definitional clause; (b) prove (NL) attention reads full relata, never a leaf (`ws3_reify_preserves_SHNE`, the constraint since Series 07); (c) derive bounded-holding ENDOGENOUSLY from finitude, refutable by exhibiting a total attention or an unbounded hold, never a cardinality assumption (§4.4).

The load-bearing subtlety, stated once and never hidden: no-total-attention is κ-FREE by construction, and this is the genuine κ-removal (§2.7). `ws1_no_self_total_hold`'s proof references only `insp` and propositional logic (`insp t t ↔ ¬ insp t t`); it holds for every `dest`, every `insp`, every κ, never touching the cardinality bound. So the bound the tower imposes on itself is a diagonal fact, not a cardinal fact — the incompletability that generates the many (Series 09) is the same incompletability that forbids the total hold (Series 11). The bound is on HOLDING (no self-total hold), not on SIZE (no cardinal ceiling), refutable by exhibiting a total attention.

**Ambient theory.** `spec/README.md` §2.2 (diagonal layer), §2.5 (tower, NL), §2.6 (finite attention). All from §6.

## Candidates

### C1 — No total attention: a total attention is a self-total hold (the Impossibility, the pin)

```lean
/-- A **total attention**: a hold whose reading is the totality of contents below it — the completed
    self-inspection. Its existence IS a self-total hold at tower scale. Pinned `:= SelfTotal`, so NT routes
    through the diagonal, not a definitional clause. -/
def TotalAttention {X : Type u} {dest : X → PkObj κ X}
    (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop := SelfTotal insp t
/-- **(NT) — THE IMPOSSIBILITY.** No finite attention holds the whole tower: a total attention is a
    self-total hold, forbidden by the diagonal. The bound's engine, an Impossibility. -/
theorem ws3_no_total_attention {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, TotalAttention insp t :=
  ws1_no_self_total_hold dest insp
```
A total attention — a hold that reads the whole tower, i.e. whose content is the completed self-inspection — is by definition a self-total hold. The diagonal forbids it. So no finite (indeed no) attention holds the whole tower; the tower is never assembled by any hold. This is `ws1_no_self_total_hold` re-read at attention scale, an Impossibility.

- **Ambient:** `SelfTotal`, `ws1_no_self_total_hold`.
- **Success condition (Impossibility proved):** the term is `ws1_no_self_total_hold` re-read; NT is the diagonal at tower scale.
- **Failure mode:** *total-hold (§4.5), the smuggle.* If `TotalAttention` were defined so it did NOT unfold to `SelfTotal` (a total attention that is not a self-total hold), NT would not route through the diagonal and a total attention could be admitted — the diagonal violated, attention mis-defined (`totalAttentionSmuggled`). C1 pins `TotalAttention := SelfTotal`, so a total attention IS a self-total hold and NT IS the diagonal. Any exhibited total attention is then a proof attention was mis-defined, a design defect.

**Paper triage.** Decidable: `TotalAttention := SelfTotal`, so `ws3_no_total_attention := ws1_no_self_total_hold`. **Winner (the Impossibility, the bound's engine).**

### C2 — No total attention is κ-free (the genuine κ-removal, §2.7)

```lean
/-- **NT is κ-free.** The diagonal references no cardinal: NT holds for every `κ`, every `dest`, every
    `insp` — the genuine κ-removal. The bound is a diagonal fact, holding-not-size, refutable by a total
    attention, NOT a cardinality ceiling. And it is independent of relational identity. -/
theorem ws3_no_total_attention_kappa_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ws1_diagonal_not_bisim dest insp
```
No-total-attention holds with no cardinality assumption and independently of relational identity (`ws1_diagonal_not_bisim`): the bound is the incompletability, distributed, not a cardinal ceiling. This is the genuine κ-removal — the proliferation bound is a diagonal fact. Whatever the tower's size, no hold holds the whole, because the completed self-inspection is not realisable by any hold.

- **Ambient:** `ws1_diagonal_not_bisim`.
- **Success condition (Discharged, the κ-removal):** the term typechecks with `κ` free (no `hκ`); the second conjunct shows independence of the carrier.
- **Failure mode:** *κ-readmitted (§4.4).* If NT rested on a cardinality bound, the wall would be rebuilt. C2 forecloses it: the proof is `ws1_diagonal_not_bisim`, which uses no κ. The carrier-κ (branching, in `PkObj κ`) is a well-formedness condition on each relatum, NOT a bound on holding — disclosed (§2.7), the WS5/WS7 verdict.

**Paper triage.** Decidable: `ws1_diagonal_not_bisim` uses no κ. **Winner (the κ-removal certificate).**

### C3 — Attention reads full relata, never a leaf (NL, the Series 07 constraint)

```lean
/-- **(NL) — attention reads full relata.** A reified non-empty `SHNE` pattern yields an `SHNE` relatum: the
    reified relatum attention holds has its own relating (`dest (reify s) = s ≠ ∅`), a full relatum, never a
    bare point. The constraint the program respects since Series 07. -/
theorem ws3_attention_reads_full_relata {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) :=
  ws3_reify_preserves_SHNE dest reify h s hs hsucc
```
The reified relatum attention holds is a full relatum: `dest (reify s) = s`, so if `s ≠ ∅` the relatum has successors, and every reachable state does too. Attention never reads a bare point — the atomlessness constraint the program refuses to violate since Series 07.

- **Ambient:** `ws3_reify_preserves_SHNE`, `SHNE`.
- **Success condition (Discharged):** the term is `ws3_reify_preserves_SHNE`; attention reads `SHNE` relata.
- **Failure mode:** *leaf (§4.2).* If attention held a leaf (a bare point with no relating), the atomlessness constraint would be violated. C3 forecloses it: the reified relatum is `SHNE`. Attention reading a leaf anywhere is a SERIOUS finding; C3 proves it does not.

**Paper triage.** Decidable: `ws3_attention_reads_full_relata := ws3_reify_preserves_SHNE`. **Winner (NL, no leaf).**

### C4 — Bounded-holding, derived endogenously from finitude (the κ-readmitted guard)

```lean
/-- **Bounded-holding, endogenous.** Every finite attention reads a bounded part: its reading is finite
    (`att.fin`), so it does NOT hold the whole tower. The bound is FINITUDE OF HOLDING, derived from the
    attention's own structure, refutable by an unbounded hold — NOT a cardinality ceiling on the tower. -/
theorem ws3_bounded_holding_endogenous {Q X : Type u} (dest : X → LkObj κ Q X)
    (att : FiniteAttention dest) : att.reads.Finite ∧ ¬ (att.reads = Set.univ ∧ Infinite X) := by
  refine ⟨att.fin, ?_⟩
  rintro ⟨huniv, hinf⟩
  exact absurd (huniv ▸ att.fin) (Set.infinite_univ (α := X)).not_finite
```
Bounded-holding is endogenous: the attention's reading is finite (`att.fin`), so on an infinite tower it does not hold the whole. The bound is the finitude of the reading — a fact about the attention's structure, refutable by exhibiting an unbounded hold — not a cardinality ceiling on the tower's size. This is the guard against §4.4: "finite" is a property of HOLDING, not a smallness assumption on the tower.

- **Ambient:** `FiniteAttention`, `Set.Finite`, `Set.infinite_univ`.
- **Success condition (Discharged, holding-not-size):** finitude of the reading gives bounded-holding on an infinite tower, with no cardinality assumption on the tower.
- **Failure mode:** *κ-readmitted (§4.4).* If bounded-holding were "the tower has `< κ` relata," it would be κ readmitted. C4 forecloses it: bounded-holding is `att.reads.Finite`, a fact about the hold, and the tower may be `Infinite X` (unboundedly many). The bound is on the HOLD, not the tower.

**Paper triage.** Decidable: `att.fin` is a finiteness field; the tower is unrestricted (`Infinite X` allowed). **Winner (the endogenous bounded-holding, the κ-readmitted guard).**

### C5 — The tower is unboundedly many yet never assembled (the bound's shape, previewing WS4)

```lean
/-- **Unboundedly many, never assembled (previewing WS4).** The tower may be infinite (`Infinite X`), yet no
    hold assembles it (`ws3_no_total_attention`): the many is unbounded but never a completed totality. The
    shape of the endogenous bound — WS4 owns the no-Russell-blowup consequence. -/
theorem ws3_unbounded_yet_unassembled {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t)                                          -- no hold assembles the whole …
  ∧ (∀ h : Hold dest, insp h ≠ diag insp) :=                               -- … and no hold's content is the totality
  ⟨ws1_no_self_total_hold dest insp, ws2_residue_distinct dest insp⟩
```
The bound's shape: the tower may be unboundedly many, but no hold assembles it (no total attention) and no hold's content is the diagonal totality (`ws2_residue_distinct`). So the many is unbounded but never completed — the endogenous bound, previewing WS4's no-Russell-blowup. The bound is everywhere (at every finite hold, none total) and nowhere (no summit).

- **Ambient:** `ws1_no_self_total_hold`, `ws2_residue_distinct`.
- **Success condition (Discharged):** both conjuncts hold — unbounded yet unassembled.
- **Failure mode:** *total-hold / transfinite-limit-breaks-bound.* The finite-stage form holds (both conjuncts are diagonal facts); whether the transfinite limit re-admits a total attention is WS4/WS5's, pre-registered. C5 delivers the finite-stage shape; WS4 owns the no-blowup theorem, WS5 the transfinite.

**Paper triage.** Decidable: both are transcribed diagonal facts. **Winner (the bound's shape, previewing WS4).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | (NT) total attention = self-total hold (Impossibility) | `SelfTotal`, `ws1_no_self_total_hold` | yes — re-read | **win (Impossibility, engine)** |
| C2 | (NT) is κ-free (the genuine removal) | `ws1_diagonal_not_bisim` | yes — no κ used | **win (κ-removal cert)** |
| C3 | (NL) attention reads full relata | `ws3_reify_preserves_SHNE` | yes | **win (no leaf)** |
| C4 | bounded-holding endogenous (finitude, not size) | `FiniteAttention.fin` | yes | **win (κ-readmitted guard)** |
| C5 | unboundedly many yet never assembled | `ws1_no_self_total_hold`, `ws2_residue_distinct` | yes | **win (bound shape, → WS4)** |

## Winning candidates: C1 (Impossibility) + C2 (κ-removal) + C3 (NL) + C4 (bounded-holding) + C5 (bound shape)

### Definitions and obligations (cite `spec/README.md` §2.2, §2.5, §2.6; consume WS1's `FiniteAttention`)

```lean
namespace Series11.WS3
-- Hold, HoldPred, diag, SelfTotal, ws1_no_self_total_hold, ws1_diagonal_not_bisim, ws2_residue_distinct,
-- residue, IsReify, reifyStep, towerN, prec, ws3_reify_preserves_SHNE, SHNE — transcribed (README §6).
-- FiniteAttention — consumed from WS1.

/-- **D0 — total attention = self-total hold (C1, the pin).** -/
def TotalAttention {X : Type u} {dest : X → PkObj κ X}
    (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop := SelfTotal insp t

/-- **D1 — (NT) THE IMPOSSIBILITY (C1).** No hold holds the whole tower: a total attention is a self-total
    hold, forbidden by the diagonal. The bound's engine. -/
theorem ws3_no_total_attention {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, TotalAttention insp t :=
  ws1_no_self_total_hold dest insp

/-- **D2 — (NT) is κ-free (C2, the genuine κ-removal).** No cardinal; independent of relational identity. -/
theorem ws3_no_total_attention_kappa_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ws1_diagonal_not_bisim dest insp

/-- **D3 — (NL) attention reads full relata (C3, no leaf).** -/
theorem ws3_attention_reads_full_relata {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) :=
  ws3_reify_preserves_SHNE dest reify h s hs hsucc

/-- **D4 — bounded-holding, endogenous (C4, the κ-readmitted guard).** Finitude of the reading, not a size
    ceiling on the tower. -/
theorem ws3_bounded_holding_endogenous {Q X : Type u} (dest : X → LkObj κ Q X)
    (att : FiniteAttention dest) : att.reads.Finite ∧ ¬ (att.reads = Set.univ ∧ Infinite X) := by
  refine ⟨att.fin, ?_⟩
  rintro ⟨huniv, hinf⟩
  exact absurd (huniv ▸ att.fin) (Set.infinite_univ (α := X)).not_finite

/-- **D5 — unboundedly many yet never assembled (C5, previewing WS4).** -/
theorem ws3_unbounded_yet_unassembled {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t) ∧ (∀ h : Hold dest, insp h ≠ diag insp) :=
  ⟨ws1_no_self_total_hold dest insp, ws2_residue_distinct dest insp⟩
```

**D1 (NT, the Impossibility)** is the bound's engine: a total attention is a self-total hold, forbidden by the diagonal — `ws3_no_total_attention := ws1_no_self_total_hold`. The pin `TotalAttention := SelfTotal` (D0) is load-bearing: it is why NT routes through the diagonal and not a definitional clause. **D2 (κ-free)** is the genuine κ-removal: no cardinal, independent of the carrier. **D3 (NL)** is no leaf. **D4 (bounded-holding)** is endogenous finitude, the κ-readmitted guard. **D5** previews WS4's no-blowup shape.

## Outcome classes (per charter §7)

- **Impossibility proved (NT, the flagship):** D1 (`ws3_no_total_attention`) and D2 (`ws3_no_total_attention_kappa_free`). A total attention is a self-total hold; no hold holds the whole tower, κ-free. First-class, the cleanest result of the series and the bound's engine.
- **Discharged:** D3 (NL, no leaf), D4 (bounded-holding endogenous), D5 (bound shape). Transcribed / immediate.
- **`totalAttentionSmuggled` (the pre-registered honest failure, charter §4.5):** if `TotalAttention` were defined so it did not unfold to `SelfTotal` (a total attention that is not a self-total hold), a total attention could be admitted — the diagonal violated, attention mis-defined, reported as a design defect (not a bound). D0's pin (`TotalAttention := SelfTotal`) forecloses it; any exhibited total attention is a proof of mis-definition.
- **`kappaReadmitted` (the pre-registered honest failure, charter §4.4):** if bounded-holding (D4) were a cardinality ceiling on the tower rather than finitude of the reading. D4 forecloses it: bounded-holding is `att.reads.Finite`, the tower may be `Infinite X`. The bound is on the hold, not the tower.
- **Partial / transfinite (pre-registered, charter §5.3):** NT holds at every stage (it is a diagonal fact, stage-independent); whether the transfinite LIMIT of the tower re-admits a total attention (an accumulated hold across a limit) is the concrete form the terminal fork most likely takes, handed to WS4/WS5. NT itself is stage-independent, so this is a WS5 question about the tower's limit, not about NT.
- **Strip test.** Delete **"attention" / "holds"** from `ws3_no_total_attention` and the statement is the bare **`¬ ∃ t, SelfTotal insp t`** — `ws1_no_self_total_hold`: no hold contains its own complete content. No-total-attention **survives the strip** as the bare diagonal — and this is exactly what the charter demands (§5, Success Criterion 3): NT must be the diagonal, distributed, NOT an assumption. So the *mathematical* content is the transcribed Series 09/10 diagonal, and "no total attention / a hold of the whole tower / the bound's engine" is the earned **interpretive** layer, flagged honestly. What the strip does **not** remove is the load-bearing gain: the diagonal is now read as a bound on ATTENTION (no hold holds the whole tower), so the incompletability that generates the many (Series 09) is the same incompletability that bounds it (Series 11) — a bound that is holding-not-size (κ-free, D2), refutable by a total attention. WS7 records: no-total-attention is the Series 09/10 diagonal read as the tower's self-bound; its novelty is the reading of the diagonal as no-total-hold, and its κ-freeness (the proof uses no cardinal) is the genuine κ-removal.

## Deliverable

`series-11/formal/Series11/ws3.lean`: transcribed diagonal layer + tower + (NL) preservation (README §6); consumed WS1 `FiniteAttention`; `TotalAttention` (D0), `ws3_no_total_attention` (D1), `ws3_no_total_attention_kappa_free` (D2), `ws3_attention_reads_full_relata` (D3), `ws3_bounded_holding_endogenous` (D4), `ws3_unbounded_yet_unassembled` (D5). **Built early as the seed (charter §6, protocol Phase C): no-total-attention is the object the bound turns on.** Axiom check: `#print axioms ws3_no_total_attention` reduces through `ws1_no_self_total_hold` to `propext` alone (the diagonal uses no choice, no cardinal); crucially **the proof references no κ** — the genuine κ-removal, the κ-readmitted check as a build gate (protocol §D). **NT is Discharged as an Impossibility, κ-free; (NL) and bounded-holding Discharged; the bound (EB) and the crown are NOT attempted here (WS4/WS5's).**
