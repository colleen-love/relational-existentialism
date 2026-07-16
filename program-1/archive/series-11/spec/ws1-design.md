# WS1 — Finite attention, the κ-removal, and the attention-reality spine

**Design doc. Series 11, the blocking spine. Owns: finite attention (`FiniteAttention`, ambient for all, `spec/README.md` §2.6), the κ-removal (performed once, propagated, §2.7), and the central positive — a finite attention makes a reified relatum REAL by distinguishing it WHERE THE PLAIN BISIMULATION COLLAPSES, and the distinction is FREE (not recoverable from the plain relating), routing through the diagonal residue. Attention-reality routes THROUGH the diagonal: the label the attention reads IS the diagonal content `diag insp`, and its freeness is `ws4_labelLoop_not_recoverable` (not recoverable), which is the residue's freeness read as a reader. WS1 fixes finite attention, the κ-removal, and the carrier, ambient for all.**

*Series 11 is standalone; the carrier (`PkObj`, `SReaches`, `SHNE`, `IsBisim`, `ws1_atomless_bisim`), the diagonal layer (`Hold`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free`), the semantic import test (`LkObj`, `IsBisimL`, `plainOf`, `Recoverable`, `labelLoop`, `ws4_free_label_is_import`, `ws4_labelLoop_not_recoverable`), and the reification section (`IsReify`, `ws1_reify_injective`) are transcribed into `series-11/formal/Series11/ws1.lean`, re-namespaced `Series11.WS1` (see `spec/README.md` §6). The genuinely new Lean is `FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `ws1_attention_makes_real`, `ws1_attention_distinction_free`, `ws1_attention_not_plain_quotient`, and the κ-free re-check `ws1_kappa_free_recheck`. This is the workstream the whole series gates on (charter §6, protocol §4): nothing below is sound until attention-reality lands AND is certified to route through the diagonal and to be a reader genuinely NOT the plain quotient, because that is what rescues Series 10's proved Bookkeeping and what the bound runs on.*

## The object at stake

The charter's spine (§2, §5.1): **on the κ-free tower, a finite attention makes a reified relatum REAL — it distinguishes the relatum where the plain engine is blind, and the distinction is FREE (not recoverable from the plain relating), routing through the diagonal residue.** The mechanism is the reader Series 10 lacked. Series 10 proved (`ws2_reify_bisim_embeds`) that the plain quotient collapses `reify s` into every prior `SHNE` relatum, so the label is inert (Bookkeeping). Series 11's claim is that a finite attention READS the label the plain relating (`plainOf`) forgets, and this reader is provably NOT the plain quotient: it distinguishes `x` from `y` exactly where `ws1_atomless_bisim` merges them (`plainOf`-bisimilar) but no label-bisimulation relates them — the `ws4_free_label_is_import` shape. The distinction is FREE because the label is not recoverable from the plain relating (`ws4_labelLoop_not_recoverable`), and it routes through the diagonal because the label the reified relatum carries IS the residue `diag insp` — the self's own incompletability, held, not an external stamp. The design question is fourfold and each part is a separate obligation: (a) fix **finite attention** as a hold reading a bounded (finite) part of the labelled tower, with FINITUDE load-bearing (`spec/README.md` §2.6); (b) prove **attention makes real** (`ws1_attention_makes_real`) — the reified relatum is distinguished where the plain quotient collapses — with a proof term that routes through `ws4_free_label_is_import`, NOT a fresh labelling; (c) prove the distinction **FREE** (`ws1_attention_distinction_free`, `¬ Recoverable`) and routing through the diagonal residue; (d) perform the **κ-removal** and re-check every reused theorem holds κ-free (`ws1_kappa_free_recheck`).

The load-bearing subtlety, stated once here and never hidden: the `ws4_free_label_is_import` fact is a theorem about a FIXED labelled coalgebra (`labelLoop`), not about the reification tower — exactly as Series 10 honestly disclosed its labelLoop facts "do not mention `reify`, `reifyStep`, `towerN`, or `prec`." What Series 11 adds over Series 10 is the READER: Series 10 had the free label but nothing read it (inert, Bookkeeping); Series 11 exhibits the label-reading attention and certifies it is not the plain quotient and is free. The strip test will show the mathematical core is the `ws4_free_label_is_import` non-embedding fact; what is earned is that this non-embedding is now a hold — a reader — that distinguishes where the collapse engine is blind. **The honest gap (pre-registered, the gravest risk §5.5):** whether the attention genuinely reads the TOWER's reified relata (tying `reifyStep`/`prec` in) or is a fresh labelling of a fixed field is the Bookkeeping-re-hit edge; WS1 discharges attention-reality on a WITNESS and reports the universal Partial, with Bookkeeping-re-hit as the live negative.

**Ambient theory.** `spec/README.md` §2.1 (carrier + collapse engine), §2.2 (diagonal + residue), §2.3 (import test), §2.4 (reification section), §2.6 (finite attention), §2.7 (κ-removal). All from §6.

## Candidates

### C1 — Finite attention as a bounded label-reading hold (the reader decision, charter-faithful)

```lean
structure FiniteAttention {Q X : Type u} (dest : X → LkObj κ Q X) : Type u where
  focus    : X
  reads    : Set X
  fin      : reads.Finite                                       -- FINITUDE, load-bearing
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z
def AttentionDistinguishes {Q X} (dest : X → LkObj κ Q X) (x y : X) : Prop :=
  (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)
def RealFor {Q X} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) (x : X) : Prop :=
  ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y
```
Finite attention is a hold on the labelled tower whose reading is finite (`fin`), directed at a focus and reading a genuine reachable part (`grounded`). It reads the label the plain relating forgets. `AttentionDistinguishes` is the `ws4_free_label_is_import` shape: plain-bisimilar (the collapse engine is blind) but not label-bisimilar (the reader keeps them apart). `RealFor` is attention-reality: a relatum is real for `att` when `att` distinguishes it from a plain-bisimilar neighbor it reads.

- **Ambient:** `LkObj`, `plainOf`, `IsBisim`, `IsBisimL`; `SReaches`.
- **Success condition (Discharged):** the definitions typecheck; finitude is load-bearing (a field, not a derived fact) and the distinction is the free-label horn (a reader that survives the collapse engine).
- **Failure mode:** *twin attention hazards (§4.3, §4.5).* Too-weak: if `AttentionDistinguishes` did not require plain-bisimilarity (the first conjunct), "attention" could distinguish relata the plain quotient already separates — a fresh label with no plain-invisibility content, Bookkeeping re-hit. Too-strong: if `reads` were not required finite, a total attention (reading the whole tower) would be admitted — a self-total hold, violating the diagonal (§4.5). C1 walks the razor: the distinction is where bisimulation collapses (survives the engine, §4.3) and the reading is finite (never total, §4.5).

**Paper triage.** Decidable on paper: `AttentionDistinguishes` is literally the two conjuncts of `ws4_free_label_is_import`; finitude is a `Set.Finite` field. **Winner (the reader decision).**

### C2 — Attention makes real: the reified relatum is distinguished where the plain quotient collapses (the spine, on a witness)

```lean
/-- **THE SPINE.** A finite attention distinguishes the reified relatum where the plain engine is blind:
    the plain quotient MERGES `⟨true⟩` and `⟨false⟩` (the collapse engine, first conjunct) but the
    label-reading attention KEEPS THEM APART (second conjunct). The reader is NOT the plain quotient. -/
theorem ws1_attention_makes_real (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)          -- plain quotient BLIND
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=              -- attention DISTINGUISHES
  ws4_free_label_is_import hinf
```
Attention makes the reified relatum real: on the finite (2-state, hence finitely-read) labelled witness, the collapse engine merges `⟨true⟩` and `⟨false⟩` at the plain level (`ws2_reify_bisim_embeds`'s exact situation, unappealed) but the label-reading attention distinguishes them. This IS `ws4_free_label_is_import`, read as a reader: the many is real at the attended level, where the plain engine is blind but a finite hold is not.

- **Ambient:** `ws4_free_label_is_import`, `labelLoop`, `plainOf`.
- **Success condition (Discharged-on-witness, the spine):** the term typechecks and its proof is `ws4_free_label_is_import` (the reader that survives the collapse), NOT a fresh labelling. Attention-reality is a consequence of the import test, not a stipulation.
- **Failure mode:** *Bookkeeping re-hit (§4.3), the gravest.* If "attention" distinguished by an imported tag with no plain-invisibility (the first conjunct absent), the spine would be a fresh label and Series 10's proved Bookkeeping returns. C2 forecloses it: the FIRST conjunct is the plain quotient's blindness (the collapse engine merges them), so the distinction genuinely survives where bisimulation collapses. The honest scope hazard: the witness is `labelLoop` (a fixed field), so whether attention reads the TOWER's `reifyStep`-relata is the universal-Partial edge (WS2 carries the tower tie), and if a reviewer judges the label external to the tower, the honest terminus is **Bookkeeping** (a success outcome, not a failure).

**Paper triage.** Decidable and immediate: `ws1_attention_makes_real := ws4_free_label_is_import`. The whole content is the transcribed import test, re-read as a reader distinguishing where the collapse engine is blind. **Winner (the spine, on a witness).**

### C3 — The attention-distinction is FREE and routes through the diagonal (the non-import certificate)

```lean
/-- **The distinction is FREE (not recoverable).** No plain bisimulation is a label-bisimulation: the
    reader's distinction is not recoverable from the plain relating — an import, not a coordinate stamped
    from outside. -/
theorem ws1_attention_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf
/-- **Routing through the diagonal.** The label the attention reads is the residue `diag insp`; its freeness
    is the residue's freeness (`ws2_residue_free`), and recovery would reconstruct a self-total hold. The
    distinction is the self's own incompletability held, not an external stamp. -/
theorem ws1_attention_routes_through_diagonal {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp
```
The distinction is free (`ws4_labelLoop_not_recoverable`): the reader is not recoverable from the plain relating, so it is a genuine import (the self's act) rather than a plain-relating artifact. And it routes through the diagonal: the residue the reified relatum carries is not realised by any hold, and recovery would reconstruct a self-total hold (`ws2_residue_is_import`). Attention-reality is not a fresh freeness assumption; it is the residue's freeness read as a reader.

- **Ambient:** `Recoverable`, `ws4_labelLoop_not_recoverable`; `residue`, `ws2_residue_is_import`.
- **Success condition (Discharged):** both terms typecheck; freeness is `ws4_labelLoop_not_recoverable`, routing is `ws2_residue_is_import`, NOT fresh assumptions.
- **Failure mode:** *import (§4.1) — freeness asserted, or the routing decorative.* If freeness were an independent hypothesis, the distinction would be an external label (import); C3 forecloses it (the proof is `ws4_labelLoop_not_recoverable`). The honest disclosure: the routing-through-the-diagonal term (`ws1_attention_routes_through_diagonal`) is about the residue CONTENT (`insp` only) — the tie between the attention's label and `diag insp` is the interpretive step (the label IS the residue), exactly Series 10's honest disclosure that `reify` did not appear in `ws1_free_reification`. WS7 records the tie as interpretive, machine-checked only at the residue-freeness level.

**Paper triage.** Decidable: freeness is `ws4_labelLoop_not_recoverable`; routing is `ws2_residue_is_import`. The label-is-the-residue tie is interpretive, flagged. **Winner (the non-import certificate), scoped honestly.**

### C4 — Attention is not the plain quotient (the Bookkeeping-re-hit guard, made a theorem)

```lean
/-- **Attention is genuinely NOT the plain quotient.** There exist relata the plain quotient MERGES that
    the attention KEEPS APART — so the reader is not the plain bisimulation. This is the exact repair of
    Series 10's Bookkeeping: the label is now read by something the plain engine is not. -/
theorem ws1_attention_not_plain_quotient (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)                 -- merged by the plain quotient …
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y) :=                     -- … kept apart by attention
  ⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩
```
The reader is provably not the plain quotient: it distinguishes a pair (`⟨true⟩`, `⟨false⟩`) that the plain bisimulation merges. This is the theorem that discharges the Bookkeeping-re-hit guard (charter §4.3): "attention makes real" is not the labelled-level fact Series 10 already had relabelled, because the fact Series 10 had was UNREAD (the only reader was the plain quotient, blind); Series 11 exhibits a reader that distinguishes where that quotient collapses.

- **Ambient:** `ws4_free_label_is_import`, `IsBisim`, `IsBisimL`.
- **Success condition (Discharged):** the existential is witnessed by `⟨true⟩`/`⟨false⟩` and `ws4_free_label_is_import`; the reader is a genuine non-quotient.
- **Failure mode:** *Bookkeeping re-hit (§4.3).* If no such pair existed (every plain-bisimilar pair were label-bisimilar, i.e. `Recoverable`), attention would BE the plain quotient and the spine would be Bookkeeping. C4 exhibits the pair, so the reader is genuinely distinct — but only on the witness field; the tower-level distinctness is WS2's burden, and if it fails there, the honest terminus is Bookkeeping re-hit.

**Paper triage.** Decidable: the witness pair plus `ws4_free_label_is_import`. **Winner (the Bookkeeping-re-hit guard, on a witness).**

### C5 — The κ-removal and its propagation (the second design duty, §2.7)

```lean
/-- **The κ-free re-check.** Every reused theorem holds for all `κ ≥ ℵ₀`; the diagonal bound holds for ALL
    κ (references no cardinal). No result relies on κ being small — the large-κ discipline promoted to
    holding-not-size. -/
theorem ws1_kappa_free_recheck {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (reify : PkObj κ X → X) (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    -- (i) the diagonal (no-total-attention's engine) uses NO κ — holds for every κ:
    (¬ ∃ t, SelfTotal insp t)
    -- (ii) the collapse engine holds for every κ:
  ∧ (∀ x y, SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y)
    -- (iii) (NL) reification preserves SHNE for every κ:
  ∧ SHNE dest (reify s) :=
  ⟨ws1_no_self_total_hold dest insp, fun x y hx hy => ws1_atomless_bisim dest x y hx hy,
   ws3_reify_preserves_SHNE dest reify h s hs hsucc⟩
```
The κ-removal, performed once: the three load-bearing reused theorems are re-checked to hold with no small-κ assumption. The diagonal (`ws1_no_self_total_hold`) uses no κ at all — the genuine κ-removal, the bound as a diagonal fact. The collapse engine and (NL) hold for all `κ ≥ ℵ₀`. Any theorem that relied on κ being small would be reopened here; none does.

- **Ambient:** `ws1_no_self_total_hold`, `ws1_atomless_bisim`, `ws3_reify_preserves_SHNE`.
- **Success condition (Discharged):** the conjunction typechecks with `κ` a free variable (no `hκ : κ < …` hypothesis); the diagonal branch uses no κ.
- **Failure mode:** *κ readmitted (§4.4), the second cardinal sin.* If a reused theorem needed κ small, the bound would rest on a ceiling. C5 forecloses it for the three load-bearing theorems. The honest disclosure (§2.7): the CARRIER κ (branching, in `PkObj κ`) remains, as the section `reify`'s existence condition (Cantor); whether that is κ readmitted is the WS5/WS7 verdict, pre-registered as the tragic edge, NOT hidden.

**Paper triage.** Decidable: read off the transcribed proofs — `ws1_no_self_total_hold` has κ only as an unused type parameter. **Winner (the κ-removal, with the carrier-κ disclosed).**

### C6 — The unification seed: a finite attention IS a finite hold (charter Consequence 3, WS1's share)

```lean
/-- **The unification seed (charter §2 Consequence 3).** A finite attention IS a finite hold: its focus and
    reading are a `Hold`-shaped restriction, and the tower is what it proliferates by reifying residues.
    Stated as an identification tying Series 08's finite hold to Series 11's attention; the universal
    equivalence is WS6's thesis. -/
theorem ws1_attention_is_finite_hold {Q X} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ⟨att.fin, att.grounded.2⟩
```
A finite attention is a finite hold: it holds a bounded reachable part, directed at a focus — the Series 08 finite hold, now reading a GROWING (reifying) field rather than a fixed one. Series 08 got a Partial because a finite hold on a fixed field could not generate plurality; Series 11's finite attention on the reifying tower both reads (the reified residues) and bounds (finitude of holding). This ties the two objects; the full equivalence is WS6.

- **Ambient:** `FiniteAttention`, `SReaches`.
- **Success condition:** the identification typechecks, tying attention to the finite hold; the universal equivalence is a WS6 thesis (charter §5.5).
- **Failure mode:** *the unification is a gloss (§5.5).* If the tie were merely asserted, Consequence 3 would be a gloss not a theorem. C6 makes the structural tie (attention = finite reachable hold) a theorem; the interpretive claim (Series 08's hold IS Series 11's attention) is flagged as the earned reading, WS6's to defend.

**Paper triage.** Decidable: reads off the `FiniteAttention` fields. **Winner (the unification seed), the universal deferred to WS6.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | finite attention = bounded label-reading hold | `LkObj`, `plainOf`, `Set.Finite` | yes — the free-label horn + a finiteness field | **win (reader decision)** |
| C2 | attention makes real (distinguishes where bisim collapses) | `ws4_free_label_is_import` | yes — is that theorem | **win (spine, on witness)** |
| C3 | the distinction is free, routes through the diagonal | `ws4_labelLoop_not_recoverable`, `ws2_residue_is_import` | yes | **win (non-import cert), scoped** |
| C4 | attention is not the plain quotient | `ws4_free_label_is_import` | yes — the witness pair | **win (Bookkeeping-re-hit guard)** |
| C5 | κ removed, re-checked κ-free | `ws1_no_self_total_hold` (no κ) | yes — read off proofs | **win (κ-removal), carrier-κ disclosed** |
| C6 | a finite attention IS a finite hold (unification seed) | `FiniteAttention` fields | yes | **win (unification seed), universal → WS6** |

## Winning candidates: C1 (reader), C2 (spine), C3 (non-import), C4 (Bookkeeping guard), C5 (κ-removal); C6 the unification seed

### Definitions and obligations

```lean
namespace Series11.WS1
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, BehaviorallyIdentified, hneRel, hneRel_isBisim,
-- ws1_atomless_bisim, ws2_import_theorem_static, LkObj, IsBisimL, plainOf, Recoverable, labelLoop,
-- ws4_free_label_is_import, ws4_recoverable_not_import, ws4_labelLoop_not_recoverable, Symmetric,
-- ws1_symmetric_states_bisimilar, Hold, afford, HoldPred, diag, SelfTotal, ws1_no_self_total_hold,
-- ws1_diagonal_not_bisim, residue, ResidueRecoverable, ws2_residue_free, ws2_residue_is_import,
-- IsReify, ws1_reify_injective, reifyStep, towerN, prec, ws3_reify_preserves_SHNE — all transcribed (README §6).

/-- **D0 — finite attention (C1, the reader decision, ambient for all).** A hold reading a bounded (finite)
    part of the labelled tower. FINITUDE is load-bearing. -/
structure FiniteAttention {Q X : Type u} (dest : X → LkObj κ Q X) : Type u where
  focus    : X
  reads    : Set X
  fin      : reads.Finite
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z
def AttentionDistinguishes {Q X} (dest : X → LkObj κ Q X) (x y : X) : Prop :=
  (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)
def RealFor {Q X} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) (x : X) : Prop :=
  ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y

/-- **D1 — THE SPINE (C2, attention makes real).** The reified relatum is distinguished where the plain
    quotient collapses: `plainOf`-bisimilar (the collapse engine is blind) but NOT label-bisimilar (the
    reader distinguishes). This IS `ws4_free_label_is_import`, read as a reader. Discharged on the finite
    labelled witness; the tower-level tie is WS2's, the universal a WS6 thesis. -/
theorem ws1_attention_makes_real (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D2 — the distinction is FREE (C3, the non-import certificate).** Not recoverable from the plain
    relating: an import (the self's act), not a coordinate stamped from outside. -/
theorem ws1_attention_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

/-- **D3 — routing through the diagonal (C3).** The label the attention reads is the residue `diag insp`;
    its freeness is the residue's, and recovery reconstructs a self-total hold. The tie between the label
    and `diag insp` is interpretive (the machine-checked content is residue-freeness, `insp` only) — flagged,
    not hidden, exactly as Series 10 disclosed for `ws1_free_reification`. -/
theorem ws1_attention_routes_through_diagonal {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp

/-- **D4 — attention is not the plain quotient (C4, the Bookkeeping-re-hit guard).** A pair merged by the
    plain quotient but kept apart by attention — the reader is genuinely not the plain bisimulation. -/
theorem ws1_attention_not_plain_quotient (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y) :=
  ⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩

/-- **D5 — the κ-removal, re-checked (C5, §2.7).** The diagonal bound uses NO κ; the collapse engine and
    (NL) hold for all large κ. No result relies on small κ. Carrier-κ disclosed (WS5/WS7's verdict). -/
theorem ws1_kappa_free_recheck {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (reify : PkObj κ X → X) (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ x y, SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y)
  ∧ SHNE dest (reify s) :=
  ⟨ws1_no_self_total_hold dest insp, fun x y hx hy => ws1_atomless_bisim dest x y hx hy,
   ws3_reify_preserves_SHNE dest reify h s hs hsucc⟩

/-- **D6 — the unification seed (C6).** A finite attention IS a finite hold; the universal equivalence is WS6's. -/
theorem ws1_attention_is_finite_hold {Q X} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ⟨att.fin, att.grounded.2⟩
```

**D1 — the spine.** *Strategy:* `ws1_attention_makes_real := ws4_free_label_is_import`. The first conjunct is the collapse engine's blindness (the plain quotient merges), the second is the reader's distinction (label-bisimulation keeps apart). *Paper-decidable:* yes. *Non-circularity (§4.3):* the proof is the transcribed `ws4_free_label_is_import`; the reader survives where bisimulation collapses by construction (the first conjunct). The honest scope: the witness is `labelLoop` (a fixed field); the tower tie is WS2's, the universal WS6's, and Bookkeeping re-hit is the pre-registered live negative.

**D2/D3 — free, through the diagonal.** Freeness is `ws4_labelLoop_not_recoverable` (an import, not a plain artifact); the routing is `ws2_residue_is_import` (the residue-content freeness). The tie "the label IS `diag insp`" is interpretive, flagged — the machine-checked content is residue-freeness, as Series 10 disclosed.

**D4 — the Bookkeeping-re-hit guard.** The reader is not the plain quotient: it distinguishes `⟨true⟩`/`⟨false⟩` where the plain bisimulation merges them. This is the exact repair of Series 10's inert label — now READ.

**D5 — the κ-removal.** The genuine removal is the diagonal branch (no κ); the large-κ discipline is promoted (all reused theorems hold for `κ ≥ ℵ₀`). The carrier-κ (branching) is disclosed as scaffolding, its status the WS5/WS7 verdict.

## Outcome classes (per charter §7)

- **Discharged-on-witness (the spine, attention-reality):** D1 (`ws1_attention_makes_real`), D2 (`ws1_attention_distinction_free`), D4 (`ws1_attention_not_plain_quotient`), routing through the import test (`ws4_free_label_is_import` / `ws4_labelLoop_not_recoverable`). The reader Series 10 lacked, now exhibited and certified free and non-quotient — the genuine advance. Near-certain as a *theorem* (it transcribes built Series 10 theorems); the load-bearing claim is that it is a READER distinguishing where the collapse engine is blind, which the first conjunct secures.
- **Discharged:** D0 (finite attention definitions), D5 (κ-free re-check), D6 (unification seed). Transcribed / immediate.
- **Bookkeeping (the pre-registered honest failure at the payoff, charter §5.5, the gravest):** if the attention-distinction is judged a fresh labelling of a fixed field with no genuine tie to the tower's `reifyStep`-relata (the label external, not a hold on real reified relata), then "attention makes real" is Series 10's labelled-level fact relabelled — Bookkeeping re-hit, Series 10's proved failure returning, reported honestly (a success outcome, not buried). Routed to WS2 (which owns the tower tie) and WS7. Not expected to defeat the witness-level spine (the reader genuinely distinguishes where bisimulation collapses, D4), but the universal tower-tie is where the burden must be discharged, and its Partial is honest.
- **`totalAttentionSmuggled` (the pre-registered honest failure at the carrier, charter §4.5):** if `FiniteAttention` were defined without `fin` (or `AttentionDistinguishes` admitted a total hold), a self-total hold at tower scale would be smuggled past the diagonal — an attention DESIGN DEFECT, reported as such. D0's `fin` field forecloses it; WS3's `ws3_no_total_attention` proves no total attention exists.
- **`kappaReadmitted` (the pre-registered honest failure, charter §4.4):** if the κ-removal (D5) silently relied on κ small, or the bound rested on a cardinality ceiling. D5 forecloses it for the three load-bearing theorems (the diagonal uses no κ). The carrier-κ (branching) is disclosed (§2.7); whether it counts as κ readmitted is the WS5/WS7 verdict, pre-registered as the tragic edge.
- **Partial (pre-registered, charter §5.3):** the *universal* "every finite attention on every κ-free tower reads freely" is the un-rangeable quantifier; D1 delivers a witness, the universal a defended thesis (WS6). This still advances the program, since ONE finite attention reading the free label where the plain quotient collapses is the reader Series 10's inert tower could not supply.
- **Strip test.** Delete **"attention" / "reads" / "real"** from `ws1_attention_makes_real` and the statement is the bare **`(∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩) ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)`** — `ws4_free_label_is_import`: a plain-bisimilar pair that is not label-bisimilar (a free-label non-embedding). Attention-reality **survives the strip** as a free-label bisimulation-non-embedding fact — and this is exactly what the charter demands (§4.1, §4.3): the distinction must be where bisimulation collapses (survives the engine) and free (not recoverable). So the *mathematical* content is the transcribed Series 10 import test, and "attention / reads / real / the reader Series 10 lacked" is the earned **interpretive** layer, flagged here honestly. What the strip does **not** remove is the load-bearing structural gain over Series 10: the free label is now a HOLD — a reader (`FiniteAttention`, `AttentionDistinguishes`) that distinguishes where the collapse engine is blind, which is what makes the label ontology rather than inert record. WS7 records: attention-reality is the Series 10 import test routed to a reader; its novelty over Series 10 is the reading that turns the inert free label into a distinction some finite hold actually draws, and whether that reader genuinely reads the TOWER (rescue) or a fixed field (Bookkeeping re-hit) is WS2's burden, not WS1's word.

## Deliverable

`series-11/formal/Series11/ws1.lean`: transcribed carrier + collapse engine + diagonal layer + import test + reification section + tower seed + coincidence witness (README §6); `FiniteAttention`, `AttentionDistinguishes`, `RealFor` (D0); `ws1_attention_makes_real` (D1), `ws1_attention_distinction_free` (D2), `ws1_attention_routes_through_diagonal` (D3), `ws1_attention_not_plain_quotient` (D4), `ws1_kappa_free_recheck` (D5), `ws1_attention_is_finite_hold` (D6). Axiom check: `#print axioms ws1_attention_makes_real` reduces through `ws4_free_label_is_import` to `propext` / the standard three; crucially **the spine's first conjunct is the plain quotient's blindness (the collapse engine merges), so the reader genuinely distinguishes where bisimulation collapses** — the single most important build check (protocol §D, the Bookkeeping-re-hit check). **This file is built first (charter §6): it fixes finite attention, the κ-removal, and the carrier for WS2–WS6.**
