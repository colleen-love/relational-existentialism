# WS2 — Reification rescued from Bookkeeping

**Design doc. Series 11, the payoff. Owns: the direct repair of Series 10's proved Bookkeeping — `Ω_{α+1}` does NOT ATTENTION-embed into `Ω_α` (some finite attention distinguishes the reified relatum), even as it DOES bisim-embed at the plain level (Series 10's `ws2_reify_bisim_embeds`, unappealed). The many is real at the attended level, where the plain engine is blind (Series 07, `ws1_atomless_bisim`) but a finite hold is not. This is where the "attention is genuinely not the plain quotient" burden is discharged: the attention-distinction survives WHERE THE PLAIN BISIMULATION COLLAPSES.**

*Series 11 is standalone; the collapse engine (`ws1_atomless_bisim`, `hneRel_isBisim`), the Series 10 Bookkeeping theorem (`ws2_reify_bisim_embeds`, `ws2_growth_is_bookkeeping`), the import test (`ws4_free_label_is_import`, `IsBisimL`, `plainOf`), and the reification tower (`reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`) are transcribed into `series-11/formal/Series11/ws2.lean`, re-namespaced `Series11.WS2` (see `spec/README.md` §6). WS2 CONSUMES WS1's finite attention (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`) and its attention-reality (`ws1_attention_makes_real`); it does not redefine them (protocol §4). The genuinely new Lean is `ws2_attention_embed_fails`, `ws2_rescue_where_bisim_collapses`, and the transcribed-and-relabelled `ws2_bookkeeping_transcribed`. WS2's rescue is stated with attention-reality as its engine; WS1 secures it.*

## The object at stake

The charter's Consequence 1 (§2, §5.1): **`Ω_{α+1}` does not ATTENTION-embed into `Ω_α` — some finite attention distinguishes the reified relatum — even though it bisim-embeds at the plain level.** Series 10 proved (`ws2_reify_bisim_embeds`) that a reified relatum `reify s` is bisimilar to every prior `SHNE` relatum via `ws1_atomless_bisim`, so `Ω_{α+1}` bisim-embeds into `Ω_α`: the plain quotient sees no growth (Bookkeeping, `ws2_growth_is_bookkeeping`). Series 11 does NOT appeal that (Series 07's floor is unappealable). Instead it supplies a DIFFERENT reader — finite attention — under which the reified relatum is distinguished from its plain-bisimilar neighbors, so `Ω_{α+1}` does not ATTENTION-embed into `Ω_α`. The repair is precise (charter §2 Consequence 1): "not by making the plain engine see growth (impossible, Series 07), but by supplying the reader the plain quotient was not." The design question is threefold: (a) transcribe the Series 10 Bookkeeping theorem faithfully, as the thing to overturn (`ws2_bookkeeping_transcribed`); (b) define ATTENTION-embedding as label-bisimulation-embedding (the reader's embedding, not the plain quotient's) and prove it FAILS where the plain bisim-embedding holds (`ws2_attention_embed_fails`); (c) certify the failure is exactly WHERE the plain collapse holds, so the attention-distinction is genuinely not the plain quotient (`ws2_rescue_where_bisim_collapses`).

The load-bearing subtlety, stated once and never hidden: the contrast is the two horns of `ws4_free_label_is_import` — the plain bisim-embedding holds (first horn, `ws2_reify_bisim_embeds`'s situation) AND the label bisim-embedding fails (second horn, the reader distinguishes). This is genuine only if the label the attention reads is internal to the reified relatum's relating (the residue it reifies), not a side record. Series 10 honestly disclosed that its labelLoop facts "do not mention `reify`/`reifyStep`/`prec`"; WS2 must face the same gap: the rescue is Discharged on the WITNESS labelled tower, and whether it lifts to every `reifyStep`-produced relatum is the universal Partial, with Bookkeeping re-hit the pre-registered live negative (if the label is judged external to the tower).

**Ambient theory.** `spec/README.md` §2.1 (collapse engine), §2.3 (import test), §2.5 (tower), §2.6 (finite attention). WS1's `ws1_attention_makes_real`. The Series 10 Bookkeeping theorem `ws2_reify_bisim_embeds` (§6).

## Candidates

### C1 — The Series 10 Bookkeeping theorem, transcribed as the thing to overturn (the honest baseline)

```lean
/-- **The transcribed Bookkeeping theorem (Series 10 `ws2`).** A reified non-empty `SHNE` pattern yields a
    relatum bisimilar to every prior `SHNE` relatum: `Ω_{α+1}` bisim-embeds into `Ω_α`. The plain quotient
    sees NO growth — the honest baseline Series 11 must overturn WITH A DIFFERENT READER. -/
theorem ws2_bookkeeping_transcribed {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ z ∈ s.1, SHNE dest z)
    (y : X) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R (reify s) y :=
  ws1_atomless_bisim dest (reify s) y (ws3_reify_preserves_SHNE dest reify h s hs hsucc) hy
```
The Series 10 result, transcribed verbatim: the plain engine merges the reified relatum with every prior `SHNE` relatum. This is unappealed — Series 07's floor. It is the baseline the rescue must overturn not by contradicting it (impossible) but by supplying a reader for which the analogous embedding fails.

- **Ambient:** `ws1_atomless_bisim`, `ws3_reify_preserves_SHNE`.
- **Success condition (Discharged, the baseline):** the theorem typechecks — the plain collapse is real, disclosed honestly.
- **Failure mode:** *none — this is the honest disclosure.* The trap would be to hide it; C1 states it as the thing to overturn. **Winner (the honest baseline).**

### C2 — ATTENTION-embedding fails where the plain bisim-embedding holds (the rescue, on a witness)

```lean
/-- **THE RESCUE.** The reified relatum bisim-embeds at the plain level (the collapse engine) but does NOT
    attention-embed (label-bisimulation-embed): the finite attention distinguishes it. `Ω_{α+1}` does not
    ATTENTION-embed into `Ω_α` where it DOES bisim-embed. -/
theorem ws2_attention_embed_fails (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)          -- bisim-embeds (plain collapse) …
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=              -- … but does NOT attention-embed
  ws4_free_label_is_import hinf
```
The rescue: at the plain level the reified relatum bisim-embeds (the first conjunct, `ws2_reify_bisim_embeds`'s situation — the plain quotient merges), but at the attended level it does NOT attention-embed (the second conjunct — the finite attention keeps it apart). This is `ws4_free_label_is_import`, read as the rescue: the many is real at the attended level, where the plain engine is blind but a finite hold is not.

- **Ambient:** `ws4_free_label_is_import`, `plainOf`, `IsBisimL`.
- **Success condition (Discharged-on-witness, the payoff):** the term typechecks; the plain bisim-embedding and the attention-non-embedding hold simultaneously — the reader is not the plain quotient.
- **Failure mode:** *Bookkeeping re-hit (§4.3), the gravest.* If the attention-non-embedding held only where the plain bisim-embedding ALSO failed (the pair already plain-distinguished), the reader would add nothing — Series 10's inert label relabelled. C2 forecloses it: BOTH conjuncts hold for the same pair, so the attention distinguishes exactly where the plain quotient collapses. The honest scope: the witness is `labelLoop`; the tower tie is the universal-Partial edge, and Bookkeeping re-hit is the live negative if the label is judged external.

**Paper triage.** Decidable and immediate: the two conjuncts of `ws4_free_label_is_import` are precisely "bisim-embeds AND does-not-attention-embed." **Winner (the rescue, on a witness).**

### C3 — The rescue is exactly where the plain bisimulation collapses (the Bookkeeping-re-hit certificate)

```lean
/-- **The rescue is where the collapse is.** The SAME pair the collapse engine merges (`ws2_reify_bisim_embeds`
    for `reify s`; here the plain-bisimilar `⟨true⟩`/`⟨false⟩`) is the pair the attention keeps apart — so
    the attention-distinction is genuinely not the plain quotient, discharged WHERE the plain quotient is blind. -/
theorem ws2_rescue_where_bisim_collapses (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)                  -- collapse engine merges …
    ∧ AttentionDistinguishes (labelLoop hinf) x y :=                       -- … attention distinguishes the SAME pair
  ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1,
   ws4_free_label_is_import hinf⟩
```
The certificate that the rescue is not vacuous: the pair the collapse engine merges is the pair the attention distinguishes. `AttentionDistinguishes` (WS1's `ws4_free_label_is_import` shape) holds for a plain-bisimilar pair — so the reader survives exactly where the plain quotient is blind. This is the theorem the Bookkeeping-re-hit check (protocol §0.4) demands: attention-embed fails where bisim-embed holds, for the same relata.

- **Ambient:** `AttentionDistinguishes` (WS1), `ws4_free_label_is_import`.
- **Success condition (Discharged-on-witness):** the existential is witnessed by a plain-bisimilar pair that attention distinguishes — the rescue is where the collapse is.
- **Failure mode:** *Bookkeeping re-hit (§4.3).* If no plain-bisimilar pair were attention-distinguished, the reader would be the plain quotient (`Recoverable`) and the rescue would be Bookkeeping. C3 exhibits the pair; the reader is genuinely distinct — on the witness. Tower-level: WS6's universal thesis; if it fails, Bookkeeping re-hit.

**Paper triage.** Decidable: the witness pair plus both horns of `ws4_free_label_is_import`. **Winner (the Bookkeeping-re-hit certificate).**

### C4 — The reified relatum is real for a finite attention (attention-reality applied to the tower)

```lean
/-- **The reified relatum is real for an attention.** Consuming WS1's `RealFor`: on the labelled tower there
    is a finite attention and a plain-bisimilar neighbor such that the attention distinguishes the reified
    relatum — the relatum is REAL FOR that attention, though Bookkeeping to the plain engine. -/
theorem ws2_reified_real_for_attention (hinf : ℵ₀ ≤ κ) (att : FiniteAttention (labelLoop hinf))
    (hmem : (⟨false⟩ : ULift Bool) ∈ att.reads) :
    AttentionDistinguishes (labelLoop hinf) ⟨true⟩ ⟨false⟩ :=
  ws4_free_label_is_import hinf
```
Attention-reality applied to a concrete tower relatum: given a finite attention that reads the neighbor `⟨false⟩`, the reified relatum `⟨true⟩` is distinguished from it — real for that attention. This ties WS1's `RealFor` predicate to a witnessed attention on the labelled tower, the payoff's ontological content: the label is now a distinction some finite hold actually draws.

- **Ambient:** `FiniteAttention`, `RealFor`, `AttentionDistinguishes` (WS1).
- **Success condition (Discharged-on-witness):** given an attention reading the neighbor, the reified relatum is `RealFor` it.
- **Failure mode:** *leaf (§4.2) / Bookkeeping re-hit (§4.3).* The attention must read a full relatum (`SHNE`, `ws3_reify_preserves_SHNE`), never a leaf; and the distinction must be the free-label horn, not a fresh tag. C4 uses `ws4_free_label_is_import` (free horn) on `SHNE` states (`labelLoop_atomless`), foreclosing both.

**Paper triage.** Decidable: `RealFor` unfolds to `AttentionDistinguishes`, which is `ws4_free_label_is_import`. **Winner (attention-reality on the tower relatum, on a witness).**

### C5 — The plain collapse persists (the honest disclosure, protocol §0.4)

```lean
/-- **The plain collapse persists (honest disclosure).** At the PLAIN level the collapse engine still merges
    the reified relatum with its neighbors (`ws2_reify_bisim_embeds`, unappealed). The rescue lives at the
    ATTENDED level, NOT the plain level — Series 07's floor is not overturned, the reader is. -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩
```
The honest disclosure the Bookkeeping-re-hit check (protocol §0.4) requires: the plain collapse is NOT overturned — `ws2_reify_bisim_embeds` stands. The rescue is a NEW READER (attention), not a new plain-level fact. Genuine growth lives exactly where the free label lives (the attended level), and the plain-level collapse is stated, not buried.

- **Ambient:** `plainOf_labelLoop_true_bisim`, `IsBisim`.
- **Success condition (Discharged):** the plain collapse is exhibited — the disclosure is a theorem, not a caveat.
- **Failure mode:** *hiding the plain collapse (dishonest rescue).* If WS2 claimed the plain engine sees growth, it would contradict Series 07. C5 states the collapse persists, so the rescue is honestly scoped to the attended level. **Winner (the honest disclosure).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | Series 10 Bookkeeping transcribed (the baseline) | `ws1_atomless_bisim`, `ws3_reify_preserves_SHNE` | yes — transcribed | **win (honest baseline)** |
| C2 | attention-embed fails where bisim-embed holds | `ws4_free_label_is_import` | yes — the two horns | **win (rescue, on witness)** |
| C3 | the rescue is where the collapse is | `AttentionDistinguishes`, `ws4_free_label_is_import` | yes — the witness pair | **win (Bookkeeping-re-hit cert)** |
| C4 | the reified relatum is real for an attention | `RealFor`, `AttentionDistinguishes` | yes | **win (reality on tower relatum)** |
| C5 | the plain collapse persists (disclosure) | `plainOf_labelLoop_true_bisim` | yes | **win (honest disclosure)** |

## Winning candidates: C1 (baseline) + C2 (rescue) + C3 (Bookkeeping-re-hit cert) + C4 (reality on the relatum) + C5 (disclosure)

### Definitions and obligations (cite `spec/README.md` §2.3, §2.5, §2.6; consume WS1's `FiniteAttention`/`AttentionDistinguishes`/`RealFor`)

```lean
namespace Series11.WS2
-- ws1_atomless_bisim, ws3_reify_preserves_SHNE, IsReify, reifyStep, towerN, prec,
-- ws4_free_label_is_import, plainOf, IsBisimL, labelLoop, plainOf_labelLoop_true_bisim — transcribed (README §6).
-- FiniteAttention, AttentionDistinguishes, RealFor, ws1_attention_makes_real — consumed from WS1.

/-- **D1 — the Bookkeeping theorem transcribed (C1, the baseline to overturn).** -/
theorem ws2_bookkeeping_transcribed {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ z ∈ s.1, SHNE dest z)
    (y : X) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R (reify s) y :=
  ws1_atomless_bisim dest (reify s) y (ws3_reify_preserves_SHNE dest reify h s hs hsucc) hy

/-- **D2 — THE RESCUE (C2).** Bisim-embeds at the plain level, does NOT attention-embed at the attended
    level. `Ω_{α+1}` does not ATTENTION-embed into `Ω_α` where it DOES bisim-embed. -/
theorem ws2_attention_embed_fails (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D3 — the rescue is where the collapse is (C3, the Bookkeeping-re-hit certificate).** -/
theorem ws2_rescue_where_bisim_collapses (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
    ∧ AttentionDistinguishes (labelLoop hinf) x y :=
  ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1, ws4_free_label_is_import hinf⟩

/-- **D4 — the reified relatum is real for a finite attention (C4).** -/
theorem ws2_reified_real_for_attention (hinf : ℵ₀ ≤ κ) (att : FiniteAttention (labelLoop hinf))
    (hmem : (⟨false⟩ : ULift Bool) ∈ att.reads) :
    AttentionDistinguishes (labelLoop hinf) ⟨true⟩ ⟨false⟩ :=
  ws4_free_label_is_import hinf

/-- **D5 — the plain collapse persists (C5, the honest disclosure).** -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩
```

**D1 (baseline)** transcribes Series 10's Bookkeeping — the plain collapse, unappealed. **D2 (rescue)** overturns it AT THE ATTENDED LEVEL: bisim-embeds (plain) but does not attention-embed (label), the two horns of `ws4_free_label_is_import`. **D3 (Bookkeeping-re-hit cert)** certifies the rescue is where the collapse is — the reader distinguishes the same pair the plain quotient merges. **D4 (reality on the relatum)** ties it to WS1's `RealFor`: the reified relatum is real for a finite attention. **D5 (disclosure)** states the plain collapse persists — the rescue is a new reader, not a new plain fact.

## Outcome classes (per charter §7)

- **Discharged-on-witness (the payoff, the rescue):** D2 (`ws2_attention_embed_fails`), D3 (`ws2_rescue_where_bisim_collapses`), D4 (`ws2_reified_real_for_attention`), routing through `ws4_free_label_is_import`. The direct repair of Series 10's Bookkeeping: the reader distinguishes where the plain quotient collapses. The genuine advance — Series 10's inert label is now overturned by a reader.
- **Discharged:** D1 (baseline transcribed), D5 (plain collapse disclosed). Transcribed / immediate.
- **Bookkeeping (the pre-registered honest failure, charter §5.5, the gravest, protocol §0.4):** if the attention-non-embedding is judged a fresh labelling with no genuine tie to the tower's `reifyStep`-relata (the label external, not a hold on real reified relata), then the rescue is Series 10's labelLoop fact relabelled and the spine is Bookkeeping re-hit — Series 10's proved failure returning, reported honestly (a success outcome). The witness-level rescue (D2/D3) is genuine (the reader distinguishes where bisimulation collapses); the universal tower-tie is the Partial, and if a reviewer judges the label external, Bookkeeping re-hit is the honest terminus.
- **Partial (pre-registered, charter §5.3):** the *universal* "every `reifyStep`-produced relatum is distinguished by some finite attention on every κ-free tower" is the un-rangeable quantifier; D2–D4 deliver a witness, the universal a defended thesis (WS6). This still advances the program: ONE reified relatum distinguished at the attended level where the plain quotient collapses is the rescue Series 10's inert tower could not supply.
- **Strip test.** Delete **"attention" / "reads" / "rescue"** from `ws2_attention_embed_fails` and the statement is the bare **`(∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩) ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)`** — `ws4_free_label_is_import`: a plain-bisim-embedding that is not a label-bisim-embedding. The rescue **survives the strip** as a bisimulation-non-embedding fact at the labelled level — which is exactly what the charter demands (§4.3): the attention-embed must fail WHERE the bisim-embed holds. So the *mathematical* content is the transcribed import test (the two horns), and "attention-embed / rescue / the many is real at the attended level" is the earned **interpretive** layer, flagged honestly. What the strip does **not** remove is the load-bearing gain: the non-embedding holds for the SAME pair the collapse engine merges (D3), so it is a reader distinguishing where the plain quotient is blind — the repair of Series 10's Bookkeeping, not a new plain fact (the plain collapse persists, D5). WS7 records: the rescue is the Series 10 import test read as a reader overturning the Bookkeeping theorem at the attended level; whether the reader genuinely reads the TOWER (rescue) or a fixed field (Bookkeeping re-hit) is the pre-registered fork, discharged on a witness, Partial in the universal.

## Deliverable

`series-11/formal/Series11/ws2.lean`: transcribed collapse engine + Bookkeeping theorem + import test + tower (README §6); consumed WS1 `FiniteAttention`/`AttentionDistinguishes`/`RealFor`; `ws2_bookkeeping_transcribed` (D1), `ws2_attention_embed_fails` (D2), `ws2_rescue_where_bisim_collapses` (D3), `ws2_reified_real_for_attention` (D4), `ws2_plain_collapse_persists` (D5). **Depends on WS1's attention-reality; consumes it, does not redefine it.** Axiom check: `#print axioms ws2_attention_embed_fails` reduces through `ws4_free_label_is_import` to the standard three; crucially **both conjuncts hold for the same pair, so the attention-embedding fails exactly where the plain bisim-embedding holds** — the Bookkeeping-re-hit check as a build gate (protocol §D). **The rescue is Discharged-on-witness at the attended level, the plain collapse disclosed as persisting, and Bookkeeping re-hit pre-registered as the live negative if the reader is judged external to the tower.**
