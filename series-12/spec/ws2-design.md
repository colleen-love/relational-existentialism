# WS2, Knowing: finite attention, and the opening inhabited

**Design doc. Series 12, the formalizable side, the plurality. Owns: finite attention (subtractive, plural, no attention holding the whole) and the proof that the opening is INHABITABLE and that inhabitation makes the many real, `Many` on the concrete rank-labelled tower, where a reified relatum and a base relatum are genuinely plain-bisimilar (the collapse engine merges them) yet separated at the labelled level by their tower RANK, `reify`/`reifyStep`/`towerN` load-bearing; and without any import, the One (`ws1_atomless_bisim`). The distinction is non-recoverable, which by Series 07 is its CERTIFICATE, not its defect. WS2 is the guard against degenerate (point-tag) inhabitation.**

*Series 12 is standalone; finite attention (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `ws3_no_total_attention`), the collapse engine (`ws1_atomless_bisim`, `ws2_import_theorem_static`), and the tower (`reifyStep`, `towerN`, `ws3_reify_preserves_SHNE`) are transcribed into `series-12/formal/Series12/ws2.lean`, re-namespaced `Series12.WS2` (see `spec/README.md` §6). WS2 DEFINES `Many` (README §2.8) and hosts the concrete carrier of `spec/ws4-witness-design.md` (the `dir := rank` witness). It CONSUMES WS1's opening (`Opening`, `¬ Recoverable`); it does not redraw it. The genuinely new Lean is `Many`, `ws2_many_witness`, and the load-bearing certificate `ws_witness_reification_loadbearing`. The one signature risk is degenerate inhabitation (discipline 4): a bare point-tag with no tower content, the Bookkeeping re-hit Series 10 and 11 landed on.*

## The object at stake

The charter's WS2 (§2): the opening is INHABITABLE, and any inhabitant makes the many real. Two facts, one carrier. (1) **Inhabitability with plurality:** adjoin an inhabitant as a labelled direction over the plain structure (the labelled lift, with the plain quotient forgetting it), and prove `Many`: a reified tower relatum and a base relatum genuinely plain-bisimilar (the Series 07 engine merges them, `ws1_atomless_bisim`) yet separated at the labelled level, the reification facts LOAD-BEARING, generalized across the tower. (2) **Without an import, the One:** `ws2_import_theorem_static`, a plain, behaviorally-identified, atomless coalgebra is a subsingleton. The plurality's distinction is non-recoverable (`ws2_distinction_free`), which is its CERTIFICATE: by Series 07 (WS1's required half) a genuine atomless distinction MUST be non-recoverable, so non-recoverability is the sign the distinction is real, not the sign it cheats. (Inhabitation is also proved reader-relative: `ws2_attention_makes_real`, a genuine finite attention for which the reified relatum is real, program-review-1 PR1-S2.)

The design's whole burden is discipline 4, and it is the program's gravest inherited risk. Series 10 (`ws2_reify_bisim_embeds`) and Series 11 (`ws1_attention_makes_real`) both drew their distinction on `labelLoop`, two fixed Booleans where `reify`/`reifyStep`/`towerN` never occur, and were honestly re-graded Bookkeeping re-hit. **WS2 must not repeat that:** the separated pair is a genuine reified relatum `reifyW sW` and its base constituent `aW`, and the label is the tower RANK (`dir := rank`), defined from `towerN`/`reifyStep`. The witness is fully designed in `spec/ws4-witness-design.md`; WS2 states the plurality it discharges.

**Ambient theory.** `spec/README.md` §2.1 (collapse engine), §2.6 (finite attention), §2.8 (`Many`); the witness carrier (`ws4-witness-design.md`).

## Candidates

### C1, Finite attention is subtractive and never total (the formal side, transcribed)

```lean
/-- **Attention is subtractive and never total.** Every finite attention reads a bounded part (`att.fin`);
    NO attention holds the whole (`ws3_no_total_attention` = the diagonal at tower scale), so no
    self-definition closes, the residue is always past the bound. -/
theorem ws2_attention_subtractive {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t)
  ∧ (∀ h : Hold dest, insp h ≠ residue insp) :=
  ⟨ws3_no_total_attention dest insp, ws2_residue_distinct dest insp⟩
```
Knowing is bounded: attention reads a finite part, no attention totalizes, the residue is always outside the bound.

- **Ambient:** `ws3_no_total_attention`, `ws2_residue_distinct`, `FiniteAttention.fin`.
- **Success condition (Discharged, transcribed):** the term typechecks, the subtractive, never-total character of knowing, transcribed from the diagonal.
- **Failure mode:** *none, transcription.* **Winner (the formal side).**

### C2, `Many` on the rank witness (the plurality; the payoff)

```lean
/-- **THE PLURALITY (`Many`, on a genuine tower-distinction).** On the rank-labelled lift a reified relatum
    `cW = reifyW {bW}`, itself CARRYING the reified constituent `bW`, and a base relatum `aW` are
    plain-bisimilar (the collapse engine is blind) yet rank-separated at the labelled level. An INSTANCE of
    the general separation `ws2_many_general`; `reify`/`reifyStep`/`towerN`/rank load-bearing, and rank is
    non-injective (README §2.7, the witness carrier). -/
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) :=
  ⟨cW, aW, ws1_atomless_bisim _ cW aW (ws_witness_SHNE hinf).top (ws_witness_SHNE hinf).base,
   (ws2_many_general (destW hinf) (reifyW hinf) rankW (sW₂ hinf) … bW … aW … ).2⟩
```
The inhabited opening: `Many destWL` (README §2.8), discharged on the `dir := rank` carrier as an instance of the general theorem (C6). Plain-bisimilar (`ws1_atomless_bisim`, the engine merges the reified relatum and the base relatum) yet not label-bisimilar (their broadcast ranks `⟨2⟩`, `⟨0⟩` mismatch). The separated relatum `cW` carries a reified constituent `bW` (rank 1), so the distinction is on the tower's genuinely up-tower relata, and rank is non-injective (`aW`, `aW'` share rank 0), so the label is coarser than identity, not a point-indicator (Finding 1).

- **Ambient:** `Many`, `ws1_atomless_bisim`, `ws2_many_general`, the witness carrier (README §2.7).
- **Success condition (Shape-drawn on the witness):** `Many destWL` holds with the separated pair a reified relatum carrying a reified constituent vs a base relatum, as an instance of the general theorem, rank non-injective.
- **Failure mode:** *degenerate inhabitation (discipline 4), the gravest.* If the separating direction were a bare point-indicator (a tag on one distinguished element, no tower content, injective on a two-element carrier, `labelLoop` or the two-state silhouette), the opening would be inhabitable only degenerately. C2 forecloses it via C3 (reification load-bearing), the non-injective rank, and C6 (the general theorem). **Winner (the plurality).**

**Paper triage.** Decidable: `ws1_atomless_bisim` merges the two `SHNE` relata (plain side); the source ranks `⟨2⟩ ≠ ⟨0⟩` block every label-bisimulation (labelled side); the pair instances `ws2_many_general`. **Winner.**

### C3, The reification is load-bearing (the anti-point-tag certificate)

```lean
/-- **REIFICATION LOAD-BEARING (the certificate the review greps for).** The separated relatum `cW` is a
    genuine reified relatum, adjoined by `reifyStep` at tower rank 2, CARRYING the reified constituent `bW`
    (rank 1), `dest (reify sW₂) = sW₂` pointwise, NOT a fixed Boolean. This is what `labelLoop` and the
    two-state silhouette lacked (Finding 1). -/
theorem ws2_reification_loadbearing (hinf : ℵ₀ ≤ κ) :
    cW = reifyW hinf (sW₂ hinf)
  ∧ cW ∈ reifyStep (destW hinf) (reifyW hinf) (towerN (destW hinf) (reifyW hinf) {aW, aW'} 1)
  ∧ bW ∈ (sW₂ hinf).1 ∧ 1 ≤ rankW bW
  ∧ destW hinf (reifyW hinf (sW₂ hinf)) = (sW₂ hinf).1 :=
  ws_witness_reification_loadbearing hinf
```
The certificate that C2's inhabitation is genuine: the separated relatum `cW` IS a `reifyStep`-produced reified relatum, at `towerN` rank 2, carrying the reified constituent `bW`; `reify`/`reifyStep`/`towerN` all occur and are load-bearing. Paired with the non-injective rank (`ws_witness_rank_noninjective`) and the general theorem (C6), the three certificates Finding 1 requires.

- **Ambient:** `reifyStep`, `reify_mem_reifyStep`, `towerN`, `rankW`, the pointwise reification facts.
- **Success condition (Shape-drawn):** `reify`/`reifyStep`/`towerN` occur load-bearing; the label is the tower rank; the separated relatum carries a reified constituent.
- **Failure mode:** *the label judged external to the tower (point-tag), Partial.* Foreclosed: `cW ∈ reifyStep (towerN … 1)` and the rank = `towerN` position tie the label to the tower's own structure, and rank is non-injective. **Winner (the anti-point-tag certificate).**

**Paper triage.** Decidable: `cW = reifyW {bW}` and `cW ∈ reifyStep (towerN … 1)` by `reify_mem_reifyStep`; the rank is the `towerN 2` position; `bW` a reified constituent of rank 1. **Winner.**

### C4, Without an import, the One (the collapse side, transcribed)

```lean
/-- **WITHOUT AN IMPORT, THE ONE.** A plain, behaviorally-identified, atomless coalgebra is a subsingleton, 
    strip the labelled direction and the collapse engine returns monism (`ws2_import_theorem_static`). -/
theorem ws2_no_import_is_one {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ws2_import_theorem_static dest hbehav hatom
```
The other side of the two-sided plurality: WITHOUT the imported direction, the plain atomless structure collapses to the One. This is genuine Series 07 (`ws1_atomless_bisim` under behavioral identity), not a rigged collapse.

- **Ambient:** `ws2_import_theorem_static`, `ws1_atomless_bisim`.
- **Success condition (Discharged, transcribed):** the collapse holds, the many needs the import; without it, the One.
- **Failure mode:** *the collapse rigged.* Foreclosed: it is genuine `ws2_import_theorem_static` (Series 07's floor). **Winner (the collapse side).**

### C5, The distinction is free, its certificate (discipline the review runs)

```lean
/-- **THE DISTINCTION IS FREE (its certificate, not its defect).** The rank-separation is not recoverable
    from the plain relating: an import, which by Series 07 (WS1's required half) is what a genuine atomless
    distinction MUST be. Non-recoverability is the certificate. -/
theorem ws2_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (destWL hinf) := …
```
The certificate: the plurality's distinction is `¬ Recoverable`. By WS1's required half, a genuine atomless distinction is non-recoverable; so this is the sign the distinction is real, not the sign it cheats, the lesson the whole series turns on.

- **Ambient:** `Recoverable`, `plainOf`, the rank-separation, `ws2_distinction_free` (the shape).
- **Success condition (Shape-drawn):** `¬ Recoverable destWL`, the distinction is free, its certificate.
- **Failure mode:** *reading non-recoverability as a defect.* Foreclosed by WS1: non-recoverability is what a genuine distinction must be. **Winner (the certificate).**

### C6, Generalization across the tower (the reach beyond one relatum)

```lean
/-- **THE GENERAL RANK-SEPARATION (Finding 1, reinstated; `reify`/`rank`/base-closure load-bearing in the
    STATEMENT).** For any `dest`, `reify`, `rank` where a reified relatum ranks strictly above its
    constituents, any pattern `s` whose reified relatum carries a constituent `w₀` of rank at least 1 (a
    REIFIED constituent), and any base relatum `y` of rank 0, the reified relatum and the base relatum are
    plain-bisimilar (the collapse engine) yet NOT label-bisimilar over the rank-labelled lift. The plurality
    is not one lucky pair; the concrete `Many` pair (`cW`, `aW`) is an INSTANCE (`s := sW₂`, `w₀ := bW`). -/
theorem ws2_many_general {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (rank : X → ℕ)
    (s : PkObj κ X) (hs : s.1 ≠ ∅) (hpt : dest (reify s) = s)
    (w₀ : X) (hw₀ : w₀ ∈ s.1) (hw₀rank : 1 ≤ rank w₀)
    (hstep : ∀ w ∈ s.1, rank w < rank (reify s))
    (y : X) (hyrank : rank y = 0)
    (hshne_r : SHNE dest (reify s)) (hshne_y : SHNE dest y) :
    (∃ R, IsBisim dest R ∧ R (reify s) y)
  ∧ (¬ ∃ R, IsBisimL (rankLift dest rank) R ∧ R (reify s) y) := …
```
The reach beyond one relatum: the separation is a GENERAL theorem over `(dest, reify, rank)`, with `reify`, `rank`, and the strict-rank-step (`hstep`, giving `rank (reify s) > rank w₀ ≥ 1 > 0 = rank y`, the label mismatch) load-bearing in the statement, and the reified relatum genuinely carrying a reified constituent (`hw₀rank`). The reification structure, not one point, does the work (Finding 1).

- **Ambient:** `ws1_atomless_bisim`, `rankLift`, the strict-rank-step, `ws3_reify_preserves_SHNE`.
- **Success condition (Shape-drawn on the witness / Partial universal):** the general theorem separates any reified-carrying-reified relatum from any base relatum; the concrete pair is an instance; the fully universal form over every κ-free tower is WS6's ceiling.
- **Failure mode:** *the family collapses to one tag.* Foreclosed: general over `(dest, reify, rank)`, `reify`/`rank`/step load-bearing in the statement, the reified constituent required. **Winner (the generalization, Partial in the universal).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | attention subtractive, never total | `ws3_no_total_attention`, `ws2_residue_distinct` | yes, transcribed | **win (formal side)** |
| C2 | `Many` on the rank witness (`cW` vs `aW`, an instance of C6) | `ws1_atomless_bisim`, `ws2_many_general` | yes, merge + rank mismatch | **win (plurality)** |
| C3 | reification load-bearing (`cW` carries reified `bW`) | `reifyStep`, `reify_mem_reifyStep`, `towerN`, `rankW` | yes, `cW ∈ reifyStep (towerN … 1)` | **win (anti-point-tag)** |
| C4 | without an import, the One | `ws2_import_theorem_static` | yes, transcribed | **win (collapse side)** |
| C5 | the distinction is free (certificate) | `Recoverable`, `plainOf` | yes, rank not recoverable | **win (certificate)** |
| C6 | the general rank-separation (Finding 1) | `ws1_atomless_bisim`, `rankLift`, strict-rank-step | yes (general) / Partial (universal) | **win (generalization)** |

## Winning candidates: C1–C6

### Definitions and obligations (cite `spec/README.md` §2.6, §2.8; consume the witness carrier)

```lean
namespace Series12.WS2
-- FiniteAttention, AttentionDistinguishes, RealFor, TotalAttention, ws3_no_total_attention,
-- ws2_residue_distinct, ws1_atomless_bisim, ws2_import_theorem_static, reifyStep, reify_mem_reifyStep,
-- towerN, ws3_reify_preserves_SHNE, Recoverable, plainOf, transcribed (README §6).
-- The dir:=rank carrier (WCar, aW, aW', bW, cW, destW, sW, sW₂, reifyW, rankW, rankLift, destWL) and its
-- lemmas (incl. ws_witness_rank_noninjective), spec/ws4-witness-design.md.

/-- **The plurality predicate, defined once (README §2.8).** -/
def Many {Q X : Type u} (destL : X → LkObj κ Q X) : Prop :=
  ∃ x y : X, (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)

-- D1 ws2_attention_subtractive (C1) ; D2 ws2_many_witness (C2) ; D3 ws2_reification_loadbearing (C3) ;
-- D4 ws2_no_import_is_one (C4) ; D5 ws2_distinction_free (C5) ; D6 ws2_many_general (C6).
```

**Proof architecture.** D1 (subtractive, never total) transcribes the diagonal at tower scale. D2 (`Many`) is the payoff: plain-bisimilar (the engine) ∧ rank-separated (the labelled level), discharged on the `dir := rank` carrier. D3 certifies the inhabitation is genuine: the separated relatum is a `reifyStep`-produced reified relatum, its rank its `towerN` position, the anti-point-tag guard the review greps for. D4 (the One) transcribes `ws2_import_theorem_static`: without the import, monism. D5 certifies the distinction free (`¬ Recoverable`), its certificate by WS1's required half. D6 generalizes across the tower. **Dependencies:** WS1's opening (the `¬ Recoverable` shape D5 inhabits); the witness carrier (`ws4-witness-design.md`); `ws1_atomless_bisim` and `ws2_import_theorem_static` (Series 07 floor). The disclosed pointwise-`IsReify` deviation is carried from the witness (README §2.5).

## Outcome classes (per charter §5)

- **Shape-drawn on the witness (the payoff):** D2 (`ws2_many_witness`), D3 (`ws2_reification_loadbearing`), D5 (`ws2_distinction_free`), the opening inhabitable, the many real, on a genuine tower-distinction with reification load-bearing, the distinction free as its certificate. The genuine tower-distinction Series 10 and 11 could not draw.
- **Discharged (transcribed):** D1 (subtractive/never-total), D4 (the One without an import).
- **Partial (pre-registered, discipline 4):** the fully universal "every `reifyStep`-produced relatum on every κ-free tower is separated by some finite attention" is the un-rangeable quantifier; D2–D6 deliver a witness and the general theorem, the fully universal form a WS6 thesis. And if a reviewer judges the rank label external to the tower, the inhabitation is a point-tag and the finding demotes to Partial, foreclosed by D3 (`cW ∈ reifyStep (towerN … 1)`, rank = `towerN` position), the non-injective rank (`ws_witness_rank_noninjective`), and the general theorem D6, reported honestly if it lands.
- **Strip test.** Delete **"attention / knowing / opening / inhabited"** from `ws2_many_witness` and it is the bare fact **"a `reifyStep`-produced relatum carrying a reified constituent and a base relatum are plain-bisimilar (`ws1_atomless_bisim`) yet not label-bisimilar under the rank labelling, on a carrier where rank is coarser than identity, GENERALLY (`ws2_many_general`)"**, a general rank-separation-and-reification fact on a coarse-rank carrier, which is NOT the two-Boolean labelled-separation fact of `ws4_label_survives_quotient` (Finding 1 satisfied; the charter's strip, protocol §0.3, is "a reified relatum and a base relatum, plain-bisimilar, separated by a labelled lift, reification load-bearing"). The mathematical content is a general-separation-and-reification fact; "the many is real / knowing is plural" is the earned interpretive layer, and no name is a term.

## Deliverable

`series-12/formal/Series12/ws2.lean`: the transcribed attention layer + collapse engine + tower (README §6); the four-state `dir := rank` carrier and its lemmas incl. `ws_witness_rank_noninjective` (`ws4-witness-design.md`); `Many` (README §2.8); `ws2_attention_subtractive` (D1), `ws2_many_witness` (D2, the pair `cW` vs `aW`), `ws2_reification_loadbearing` (D3), `ws2_no_import_is_one` (D4), `ws2_distinction_free` (D5), `ws2_many_general` (D6). **Depends on WS1's opening; hosts the witness carrier consumed by WS4.** Axiom check: `#print axioms ws2_many_witness` reduces through `ws1_atomless_bisim` and the finite carrier facts to the standard three. **The opening is inhabitable, the many real on a genuine tower-distinction (a reified relatum carrying a reified constituent, rank non-injective, generalized, NOT a point-tag), the distinction free as its certificate, and without an import the One: the guard against degenerate inhabitation.**
