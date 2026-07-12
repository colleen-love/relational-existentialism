# WS2 — Knowing: finite attention, and the opening inhabited

**Design doc. Series 12, the formalizable side, the plurality. Owns: finite attention (subtractive, plural, no attention holding the whole) and the proof that the opening is INHABITABLE and that inhabitation makes the many real — `Many` on the concrete rank-labelled tower, where a reified relatum and a base relatum are genuinely plain-bisimilar (the collapse engine merges them) yet separated at the labelled level by their tower RANK, `reify`/`reifyStep`/`towerN` load-bearing; and without any import, the One (`ws1_atomless_bisim`). The distinction is non-recoverable, which by Series 07 is its CERTIFICATE, not its defect. WS2 is the guard against degenerate (point-tag) inhabitation.**

*Series 12 is standalone; finite attention (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `ws3_no_total_attention`), the collapse engine (`ws1_atomless_bisim`, `ws2_import_theorem_static`), and the tower (`reifyStep`, `towerN`, `ws3_reify_preserves_SHNE`) are transcribed into `series-12/formal/Series12/ws2.lean`, re-namespaced `Series12.WS2` (see `spec/README.md` §6). WS2 DEFINES `Many` (README §2.8) and hosts the concrete carrier of `spec/ws4-witness-design.md` (the `dir := rank` witness). It CONSUMES WS1's opening (`Opening`, `¬ Recoverable`); it does not redraw it. The genuinely new Lean is `Many`, `ws2_many_witness`, and the load-bearing certificate `ws_witness_reification_loadbearing`. The one signature risk is degenerate inhabitation (discipline 4): a bare point-tag with no tower content, the Bookkeeping re-hit Series 10 and 11 landed on.*

## The object at stake

The charter's WS2 (§2): the opening is INHABITABLE, and any inhabitant makes the many real. Two facts, one carrier. (1) **Inhabitability with plurality:** adjoin an inhabitant as a labelled direction over the plain structure (the labelled lift, with the plain quotient forgetting it), and prove `Many`: a reified tower relatum and a base relatum genuinely plain-bisimilar (the Series 07 engine merges them, `ws1_atomless_bisim`) yet separated at the labelled level, the reification facts LOAD-BEARING, generalized across the tower. (2) **Without an import, the One:** `ws2_import_theorem_static` — a plain, behaviorally-identified, atomless coalgebra is a subsingleton. The plurality's distinction is non-recoverable (`ws1_attention_distinction_free`), which is its CERTIFICATE: by Series 07 (WS1's required half) a genuine atomless distinction MUST be non-recoverable, so non-recoverability is the sign the distinction is real, not the sign it cheats.

The design's whole burden is discipline 4, and it is the program's gravest inherited risk. Series 10 (`ws2_reify_bisim_embeds`) and Series 11 (`ws1_attention_makes_real`) both drew their distinction on `labelLoop` — two fixed Booleans where `reify`/`reifyStep`/`towerN` never occur — and were honestly re-graded Bookkeeping re-hit. **WS2 must not repeat that:** the separated pair is a genuine reified relatum `reifyW sW` and its base constituent `aW`, and the label is the tower RANK (`dir := rank`), defined from `towerN`/`reifyStep`. The witness is fully designed in `spec/ws4-witness-design.md`; WS2 states the plurality it discharges.

**Ambient theory.** `spec/README.md` §2.1 (collapse engine), §2.6 (finite attention), §2.8 (`Many`); the witness carrier (`ws4-witness-design.md`).

## Candidates

### C1 — Finite attention is subtractive and never total (the formal side, transcribed)

```lean
/-- **Attention is subtractive and never total.** Every finite attention reads a bounded part (`att.fin`);
    NO attention holds the whole (`ws3_no_total_attention` = the diagonal at tower scale), so no
    self-definition closes — the residue is always past the bound. -/
theorem ws2_attention_subtractive {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t)
  ∧ (∀ h : Hold dest, insp h ≠ residue insp) :=
  ⟨ws3_no_total_attention dest insp, ws2_residue_distinct dest insp⟩
```
Knowing is bounded: attention reads a finite part, no attention totalizes, the residue is always outside the bound.

- **Ambient:** `ws3_no_total_attention`, `ws2_residue_distinct`, `FiniteAttention.fin`.
- **Success condition (Discharged, transcribed):** the term typechecks — the subtractive, never-total character of knowing, transcribed from the diagonal.
- **Failure mode:** *none — transcription.* **Winner (the formal side).**

### C2 — `Many` on the rank witness (the plurality; the payoff)

```lean
/-- **THE PLURALITY (`Many`, on a genuine tower-distinction).** On the rank-labelled tower a reified relatum
    `bW = reifyW sW` and a base relatum `aW` are plain-bisimilar (the collapse engine is blind) yet
    rank-separated at the labelled level — the many is real, `reify`/`reifyStep`/`towerN` load-bearing. -/
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) :=
  ⟨aW, bW, ws1_atomless_bisim _ aW bW (ws_witness_SHNE hinf).1 (ws_witness_SHNE hinf).2,
   ws_witness_rank_separates hinf⟩
```
The inhabited opening: `Many destWL` (README §2.8), discharged on the `dir := rank` carrier. Plain-bisimilar (`ws1_atomless_bisim` — the engine merges the reified relatum and the base relatum) yet not label-bisimilar (their broadcast ranks `⟨0⟩`, `⟨1⟩` mismatch).

- **Ambient:** `Many`, `ws1_atomless_bisim`, `ws_witness_rank_separates`, the witness carrier.
- **Success condition (Shape-drawn on the witness):** `Many destWL` holds with the separated pair a genuine reified relatum vs a base relatum.
- **Failure mode:** *degenerate inhabitation (discipline 4), the gravest.* If the separating direction were a bare point-indicator (a tag on one distinguished element carrying no tower content, `labelLoop`), the opening would be inhabitable only degenerately. C2 forecloses it via C3. **Winner (the plurality).**

**Paper triage.** Decidable: `ws1_atomless_bisim` merges the two `SHNE` relata (plain side); the rank labels `⟨0⟩ ≠ ⟨1⟩` block every label-bisimulation (labelled side). **Winner.**

### C3 — The reification is load-bearing (the anti-point-tag certificate)

```lean
/-- **REIFICATION LOAD-BEARING (the certificate the review greps for).** The separated relatum is a genuine
    reified relatum, adjoined by `reifyStep` at tower rank 1, `dest (reify sW) = sW` pointwise — NOT a fixed
    Boolean. This is what `labelLoop` lacked. -/
theorem ws2_reification_loadbearing (hinf : ℵ₀ ≤ κ) :
    bW = reifyW hinf (sW hinf)
  ∧ bW ∈ reifyStep (destW hinf) (reifyW hinf) {aW}
  ∧ destW hinf (reifyW hinf (sW hinf)) = (sW hinf).1
  ∧ aW ∈ (sW hinf).1 :=
  ws_witness_reification_loadbearing hinf
```
The certificate that C2's inhabitation is genuine: the separated relatum IS a `reifyStep`-produced reified relatum, its rank IS its `towerN` position, `reify`/`reifyStep`/`towerN` all occur and are load-bearing.

- **Ambient:** `reifyStep`, `reify_mem_reifyStep`, `towerN`, the pointwise reification facts.
- **Success condition (Shape-drawn):** `reify`/`reifyStep`/`towerN` occur load-bearing; the label is the tower rank, not a fresh index.
- **Failure mode:** *the label judged external to the tower (point-tag), Partial.* Foreclosed: `bW ∈ reifyStep {aW}` and the rank = `towerN` position tie the label to the tower's own structure. **Winner (the anti-point-tag certificate).**

**Paper triage.** Decidable: `bW = reifyW {aW}` and `bW ∈ reifyStep {aW}` by `reify_mem_reifyStep`; the rank is the `towerN 1` position. **Winner.**

### C4 — Without an import, the One (the collapse side, transcribed)

```lean
/-- **WITHOUT AN IMPORT, THE ONE.** A plain, behaviorally-identified, atomless coalgebra is a subsingleton —
    strip the labelled direction and the collapse engine returns monism (`ws2_import_theorem_static`). -/
theorem ws2_no_import_is_one {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ws2_import_theorem_static dest hbehav hatom
```
The other side of the two-sided plurality: WITHOUT the imported direction, the plain atomless structure collapses to the One. This is genuine Series 07 (`ws1_atomless_bisim` under behavioral identity), not a rigged collapse.

- **Ambient:** `ws2_import_theorem_static`, `ws1_atomless_bisim`.
- **Success condition (Discharged, transcribed):** the collapse holds — the many needs the import; without it, the One.
- **Failure mode:** *the collapse rigged.* Foreclosed: it is genuine `ws2_import_theorem_static` (Series 07's floor). **Winner (the collapse side).**

### C5 — The distinction is free, its certificate (discipline the review runs)

```lean
/-- **THE DISTINCTION IS FREE (its certificate, not its defect).** The rank-separation is not recoverable
    from the plain relating: an import, which by Series 07 (WS1's required half) is what a genuine atomless
    distinction MUST be. Non-recoverability is the certificate. -/
theorem ws2_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (destWL hinf) := …
```
The certificate: the plurality's distinction is `¬ Recoverable`. By WS1's required half, a genuine atomless distinction is non-recoverable; so this is the sign the distinction is real, not the sign it cheats — the lesson the whole series turns on.

- **Ambient:** `Recoverable`, `plainOf`, the rank-separation, `ws1_attention_distinction_free` (the shape).
- **Success condition (Shape-drawn):** `¬ Recoverable destWL` — the distinction is free, its certificate.
- **Failure mode:** *reading non-recoverability as a defect.* Foreclosed by WS1: non-recoverability is what a genuine distinction must be. **Winner (the certificate).**

### C6 — Generalization across the tower (the reach beyond one relatum)

```lean
/-- **Generalized across the tower.** Any reified relatum carrying a reified constituent separates from a
    base relatum: the plurality is not one lucky pair — every `reifyStep`-adjoined relatum with a base
    constituent is plain-bisimilar to it yet rank-separated. (Discharged on the witness; the fully universal
    form over every κ-free tower is WS6's ceiling.) -/
theorem ws2_many_general (hinf : ℵ₀ ≤ κ) (s : PkObj κ X) (hs : s.1 ⊆ {aW}) (hne : s.1 ≠ ∅) :
    (∃ R, IsBisim (destW hinf) R ∧ R (reifyW hinf s) aW)                    -- plain-bisimilar …
  ∧ (reifyW hinf s) ∈ reifyStep (destW hinf) (reifyW hinf) {aW} := …        -- … and reifyStep-adjoined
```
The reach beyond one relatum: the separation family is parameterized by the reifiable pattern `s`, so it is the reification structure (not one point) doing the work.

- **Ambient:** `ws1_atomless_bisim`, `reify_mem_reifyStep`, `ws3_reify_preserves_SHNE`.
- **Success condition (Shape-drawn on the witness / Partial universal):** the separation generalizes over reifiable patterns; the fully universal form is WS6's ceiling.
- **Failure mode:** *the family collapses to one tag.* Foreclosed: parameterized by `s`, with `reify`/`reifyStep` load-bearing in each. **Winner (the generalization, Partial in the universal).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | attention subtractive, never total | `ws3_no_total_attention`, `ws2_residue_distinct` | yes — transcribed | **win (formal side)** |
| C2 | `Many` on the rank witness | `ws1_atomless_bisim`, `ws_witness_rank_separates` | yes — merge + rank mismatch | **win (plurality)** |
| C3 | reification load-bearing | `reifyStep`, `reify_mem_reifyStep`, `towerN` | yes — `bW ∈ reifyStep {aW}` | **win (anti-point-tag)** |
| C4 | without an import, the One | `ws2_import_theorem_static` | yes — transcribed | **win (collapse side)** |
| C5 | the distinction is free (certificate) | `Recoverable`, `plainOf` | yes — rank not recoverable | **win (certificate)** |
| C6 | generalized across the tower | `ws1_atomless_bisim`, `reify_mem_reifyStep` | yes (witness) / Partial (universal) | **win (generalization)** |

## Winning candidates: C1–C6

### Definitions and obligations (cite `spec/README.md` §2.6, §2.8; consume the witness carrier)

```lean
namespace Series12.WS2
-- FiniteAttention, AttentionDistinguishes, RealFor, TotalAttention, ws3_no_total_attention,
-- ws2_residue_distinct, ws1_atomless_bisim, ws2_import_theorem_static, reifyStep, reify_mem_reifyStep,
-- towerN, ws3_reify_preserves_SHNE, Recoverable, plainOf — transcribed (README §6).
-- The dir:=rank carrier (X, aW, bW, destW, sW, reifyW, dirOf, destWL) and its lemmas — spec/ws4-witness-design.md.

/-- **The plurality predicate, defined once (README §2.8).** -/
def Many {Q X : Type u} (destL : X → LkObj κ Q X) : Prop :=
  ∃ x y : X, (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)

-- D1 ws2_attention_subtractive (C1) ; D2 ws2_many_witness (C2) ; D3 ws2_reification_loadbearing (C3) ;
-- D4 ws2_no_import_is_one (C4) ; D5 ws2_distinction_free (C5) ; D6 ws2_many_general (C6).
```

**Proof architecture.** D1 (subtractive, never total) transcribes the diagonal at tower scale. D2 (`Many`) is the payoff: plain-bisimilar (the engine) ∧ rank-separated (the labelled level), discharged on the `dir := rank` carrier. D3 certifies the inhabitation is genuine: the separated relatum is a `reifyStep`-produced reified relatum, its rank its `towerN` position — the anti-point-tag guard the review greps for. D4 (the One) transcribes `ws2_import_theorem_static`: without the import, monism. D5 certifies the distinction free (`¬ Recoverable`), its certificate by WS1's required half. D6 generalizes across the tower. **Dependencies:** WS1's opening (the `¬ Recoverable` shape D5 inhabits); the witness carrier (`ws4-witness-design.md`); `ws1_atomless_bisim` and `ws2_import_theorem_static` (Series 07 floor). The disclosed pointwise-`IsReify` deviation is carried from the witness (README §2.5).

## Outcome classes (per charter §5)

- **Shape-drawn on the witness (the payoff):** D2 (`ws2_many_witness`), D3 (`ws2_reification_loadbearing`), D5 (`ws2_distinction_free`) — the opening inhabitable, the many real, on a genuine tower-distinction with reification load-bearing, the distinction free as its certificate. The genuine tower-distinction Series 10 and 11 could not draw.
- **Discharged (transcribed):** D1 (subtractive/never-total), D4 (the One without an import).
- **Partial (pre-registered, discipline 4):** the fully universal "every `reifyStep`-produced relatum on every κ-free tower is separated by some finite attention" is the un-rangeable quantifier; D2–D6 deliver a witness and a witnessed generalization, the universal a WS6 thesis. And if a reviewer judges the rank label external to the tower, the inhabitation is a point-tag and the finding demotes to Partial — foreclosed by D3 (`bW ∈ reifyStep {aW}`, rank = `towerN` position), reported honestly if it lands.
- **Strip test.** Delete **"attention / knowing / opening / inhabited"** from `ws2_many_witness` and it is the bare fact **"a `reifyStep`-produced relatum and a base relatum are plain-bisimilar (`ws1_atomless_bisim`) yet not label-bisimilar under the rank labelling, `reify`/`reifyStep`/`towerN` load-bearing"** — exactly the plurality strip the charter demands (protocol §0.3: the plurality should strip to "a reified relatum and a base relatum, plain-bisimilar, separated by a labelled lift, reification load-bearing"). The mathematical content is a reification-and-bisimulation fact; "the many is real / knowing is plural" is the earned interpretive layer, and no name is a term.

## Deliverable

`series-12/formal/Series12/ws2.lean`: the transcribed attention layer + collapse engine + tower (README §6); the `dir := rank` carrier and its lemmas (`ws4-witness-design.md`); `Many` (README §2.8); `ws2_attention_subtractive` (D1), `ws2_many_witness` (D2), `ws2_reification_loadbearing` (D3), `ws2_no_import_is_one` (D4), `ws2_distinction_free` (D5), `ws2_many_general` (D6). **Depends on WS1's opening; hosts the witness carrier consumed by WS4.** Axiom check: `#print axioms ws2_many_witness` reduces through `ws1_atomless_bisim` and the finite carrier facts to the standard three. **The opening is inhabitable, the many real on a genuine tower-distinction (reification load-bearing, NOT a point-tag), the distinction free as its certificate, and without an import the One — the guard against degenerate inhabitation.**
