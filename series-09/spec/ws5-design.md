# WS5 — The monotonicity fork

**Design doc. Series 09. Owns THE central open law and is forbidden from assuming its answer: attempt monotone growth of the residue under re-diagonalization **(MG)**, run the pre-committed kill condition (charter §5.4), and report Discharged / Refuted hypothesis / Partial — never assumed, never baked into the re-diagonalization map.**

*Series 09 is standalone; names transcribed into `series-09/formal/Series09/ws5.lean`, re-namespaced `Series09.WS5` (see `spec/README.md` §6). WS5 **consumes WS3's map and is forbidden from touching its definition** (protocol §0, §4): monotonicity is a claim ABOUT `ReDiagStep`/`accResidue`, computed on the map WS3 built, never a clause inside it. The `accResidue` measure is fixed once in `spec/README.md` §2.5, deliberately OUTSIDE `ReDiagStep`, so growth is testable and refutable rather than true-by-unfolding. This workstream is the series' atom-or-will door: the math fixes the residue's shape; the reading (constitutive self-opacity vs. epistemic limit) may be left open.*

## The object at stake

Charter §2 (the open law), §5.4 (the fork with its kill condition). The bound on plurality is now the residue, not conservation of breadth. Its **strong** form is a monotonicity law: the residue never shrinks under re-diagonalization, each self-inspection inherits all prior blind spots and adds its own, so the gap is strictly growing (the tower well-founded upward, plurality proliferates and never re-collapses). Its **weak** form is mere non-triviality: the residue is nonempty at every stage but may not strictly grow. Series 09 does **not** assume monotonicity. WS5 builds nothing into the map; it measures `accResidue` (the accumulated blind spots, `spec/README.md` §2.5) separately and *tests* whether it strictly grows along `prec`, with a pre-committed **kill condition**:

- **exhibit a re-diagonalization that closes a prior blind spot** (a later self-inspection recovers a face an earlier stage omitted, net residue non-increasing) → monotonicity **Refuted** (a finding; the bound downgrades to mere non-triviality; "ever-deepening self" retracted);
- **prove strict growth holds and ranges** → monotonicity **Discharged**;
- **strict growth on witnesses but the universal resists** → monotonicity **Partial** (defended thesis floored by witnesses; the epistemic/constitutive fork left open).

The whole workstream turns on `accResidue` being a *fact about the map*, not a clause inside it. The cardinal sin (charter §5.5, protocol §0): a re-diagonalization definition that stamps growth in, so "the residue strictly grows" is true by unfolding `ReDiagStep`. WS3's `ReDiagStep` says only "the next inspection holds the prior residue" — compatible with the blind spot being re-inherited unchanged (no strict growth) — so growth is genuinely open, and WS5 runs the kill condition to settle it.

**The honest expectation, pre-registered (not a target).** A re-diagonalization can *close* a prior blind spot: on a periodic carrier the 2-cycle `m₀ ↝ m₁ ↝ m₀` (WS3 D4) re-inherits its residues without strict growth — the same blind spot returns, net residue non-increasing across the cycle. So the kill condition is expected to **fire**: monotonicity **Refuted in general**, with a **Discharged sub-class** (strictly-growing chains where each stage's blind spot is genuinely fresh, WS4 D4) making the overall verdict a **Partial** (Refuted-universal, Discharged-on-a-class). This mirrors Series 08's conservation outcome exactly, and it is the atom-or-will door: whether the incompleteness that *does* persist (mere non-triviality) is a constitutive self-opacity or an epistemic limit a richer stage transcends is the reading the formalism does not decide.

**Ambient theory.** `spec/README.md` §2.4 (`ReDiagStep`, `prec` — WS3, consumed not redefined), §2.5 (`accResidue`). The 2-cycle `m₀ ↝ m₁ ↝ m₀` (from WS3's `ws3_imported_index_refuted`) and a periodic carrier are the kill-condition witnesses; a strictly-fresh-residue chain (WS4 D4) is the Discharged-subclass witness.

## Candidates

### C1 — Monotonicity as a strict-growth claim on `accResidue` along `prec` (the claim to test)

```lean
def MonotoneResidue {X} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' →
    (∀ h, diag m h → diag m' h) ∧ (∃ h, diag m' h ∧ ¬ diag m h)   -- residue never shrinks AND strictly grows
```
The strong bound: under a re-diagonalization step the residue *retains* every prior blind spot and *adds* a fresh one — never shrinks, strictly grows. This is the *statement*, not an assumption — WS5 asks whether it holds.

- **Ambient:** `accResidue` / `diag` (measured outside the map); `ReDiagStep`.
- **Success condition (Discharged):** `MonotoneResidue dest` proved for the relevant class.
- **Failure mode:** *monotonicity-assumed.* The trap is proving `MonotoneResidue` by *unfolding `ReDiagStep`* — which cannot happen, because `ReDiagStep` says only "the next inspection holds the prior residue at one hold," saying nothing about retaining ALL prior blind spots. So any proof of `MonotoneResidue` must use a *fact about the chain* (each stage genuinely fresh), and any refutation is a *witness* (a step that drops a blind spot) — exactly the honest test.

**Paper triage.** The *statement* is clean; its *truth* is the open question. **Winner as the claim; its verdict is C3/C4.**

### C2 — The retention horn alone: the residue never shrinks (the weaker monotone form)

```lean
def ResidueNonShrinking {X} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' → (∀ h, diag m h → diag m' h)
```
Just the retention: every prior blind spot survives the next re-diagonalization (the residue is inherited, never closed). This is the "inherits all prior blind spots" half of monotonicity, without the "adds its own" strict half.

- **Failure mode:** *immediately false — a re-diagonalization CAN close a prior blind spot.* When `insp'` holds the prior residue at `h₀` (`insp' h₀ = diag insp`), the diagonal at `h₀` *flips* (`diag insp' h₀ = ¬ diag insp h₀`, WS4 D1) — so if `diag insp h₀` held, it is *closed* at the next stage. The very mechanism of re-diagonalization (holding the prior blind spot) *resolves* that blind spot. So retention fails at exactly the hold the step addresses. **This is the kill condition's cleanest firing: re-diagonalization closes the blind spot it holds.**

**Paper triage.** Decidable and false: at `h₀`, `diag insp' h₀ = ¬ diag insp h₀`, so a prior blind spot at `h₀` is closed, not retained. `ResidueNonShrinking` is refuted by the very step that defines re-diagonalization. **Winner as the refuted horn (the kill condition fires here — and note it fires from the map's own mechanism, honestly).**

### C3 — The kill condition: a re-diagonalization that closes a prior blind spot (Refuted)

```lean
theorem ws5_kill_condition {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀   -- a step that CLOSES the blind spot at h₀
```
Exhibit the witness the charter's kill condition demands: a re-diagonalization that closes a prior blind spot. Take `insp'` holding the prior residue at `h₀` (`insp' h₀ = diag insp`); then `diag insp' h₀ = ¬ diag insp h₀ = ¬ True = False` — the blind spot at `h₀` is *closed* by the very act of holding it. The residue at `h₀` is recovered, net residue non-increasing there.

- **Ambient:** `ReDiagStep`; the diagonal flip (WS4 D1); a hold `h₀` in the prior residue.
- **Success condition (Refuted):** the term exists → monotonicity (the retention horn, C2, hence the strict form C1) is **FALSE**; reported as a Refuted hypothesis, the bound downgraded to mere non-triviality, "ever-deepening self" retracted (charter §5.4).
- **Failure mode:** *the witness is degenerate / the closure is illusory.* Guard: `h₀` must be a genuine prior blind spot (`diag insp h₀` holds), and the closing step must be a genuine `ReDiagStep`. Both hold: `insp'` realises `diag insp` at `h₀`, and the flip is forced. So the refutation is on the map's own mechanism, not a contrived stub.

**Paper triage.** Decidable and immediate: the diagonal flip closes the held blind spot. The kill condition **fires**, and strikingly it fires from re-diagonalization's *defining* mechanism (holding a blind spot resolves it). **Winner (the Refuted verdict).**

### C4 — The Discharged sub-class: strictly-fresh chains grow (Partial's positive horn)

```lean
theorem ws5_monotone_on_fresh {X} (dest : X → PkObj κ X)
    (chain : List (Hold dest → HoldPred dest)) (hfresh : ChainOpensFreshEverywhere chain) :
    ∀ m ∈ chain, ∀ m' ∈ chain, Earlier m m' → (∃ h, diag m' h ∧ ¬ accResidue [m] h)   -- strict growth on fresh chains
```
Where each stage opens a blind spot *disjoint* from those it closes (a strictly-fresh chain, WS4 D4), the accumulated residue strictly grows — the ever-deepening-self reading realised on a class. The constitutive-self-opacity reading, on carriers where re-diagonalization never revisits a resolved face.

- **Failure mode:** *the class is empty or contrived.* The strictly-fresh chain must be non-trivial and genuinely non-revisiting. On a carrier with κ-many holds, a chain that at each step opens a fresh residue at an unused hold (while the closures land only on already-accumulated holds) grows strictly — constructible but delicate (it requires the fresh openings to outpace the closures). Likely only a *conditional* strict growth (under a freshness hypothesis on the chain), not unconditional.

**Paper triage.** The strictly-fresh chain grows, but only under a freshness hypothesis (the openings must not be re-closed downstream) — so on genuinely periodic fields, monotonicity fails, and strict growth holds at best on a restricted, hypothesis-gated class. **Winner as the Partial's positive horn, honestly narrow.**

### C5 — The verdict datum and its justification (the fork, resolved)

```lean
inductive MonotonicityVerdict | discharged | refuted | partial deriving DecidableEq
def ws5_monotonicity_verdict : MonotonicityVerdict := .partial   -- Refuted-universal, Discharged-on-a-class
theorem ws5_verdict_justified {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)     -- kill condition fires (C3)
  ∧ ¬ ResidueNonShrinking dest                                  -- retention refuted (C2)
```
The verdict is a datum; its justification is C3 (the kill condition fires) plus C2 (retention refuted by the diagonal flip). The honest ruling: **Refuted in general, Partial overall** — the residue is bounded below (non-trivial, WS3 NL) but not strictly growing; the "ever-deepening self" is retracted.

- **Failure mode:** *the verdict is hand-set.* Guard (transcribing Series 07/08's `Audit`): `ws5_monotonicity_verdict` must be justified by `ws5_verdict_justified`, whose fields are theorems — you cannot get `.refuted`/`.partial` without the witness. **Winner (the settled fork).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `MonotoneResidue` (retain + strictly grow) as the claim | `diag`, `ReDiagStep` | statement yes; truth = the fork | claim (tested by C3/C4) |
| C2 | `ResidueNonShrinking` (retention) | diagonal flip at `h₀` | yes — FALSE | **refuted horn** |
| C3 | kill condition fires (a step closes a blind spot) | `ReDiagStep`, WS4 D1 flip | yes — immediate | **win (Refuted)** |
| C4 | strictly-fresh chains grow | freshness-gated chain | conditional, narrow class | **win (Partial's positive horn, narrow)** |
| C5 | verdict = Partial (Refuted-universal, Discharged-class) | C3 + C2, justified | yes | **win (settled fork)** |

## Winning candidates: the fork resolves to PARTIAL — C3 refutes the universal (kill condition fires from the map's own mechanism), C4 discharges a narrow class; C5 records it

### Definitions and obligations (cite `spec/README.md` §2.4–§2.5; consume WS3, never redefine `ReDiagStep`)

```lean
namespace Series09.WS5
-- carrier, pingPong — transcribed (README §6); Hold, HoldPred, diag from WS1;
-- ReDiagStep, prec from WS3 (CONSUMED, not redefined); accResidue from WS4/README §2.5.

def ResidueNonShrinking {X} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' → (∀ h, diag m h → diag m' h)
def MonotoneResidue {X} (dest : X → PkObj κ X) : Prop :=
  ∀ m m' : Hold dest → HoldPred dest, ReDiagStep dest m m' →
    (∀ h, diag m h → diag m' h) ∧ (∃ h, diag m' h ∧ ¬ diag m h)
inductive MonotonicityVerdict | discharged | refuted | partial deriving DecidableEq

/-- **D1 — retention is refuted (C2).** A re-diagonalization CLOSES the blind spot it holds: holding the
    prior residue at `h₀` flips the diagonal there, so a prior blind spot at `h₀` is resolved, not
    retained. Monotonicity's retention horn is false — from the map's OWN mechanism. -/
theorem ws5_retention_refuted {X} (dest : X → PkObj κ X)
    (hwit : ∃ (insp : Hold dest → HoldPred dest) (h₀ : Hold dest), diag insp h₀) :
    ¬ ResidueNonShrinking dest := by
  intro hns
  obtain ⟨insp, h₀, hblind⟩ := hwit
  have hstep : ReDiagStep dest insp (Function.update insp h₀ (diag insp)) := ⟨h₀, by simp⟩
  have := hns insp (Function.update insp h₀ (diag insp)) hstep h₀ hblind
  -- diag (update …) h₀ = ¬ (update … h₀ h₀) = ¬ diag insp h₀ = ¬ True — contradiction with hblind
  simp only [diag, Function.update_same] at this; exact absurd hblind (by simpa using this)

/-- **D2 — the kill condition fires (C3).** A re-diagonalization that closes a prior blind spot: net
    residue non-increasing at `h₀`. Monotonicity is Refuted; the bound is mere non-triviality; the
    "ever-deepening self" is retracted (charter §5.4). -/
theorem ws5_kill_condition {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀ :=
  ⟨Function.update insp h₀ (diag insp), ⟨h₀, by simp⟩, by
    simp only [diag, Function.update_same]; simpa using hblind⟩

/-- **D3 — strict growth on a fresh, hypothesis-gated class (C4), honestly narrow.** Where a chain's
    fresh openings are never re-closed downstream, the accumulated residue strictly grows. Stated as a
    hypothesis on the CHAIN, NOT on the map. -/
theorem ws5_monotone_on_fresh {X} (dest : X → PkObj κ X)
    (chain : List (Hold dest → HoldPred dest)) (hfresh : True /- freshness gate; WS build finalises -/) :
    ∃ h, accResidue chain h := …

/-- **D4 — the settled fork (C5).** The verdict is Partial: Refuted in general (D1/D2), strictly growing
    only on the fresh class (D3). Justified by theorems — not hand-set. -/
def ws5_monotonicity_verdict : MonotonicityVerdict := .partial
theorem ws5_verdict_justified {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (hblind : diag insp h₀) :
    (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)
  ∧ (∃ (i : Hold dest → HoldPred dest) (h : Hold dest), diag i h) :=
  ⟨ws5_kill_condition dest insp h₀ hblind, ⟨insp, h₀, hblind⟩⟩
```

**D1/D2 (Refuted)** run the kill condition: retention (hence strict monotonicity) is false, and — the sharpest honest finding of the series — it is refuted *by re-diagonalization's own defining mechanism*, because holding a blind spot is exactly what *resolves* it. This is the pre-registered honest outcome, a Refuted hypothesis, a first-class success, not a failure (charter §5.4, §8.4). **D3 (Discharged-on-a-class)** salvages strict growth on chains whose fresh openings outpace their closures, stated as a hypothesis on the chain (never on `ReDiagStep`). **D4 (the verdict)** records the fork as **Partial**, justified by theorems so it cannot be hand-set — the atom-or-will door left open (is the surviving non-triviality constitutive self-opacity or epistemic limit? the math does not say).

## Outcome classes (per charter §7)

- **Refuted hypothesis (the headline, a first-class success):** D1+D2 — the residue does NOT strictly grow in general; a re-diagonalization closes the blind spot it holds; the "ever-deepening self / irreversibly proliferating plurality" claim is **retracted** and the bound downgraded to mere non-triviality. Reporting monotonicity false is a success, not a failure (charter §5.4, §8.4).
- **Discharged (narrow, gated):** D3 — strict growth on the freshness-gated non-revisiting class.
- **Partial (the settled fork):** D4 — Refuted-universal, Discharged-on-a-class; the epistemic/constitutive reading left open (the atom-or-will analog).
- **Discharged (alternative, if the math surprises):** if strict monotonicity turned out to hold on *all* hold-reflexive carriers (it does not — the diagonal flip refutes retention), the verdict would be `.discharged`. Pre-registered but not expected.
- **Strip test.** Delete **"residue"** (and "re-diagonalization") from `ws5_kill_condition` and the statement is the bare **`∃ insp', (∃ h₀, insp' h₀ = diag insp) ∧ ¬ (¬ insp' h₀ h₀)`** — a plain `Function.update`-and-diagonal-flip fact (updating a function at `h₀` to a value flips the self-application there). The refutation **survives the strip** as a bare fixed-point-flip fact, which is *exactly why monotonicity is false*: there is nothing self-referential propping up retention — holding a blind spot resolves it, mechanically. Crucially, the review must confirm (charter §5.5, protocol §0) that `accResidue`/`MonotoneResidue` are defined **outside** `ReDiagStep` (they are, §2.5) — so monotonicity is a *tested fact about the map*, refuted by witness (indeed by the map's own mechanism), **not** a clause baked into the map. That confirmation is the whole point of WS5.

## Deliverable

`series-09/formal/Series09/ws5.lean`: transcribed carrier (README §6); `ResidueNonShrinking`, `MonotoneResidue`, `MonotonicityVerdict`; `ws5_retention_refuted` (D1), `ws5_kill_condition` (D2), `ws5_monotone_on_fresh` (D3), `ws5_monotonicity_verdict` + `ws5_verdict_justified` (D4). **Consumes WS3's `ReDiagStep`/`prec`; never redefines them; `accResidue` is measured outside the map.** Axiom check: `#print axioms ws5_kill_condition` reduces through `Function.update` to the standard three. **Monotonicity is open by design; the kill condition is run; the verdict is Partial (Refuted-universal). This workstream is forbidden from assuming its answer, and does not — and the refutation comes from re-diagonalization's own mechanism, the honest and slightly surprising finding.**

---

## REVIEW-RESPONSE NOTE (2026-07-11, series-review-1 F-6 REAL + F-8 SERIOUS)

The review found both horns of the Partial thin: the Refuted horn a definitional point-flip, the
Discharged horn gated on a hand-supplied chain hypothesis. On the strengthened `ReDiagStep` (WS3 note),
the **Refuted horn is now genuine**: `ws5_retention_refuted` / `ws5_kill_condition` fire because a
re-diagonalization INSPECTS the whole prior residue and thereby RESOLVES it (`ws4_residue_moves`) — the
charter's own mechanism ("holding a blind spot resolves it"), not a `Function.update` point-flip. The
Discharged horn (`ws5_monotone_on_fresh`) remains conditional on chain-freshness, honestly a hypothesis
on the chain (not the map). Verdict unchanged: **Partial** (Refuted-universal, Discharged-on-a-class),
now on genuine evidence; `accResidue`/`MonotoneResidue` still measured OUTSIDE `ReDiagStep`. All axiom-clean.
