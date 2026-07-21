> **CORRECTION (finding T1-S1, Tier-1 landing review).** The CONSERVED-RELATIVE design described below was OVERTURNED as a costume: its "in-sight conservation" (`ws2_tick_conserves`) was the collapse engine (a state-bisimilarity holding for any measure), not a `Q`-invariance, and its free-lunch fork was decided by a `Finset.card` counter disconnected from the diagonal. The series was reground to the honest, computed verdict **MONOTONE-ONLY**: the measure `Q := rankM` is non-trivial but RISES under the tick and is not conserved, and conservation-from-within is IMPOSSIBLE (the diagonal is always a source, `ws2_residue_free`). The authoritative record is the built `formal/P2S7/` (verdict `ws5_verdict_eq = monotoneOnly`), `summary.md` / `summary-technical.md`, and `charter-status.md` §4 (T1-S1, T1-A1). The CONSERVED-RELATIVE attempt is on record and checkable in `formal/P2S7/ConservedRelativeAttempt.lean`. This design file is kept as the pre-reground record of the original intent.

---

# WS1 design — the measure `Q`, non-trivial (the risky ground) (2.7)

**DEFINE the measure of distinction `Q := rankM` (the reification rank, the accumulated import-content) on the
witness carrier, and prove it well-defined and NON-TRIVIAL: two configurations with different `Q`, and the
difference a GENUINE import (`AttentionDistinguishes`), so `Q` measures `¬ Recoverable` distinction, not an
arbitrary label. `Q` is defined structurally — with no reference to its conservation (WS2) or its diagonal status
(WS4), which are proved of the independent `Q` — so it is not rigged (charter §4.c, the WS1 watch). This is the
risky ground: the measure had to be FOUND (`measure-derisking.md`, Candidate 1); it was.**

## 1. The witness carrier (shared object, README §3)

`MCar := Fin 4`, with `e0, e0' : MCar` two base relata (rank 0, so rank is NON-INJECTIVE), `e1 := reifyM {e0}` a
reified relatum (rank 1, an actualized tick-product), `e2 := reifyM {e1}` a reified relatum (rank 2) carrying the
reified constituent `e1`. `attendsM`: `e0`,`e0'` self-loop; `e1 → e0`; `e2 → e1` (the pointwise reification
sections `attendsM (reifyM {e0}) = {e0}`, `attendsM (reifyM {e1}) = {e1}`). `rankM`: `e0,e0' ↦ 0`, `e1 ↦ 1`,
`e2 ↦ 2`. The measure lift `destML hinf := rankLift (outDest hinf attendsM) rankM` (transitively `P1.Reader`,
`P2S0`). All four states `SHNE`, so the collapse engine applies.

## 2. Triage

- **The measure is `rankM`, defined structurally (audit b, not rigged).** `Q := rankM : MCar → ℕ` is the tower
  height, fixed with the carrier, with no conservation/rise clause. Non-triviality is a fact about this independent
  `Q`, and so are WS2/WS3/WS4.
- **The value-difference is a genuine distinction, not a label (audit c, not a costume).** `Q e1 ≠ Q e0` is
  witnessed as `AttentionDistinguishes destML e1 e0`: `e1`, `e0` plain-bisimilar (collapse engine) yet
  rank-separated. So a `Q`-difference IS a `¬ Recoverable` import; `Q` measures import-content.
- **Strip test.** `ws1_rank_nontrivial` → "a function on configurations taking two distinct values, the
  difference a plain-bisimilar-yet-label-separated pair" — a bare `AttentionDistinguishes` / inequality fact,
  no interpretive term load-bearing (charter §0.3).
- **Names-not-terms (audit e).** `MCar`, `attendsM`, `rankM`, `reifyM`, `destML`, `e0`…`e2`, `ws1_rank_nontrivial`
  embed no forbidden content-word ("measure", "energy", "conservation", …) as a whole word.

## 3. Winning construction — typed signatures

```
abbrev MCar : Type := Fin 4
def e0 : MCar := 0   def e0' : MCar := 1   def e1 : MCar := 2   def e2 : MCar := 3
def attendsM : MCar → Finset MCar
def rankM : MCar → ℕ                     -- THE MEASURE Q (structural; no conservation clause)
def reifyM : Finset MCar → MCar
noncomputable def destML {κ} (hinf : ℵ₀ ≤ κ) : MCar → LkObj κ (ULift ℕ) MCar   -- rankLift (outDest hinf attendsM) rankM

-- carrier lemmas
lemma attendsM_nonempty : ∀ x : MCar, (attendsM x).Nonempty
lemma SHNE_M {κ} (hinf : ℵ₀ ≤ κ) (x : MCar) : SHNE (outDest hinf attendsM) x
lemma plainOf_rankLiftM {κ} (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) :
    plainOf (rankLift dest lab) = dest
lemma rankLiftM_val {κ} (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) (x : MCar) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift ℕ), z)) '' (dest x).1

-- the section (the tick genuinely reifies; consumed by WS2)
lemma sectionM_e0 : attendsM (reifyM {e0}) = {e0}
lemma reifyM_e0 : reifyM {e0} = e1

-- THE PAYOFF: Q non-trivial, and the difference a genuine import
theorem ws1_rank_nontrivial {κ} (hinf : ℵ₀ ≤ κ) :
    rankM e1 ≠ rankM e0
  ∧ AttentionDistinguishes (destML hinf) e1 e0
  ∧ (∃ x y : MCar, rankM x ≠ rankM y)      -- Q not constant
```

`AttentionDistinguishes (destML hinf) e1 e0` proved as in `firstOther_label_sep`: plain side via
`plainOf_rankLiftM` + `ws1_atomless_bisim` (both `SHNE`); label side by the rank gap (`rankM e1 = 1 ≠ 0 = rankM e0`
forces the labelled edge coords apart). `∃ x y, rankM x ≠ rankM y` by `⟨e1, e0, by decide⟩`.

## 4. Outcome classes

- If NO non-trivial measure survived the de-risking (it did): DISCONNECTED (charter §6). Not reached.
- `ws1_rank_nontrivial` is the ground the whole verdict stands on: `!nonTrivial` in `verdict` returns
  `disconnected` (WS5).
