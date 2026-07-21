> **CORRECTION (finding T1-S1, Tier-1 landing review).** The CONSERVED-RELATIVE design described below was OVERTURNED as a costume: its "in-sight conservation" (`ws2_tick_conserves`) was the collapse engine (a state-bisimilarity holding for any measure), not a `Q`-invariance, and its free-lunch fork was decided by a `Finset.card` counter disconnected from the diagonal. The series was reground to the honest, computed verdict **MONOTONE-ONLY**: the measure `Q := rankM` is non-trivial but RISES under the tick and is not conserved, and conservation-from-within is IMPOSSIBLE (the diagonal is always a source, `ws2_residue_free`). The authoritative record is the built `formal/P2S7/` (verdict `ws5_verdict_eq = monotoneOnly`), `summary.md` / `summary-technical.md`, and `charter-status.md` §4 (T1-S1, T1-A1). The CONSERVED-RELATIVE attempt is on record and checkable in `formal/P2S7/ConservedRelativeAttempt.lean`. This design file is kept as the pre-reground record of the original intent.

---

# WS4 design — the free-lunch crux (the knot) (2.7)

**Prove the fork on self-reference: does the diagonal (the residue, `ws2_residue_free`) CHANGE `Q` with NO external
import — CREATE distinction from within (FREE-LUNCH) — or only RELOCATE distinction already latent (CONSERVED)?
Both readings must be GENUINELY REACHABLE, the verdict discriminating, and the knot must rest on the DIAGONAL being
a source-or-not (the new content), NOT on the mere import-ness of a distinction (Series 07, a costume — charter
§4.b, the costume gate). The load-bearing genuine content is the P1 diagonal: `ws2_residue_free` (the residue is a
real non-recoverable content, produced by self-inspection alone) and `ws1_coincidence_not_identity_witness` (from a
single position the diagonal yields ≥ 2 DISTINCT such contents). Because both readings are reachable and neither
forced, the free-lunch crux is SELF-RELATIVE (the S6 shape).**

## 1. Candidate constructions

1. **Fork on import-ness (a distinction is `¬ Recoverable`).** REJECTED: the costume (charter §4.b). That is Series
   07; it carries no create-or-relocate content. The fork must rest on the DIAGONAL (the residue), self-reference.
2. **FREE-LUNCH by fiat (the diagonal defined to add a unit).** REJECTED: rigged (§4.d). Creation must be a theorem
   about the genuine residue, both sides reachable.
3. **Fork on whether the diagonal's free residue is NEW (beyond the latent budget) or already latent (CHOSEN).** The
   residue is ALWAYS free (`ws2_residue_free`) — self-inspection always yields a genuine non-recoverable content, no
   import crossing. The crux is whether that content is a NET new unit (`Q` rises — FREE-LUNCH) or already latent
   (`Q` unchanged — CONSERVED). Both reachable: FREE-LUNCH witnessed by the diagonal producing ≥ 2 DISTINCT free
   residues from one position (genuine creation of a plurality from within); CONSERVED witnessed by a budget already
   containing the residue's content (relocation, no net increase). Neither forced ⇒ self-relative.

## 2. Triage

- **The knot is the diagonal-as-source, not import-ness (audit c, the costume gate).** Both payoffs quantify over
  the residue / self-inspection (`Hold`, `HoldPred`, `residue`, `ws2_residue_free`,
  `ws1_coincidence_not_identity_witness`) — the P1 diagonal, NOT boundary imports. Strip "creation"/"measure" and the
  content is "self-inspection yields a free residue distinct from another free residue" — a diagonal fact, not an
  import-ness fact (charter §0.3, WS4 annotation).
- **No fiat (audit d).** FREE-LUNCH and CONSERVED both reachable; the measure non-trivial (WS1). Neither is excluded
  by construction.
- **The bookkeeping skeleton, DISCLOSED (finding-style, like S6's meta-flags).** The create-vs-relocate arithmetic is
  carried by a decidable count `Qc B := B.card`, `diagStep B d := insert d B`: FREE-LUNCH is `d ∉ B → Qc` rises;
  CONSERVED is `d ∈ B → Qc` unchanged. The count is the SKELETON (a `decide` fact); the LOAD-BEARING genuine content
  is `ws2_residue_free` and `ws1_coincidence_not_identity_witness`, conjoined in the payoff so the increment is
  REALIZED by a genuine free-residue plurality, not stipulated. This split is disclosed here and in the ledger and
  graded honestly (COSMETIC-disclosed, not hidden), per protocol §0.2/§0.5.
- **Names-not-terms (audit e).** `diagStep`, `Qc`, `ws4_free_lunch_reachable`, `ws4_conserved_reachable`,
  `ws4_crux_both_reachable` embed no forbidden content-word ("creation", "free", "lunch" are prose only).

## 3. Winning construction — typed signatures

```
-- the bookkeeping skeleton (decidable)
def Qc (B : Finset (Fin 2)) : ℕ := B.card
def diagStep (B : Finset (Fin 2)) (d : Fin 2) : Finset (Fin 2) := insert d B

-- an inhabited self-inspecting position on the carrier (a Hold: e0 self-loops)
def h0 {κ} (hinf : ℵ₀ ≤ κ) : Hold (outDest hinf attendsM)

-- FREE-LUNCH reachable: the diagonal is a genuine internal source (≥ 2 distinct free residues, no import),
-- and the count strictly rises (skeleton)
theorem ws4_free_lunch_reachable {κ} (hinf : ℵ₀ ≤ κ) :
    (∃ insp₁ insp₂ : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM),
        ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂)
  ∧ Qc (diagStep ∅ 0) = Qc ∅ + 1

-- CONSERVED reachable: the diagonal relocates onto an already-latent slot, the count unchanged; the residue is
-- still a genuine free content (self-inspection), it simply does not add a NET unit
theorem ws4_conserved_reachable {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)
  ∧ Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2))

-- the crux is self-relative: both reachable, neither forced
theorem ws4_crux_both_reachable {κ} (hinf : ℵ₀ ≤ κ) :
    (Qc (diagStep ∅ 0) = Qc ∅ + 1) ∧ (Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2)))
```

`h0` inhabited because `e0 ∈ (outDest hinf attendsM e0).1` (`attendsM e0 = {e0}`). The two-distinct-free-residues
via `ws1_coincidence_not_identity_witness (outDest hinf attendsM) (h0 hinf)` (the constant-`True`/constant-`False`
inspections, pointwise-opposite residues), each free by `ws2_residue_free`. The count facts by `decide`. The
universal-freeness in CONSERVED is `ws2_residue_free` (relocation does not make the residue recoverable; it just
does not add a net unit).

## 4. Outcome classes

- `freeLunchReachable`, `conservedReachable` are the two WS4 flags (WS5). Both true ⇒ the fork is genuine and
  self-relative ⇒ CONSERVED-RELATIVE (in-sight conserved, import the source, creation open both ways).
- `freeLunchReachable && !conservedReachable` (creation forced) ⇒ FREE-LUNCH: the diagonal a genuine source,
  conservation fails from within, "to relate is to create" as a law — reported in its direction (charter §6).
- `!freeLunchReachable` (no creation side) ⇒ `partial'` (the fork degenerate).
