# WS4 — The tower and depth

**Design doc. Series 9, layering. Owns: depth is the accumulation of blind spots (each re-diagonalization opens a new face the prior stage could not see), and reachability-into-depth as the trace of a re-diagonalization sequence, derived not axiomatic. Discharged on witnesses; the universal form ("all depth is diagonal residue, across any construction") is a pre-registered Partial (charter §5.3).**

*Series 9 is standalone; names transcribed into `series-9/formal/Series9/ws4.lean`, re-namespaced `Series9.WS4` (see `spec/README.md` §6). WS4 **consumes WS3** (protocol §4): the re-diagonalization map `ReDiagStep` and the order `prec` are WS3's, fixed once in `spec/README.md` §2.4; WS4 does not redefine them. The fresh-residue lemma routed here from WS3 (candidate C5) is WS4's depth content. The genuinely new Lean is `ws4_new_blind_spot` (the diagonal always escapes its enumeration) and the tower/trace theorems.*

## The object at stake

Charter's Consequence 3 (§2, §5.3). Re-inspection is *directed*: each stage resolves a face by opening a new blind spot (the diagonal always escapes the enumeration it is run against). Depth is the accumulation of successive blind spots, the transfinite tower of "the truth this stage cannot see" — **not** the narrowing of a hold (Series 8's reading) but the *proliferation* of unseen faces. A hold that could see all at once would be the self-total hold, which does not exist (WS1); layering exists BECAUSE self-inspection is incompletable and must tower. WS4 must make three things theorems on the WS3 map: (a) a re-diagonalization step **opens a fresh blind spot** — the new stage's residue contains a hold the prior stage's residue did not (`ws4_new_blind_spot`); (b) **depth = the length of the re-diagonalization chain**, the accumulated residue growing along `prec` as a *set* (not necessarily strictly — that strictness is WS5's monotonicity question), and reachability-into-depth is exactly the **trace** of the chain — reaching a deeper blind spot is derived from the re-diagonalization sequence, never axiomatic (charter §3); (c) the honest boundary: on witnesses this is discharged, but "all depth is diagonal residue across *any* construction" is the un-rangeable quantifier, a pre-registered Partial.

The pivot that separates WS4 (depth/accumulation) from WS5 (monotonicity): WS4 proves the accumulated residue **grows or stays** along `prec` (`⊆`, set-monotone accumulation — a new stage adds its residue to the pile), which is *accumulation*. Whether that accumulation is **strict** — whether the residue genuinely *enlarges* at every step and never re-collapses — is NOT WS4's claim; it is the monotonicity question WS5 owns and tests. WS4 stays at `⊆` (accumulation); WS5 asks about `⊊` (strict growth) and the kill condition. Keeping this line sharp is what stops WS4 from smuggling monotonicity (charter §5.5): WS4's "depth" is set-accumulation of residues, a fact about the map; it does not assert strict growth.

**Ambient theory.** `spec/README.md` §2.3 (`diag`, `SelfTotal`), §2.4 (`ReDiagStep`, `prec`, from WS3), §2.5 (`accResidue`). A periodic (`pingPong`-flavoured) carrier is the constant-accumulation witness; a strictly-growing chain (each step's residue genuinely fresh) is the strict-depth witness.

## Candidates

### C1 — A re-diagonalization step opens a fresh blind spot (the lead; WS3's C5, landed here)

```lean
theorem ws4_new_blind_spot {X} (dest : X → PkObj κ X) (insp insp' : Hold dest → HoldPred dest)
    (r : ReDiagStep dest insp insp') (h₀ : insp' _ = diag insp) :
    ∃ h, diag insp' h ∧ ¬ diag insp h         -- the new residue sees a hold the old residue could not
```
The next stage `insp'` holds the prior residue (`ReDiagStep`), so at the hold `h₀` where `insp' h₀ = diag insp`, its self-value flips — and the diagonal escapes: `diag insp'` contains a hold that `diag insp` did not. Each re-diagonalization resolves a face (holds the prior residue) by opening a new one (the diagonal always escapes its enumeration).

- **Ambient:** `diag`; `ReDiagStep`; the diagonal-escapes-enumeration fact.
- **Success condition:** the term typechecks — every re-diagonalization opens a blind spot the prior stage could not see. This is layering as *proliferation*, not narrowing.
- **Failure mode:** *the new blind spot is not genuinely new (the diagonal does not escape).* If `diag insp' ⊆ diag insp`, depth would collapse (the stage sees everything the next does). The diagonal forbids it: holding the prior residue at `h₀` changes `insp' h₀ h₀`, so `diag insp'` and `diag insp` differ at `h₀` — the escape is forced by the diagonal, not chosen.

**Paper triage.** Decidable: at `h₀` with `insp' h₀ = diag insp`, `diag insp' h₀ = ¬ insp' h₀ h₀ = ¬ diag insp h₀`, so they differ at `h₀`. **Winner (layering as accumulated blind spots).**

### C2 — Depth = chain length; accumulated residue grows along `≺` (set-monotone)

```lean
def accResidue {X} {dest : X → PkObj κ X} (chain : List (Hold dest → HoldPred dest)) : HoldPred dest :=
  fun h => ∃ insp ∈ chain, diag insp h
theorem ws4_depth_is_tower {X} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest)
    (hp : prec dest m m') (chain chain' : List _) (hgrow : chain ⊆ chain') :
    (fun h => accResidue chain h) ≤ (fun h => accResidue chain' h)   -- accumulated residue is monotone (⊆)
```
Depth is the length of the re-diagonalization chain; the accumulated residue (the union of blind spots along the chain) is set-monotone (`⊆`) as the chain extends — the tower of "the truth this stage cannot see," gathered. Reaching depth `n` means a re-diagonalization sequence of length `n`.

- **Failure mode:** *monotonicity smuggled (charter §5.5).* If stated at strict `⊊` (accumulated residue strictly grows every step), it would (i) be false on a periodic carrier (constant accumulation) and (ii) smuggle WS5's monotonicity. C2 stays at `⊆` (accumulation, always true as the chain extends) — a fact about the map, NOT a strict-growth claim.

**Paper triage.** Decidable: `accResidue` over a longer chain includes `accResidue` over a prefix (`∃ insp ∈ chain` weakens as `chain` grows). **Winner (depth-as-tower, in the honest `⊆` form).**

### C3 — Reachability-into-depth is the trace of a re-diagonalization sequence (reach derived)

```lean
theorem ws4_reaches_is_trace {X} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m'    -- reaching depth = the chain's trace
```
Reaching a deeper stage `m'` from `m` holds iff there is a re-diagonalization sequence (`prec`) from `m` to `m'`: reaching-into-depth is the *trace* of re-diagonalization, derived, not an axiom (charter §3, holding-first — here inspecting-first). The blind-spot at depth `n` is reachable iff the length-`n` chain reaches it.

- **Failure mode:** *reach re-introduced as primitive.* If depth-reachability were an independent primitive rather than the chain's trace, holding-first would break. It does not: `prec` IS `ReflTransGen (ReDiagStep)` by definition (WS3 D3), so reachability-into-depth is definitionally the trace. `Iff.rfl`.

**Paper triage.** Decidable: `prec` is defined as the closure, so the trace identity is `Iff.rfl` (WS3's `ws3_order_endogenous`). **Winner (reach-into-depth derived).**

### C4 — Depth genuinely grows: the strict-tower witness (bridges to WS5, does NOT claim monotonicity)

```lean
theorem ws4_depth_grows_witness {X} (dest : X → PkObj κ X) :
    ∃ (chain : List (Hold dest → HoldPred dest)) (m m' : Hold dest → HoldPred dest),
      prec dest m m' ∧ (∃ h, ¬ accResidue chain h ∧ diag m' h)   -- SOME chain's accumulated residue strictly grows
```
Exhibit *one* construction where the accumulated residue strictly grows — a re-diagonalization sequence in which each stage's blind spot is genuinely fresh (the empirical signature of ever-deepening self-inspection). This is the *existence* of strict growth, not its universality.

- **Failure mode:** *mistaken for monotonicity.* This witnesses that strict depth-growth *can* happen; it does NOT claim *every* re-diagonalization strictly grows (that is monotonicity, WS5, and is expected to fail on periodic carriers). Kept as a witness that the phenomenon is real, explicitly scoped away from the universal.

**Paper triage.** Decidable: a chain of inspections each opening a fresh residue (via `ws4_new_blind_spot` iterated) gives strict accumulation on that chain. **Winner (the witness that depth-growth is inhabited), scoped strictly away from monotonicity.**

### C5 — The universal form: all depth is diagonal residue (pre-registered Partial)

```lean
-- ws4_all_depth_is_residue : ∀ (construction) (deeper-than relation), deeper ⇒ an accumulated diagonal residue
theorem ws4_universal_depth_partial : True   -- placeholder: the un-rangeable quantifier
```
The charter-strength claim quantifies over *every* construction and *every* notion of "deeper" — the un-rangeable universal (charter §5.3), exactly as Series 7's trichotomy-exhaustiveness and Series 8's universal narrowing were.

- **Failure mode:** *over-claim.* Stating it as a theorem would require quantifying over all coalgebras and depth-notions. **Reject as a theorem; deliver as a defended thesis floored by C1+C2+C3+C4, routed to WS6.**

**Paper triage.** Not paper-decidable at the universal. **Partial, routed to WS6.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | a step opens a fresh blind spot (diagonal escapes) | `diag insp'` vs `diag insp` at `h₀` | yes | **win (accumulated blind spots)** |
| C2 | depth = chain length; accumulation monotone (`⊆`) | `accResidue`, chain extension | yes | **win (depth-as-tower)** |
| C3 | reach-into-depth = trace of the chain | `prec` = closure (`Iff.rfl`) | yes | **win (reach derived)** |
| C4 | SOME chain strictly grows (growth inhabited) | fresh-residue chain witness | yes | **win (witness, scoped)** |
| C5 | ALL depth is diagonal residue (any construction) | un-rangeable | no | Partial → WS6 |

## Winning candidates: C1 (fresh blind spot), C2 (depth-as-tower), C3 (reach-as-trace), C4 (strict-growth witness); C5 Partial → WS6

### Definitions and obligations (cite `spec/README.md` §2; consume WS3)

```lean
namespace Series9.WS4
-- carrier, diag, SelfTotal, ReflTransGen machinery — transcribed / from WS1 (README §6);
-- ReDiagStep, prec, ws3_order_endogenous from WS3.

def accResidue {X} {dest : X → PkObj κ X} (chain : List (Hold dest → HoldPred dest)) : HoldPred dest :=
  fun h => ∃ insp ∈ chain, diag insp h

/-- **D1 — a step opens a fresh blind spot (C1).** Holding the prior residue at `h₀` flips the diagonal
    there: `diag insp'` sees a hold `diag insp` could not. Layering as PROLIFERATION, not narrowing. -/
theorem ws4_new_blind_spot {X} (dest : X → PkObj κ X) (insp insp' : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (h₀eq : insp' h₀ = diag insp) :
    diag insp' h₀ ↔ ¬ diag insp h₀ := by
  simp only [diag, h₀eq]

/-- **D2 — depth is the tower (C2).** The accumulated residue is set-monotone (`⊆`) as the chain
    extends: the tower of "the truth this stage cannot see," gathered. Stated at `⊆` (accumulation);
    strictness is WS5's monotonicity question, NOT claimed here. -/
theorem ws4_depth_is_tower {X} (dest : X → PkObj κ X)
    (chain chain' : List (Hold dest → HoldPred dest)) (hsub : chain ⊆ chain') :
    ∀ h, accResidue chain h → accResidue chain' h := by
  intro h ⟨insp, hmem, hd⟩; exact ⟨insp, hsub hmem, hd⟩

/-- **D3 — reach-into-depth is the trace (C3).** `prec` (a re-diagonalization sequence) IS the closure of
    `ReDiagStep`: reaching a deeper blind spot is the trace of the chain, derived not axiomatic. -/
theorem ws4_reaches_is_trace {X} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' := ws3_order_endogenous dest m m'

/-- **D4 — depth-growth is inhabited (C4), scoped away from monotonicity.** SOME re-diagonalization chain
    strictly accumulates: each stage's blind spot genuinely fresh. This does NOT claim every step grows
    (that is WS5). Built by iterating `ws4_new_blind_spot`. -/
theorem ws4_depth_grows_witness {X} (dest : X → PkObj κ X) :
    ∃ (chain : List (Hold dest → HoldPred dest)) (m m' : Hold dest → HoldPred dest),
      prec dest m m' ∧ (∃ h, ¬ accResidue chain h ∧ diag m' h) := …
```

**D1 (fresh blind spot)** is the layering payoff: the diagonal always escapes its enumeration, so each re-diagonalization opens a new unseen face — depth as accumulation, the diagonal analogue proved directly. **D2 (depth-as-tower)** is the accumulation law at `⊆` — set-monotone `accResidue` as the chain extends. **D3 (reach-as-trace)** cites WS3's `ws3_order_endogenous`: reaching-into-depth is the trace of re-diagonalization, inspecting-first honored. **D4 (strict-growth witness)** shows strict depth-growth *happens* without claiming it *always* happens — the bridge to WS5, scoped explicitly away from monotonicity so WS4 does not smuggle it.

## Outcome classes (per charter §7)

- **Discharged:** D1 (fresh blind spot), D2 (depth-as-tower, accumulation `⊆`), D3 (reach-as-trace, cited from WS3), D4 (strict-growth inhabited).
- **Partial (pre-registered, routed to WS6):** C5, "all depth is diagonal residue across any construction" — the un-rangeable quantifier (charter §5.3), a defended thesis floored by D1–D4, exactly Series 7/8's exhaustiveness pattern.
- **Failed (pre-registered honest alternative):** if a re-diagonalization step were found that *shrinks* the seen residue without opening a fresh blind spot (`diag insp' ⊆ diag insp`), depth-as-accumulation would fail. Not possible: holding the prior residue at `h₀` flips the diagonal there (D1), so a fresh blind spot always opens. The direction of proliferation is forced by the diagonal, not chosen.
- **Coincident-adjacent / laundering risk (cross-workstream, protocol §D):** WS4's depth depends on WS3's re-diagonalization genuinely opening new blind spots (D1) — which depends on the map being genuine and the residue always existing (WS1). If WS1's spine is Coincident, the "new blind spots" are relational-identity artifacts, and WS4's depth is laundered. The batched review must confirm the edge: depth is genuine layering only if the spine is the independent diagonal.
- **Strip test.** Delete **"blind spot"** from `ws4_new_blind_spot` and it is the bare **`diag insp' h₀ ↔ ¬ diag insp h₀`** — a fixed-point-flip fact (the diagonal differs from its predecessor at the updated point). Delete **"depth/tower"** from `ws4_depth_is_tower` and it is the bare **`accResidue` monotone under `List.Subset`** — a set-union monotonicity fact. Delete **"depth/trace"** from `ws4_reaches_is_trace` and it is the bare **`prec` = `ReflTransGen` closure** (WS3). All three payoffs **survive the strip** as fixed-point / set-monotonicity / reachability facts; the earned layer is reading the fresh diagonal as *a blind spot the prior stage could not see*, the accumulation as *depth*, the chain length as *the tower*. WS4 flags this honestly: the mathematics is diagonal-escape plus set-accumulation plus reachability; the *layering* is the interpretation. The residue that does **not** strip — that reaching-into-depth is *derived* from re-diagonalization sequences (D3), not primitive — is the genuine inspecting-first content.

## Deliverable

`series-9/formal/Series9/ws4.lean`: transcribed carrier (README §6); `accResidue`; `ws4_new_blind_spot` (D1), `ws4_depth_is_tower` (D2), `ws4_reaches_is_trace` (D3), `ws4_depth_grows_witness` (D4). **Consumes WS3's `ReDiagStep`/`prec`/`ws3_order_endogenous`**; does not redefine the order. The universal (C5) is routed to WS6. Axiom check: `#print axioms ws4_new_blind_spot` reduces through `diag` to `propext` / the standard three. Depth is accumulation (`⊆`), NOT strict growth — the strict/monotone question is WS5's, and WS4 is scoped explicitly away from it.

---

## REVIEW-RESPONSE NOTE (2026-07-11, series-review-1 F-8 SERIOUS + F-5 REAL)

On the strengthened `ReDiagStep` (WS3 note: the next stage inspects the whole prior residue), the depth
content is now genuine. `ws4_new_blind_spot` (a point-flip on `insp' h₀ = diag insp`) is replaced by
**`ws4_residue_moves`**: `ReDiagStep insp insp' → ∀ h, diag insp h → ¬ diag insp' h` — re-inspection
CLOSES the whole prior residue, so the diagonal escapes its enumeration and does not linger; the new
residue is disjoint from the prior one. `ws4_residue_moves_witness` exhibits the residue moving to a
fresh hold, tied to `insp` by `ReDiagStep` (not a free constant inspection, the F-8 laundering the review
flagged). **F-5:** `ws4_depth_is_tower` is relabelled honestly as accumulation (`⊆`) of the accumulated
residue — a list-membership fact; the tower reading is prose, flagged. All axiom-clean.
