# WS1, The other as a second attending locus (the construction)

**Design doc. Series 2.2, the blocking workstream. Owns: the shared witness carrier `RCar` (README §3) and the
proof that the OTHER is a genuine second reader — a relatum of the same field with its own finite `attends`,
distinct from the self, seeded by reifying the shared-field pattern (which contains the self-relation), reading a
shared field that contains both. The sin (charter §4, DISCONNECTED): a second locus constructible only by
importing structure beyond the symmetry-breaker.**

*Imports `P2S1`; builds the `Fin 3` witness on the S0 `attends`/`outDest`/`FinReify` API, generalizing S0's
`ws1_first_other` (the self-loop reified into the first other) by giving the reified relatum its OWN attention
that reads back into the field. Every obligation reduces by the kernel (`decide`/`rfl`).*

## The object at stake

The charter's WS1 (§2): construct the OTHER as a genuine second reader over the imported ground — a relatum with
its own finite `attends`, distinct from the self, seeded in the first other (the reified self-relation upgraded
from an attended object to an attending locus), reading a shared field that contains both. Prove it well-formed:
a relatum of the same field (no new layer of substance), its attention a genuine finite `attends` set, the
shared field genuinely containing self, other, and what each attends. If no second locus is constructible
without importing structure beyond the symmetry-breaker, that is the pre-registered DISCONNECTED obstruction.

## The carrier (README §3, fixed here)

```lean
abbrev RCar : Type := Fin 4
def slf : RCar := 0   -- the self (base of the constitution tower), rank 0
def oth : RCar := 1   -- the OTHER: the reified self-relation upgraded to a locus reading back, rank 1
def sh  : RCar := 2   -- a shared relatum in the other's wider reach (makes the two reaches distinct), rank 0
def bnd : RCar := 3   -- a higher closure the pair does not jointly attend (WS4 residue witness), rank 2

def attendsR : RCar → Finset RCar := fun x =>
  if x = slf then {slf, oth} else if x = oth then {slf, oth, sh} else if x = sh then {sh} else {oth}
def rankR : RCar → ℕ := fun x => if x = oth then 1 else if x = bnd then 2 else 0
def reifyR : Finset RCar → RCar := fun s =>
  if s = {slf, oth, sh} then oth else if s = {oth} then bnd else slf
def rfield : Finset RCar := {slf, oth, sh}   -- the shared field: self, other, and what they attend
```
The self's reach `{slf,oth}` is a proper subset of the other's `{slf,oth,sh}` (the C3-S1 repair: distinct
reaches, so WS4's joint residue `bnd` is missed by two DIFFERENT attentions, not one membership).

Carrier lemmas (all `decide`/`rfl`): `attendsR_slf`, `attendsR_oth`, `attendsR_bnd`; `attendsR_nonempty`;
`outDestR_ne_empty`; `ws1_rcar_SHNE` (every node `SHNE`, by reduction to `attendsR_ne_empty`, the S1
`ws1_tcar_SHNE` pattern); `plainOf_rankLiftR` (`plainOf (rankLift dest lab) = dest`, the S1 `plainOf_rankLiftT`
pattern); `rankLiftR_val` (the labelled edge set at `x`).

## Candidates

### C1, the other as the reified shared-field pattern, reading back (the lead)

The other `oth = reifyR {slf, oth}` reifies the shared-field pattern `{slf, oth}` (which contains the
self-relation `{slf}`), sections it (`attendsR (reifyR {slf,oth}) = {slf,oth}`), is a relatum of the SAME field
`RCar`, ranks strictly above the self (`rankR oth = 1 > 0`), and reads back into the field (`slf, oth ∈ attendsR
oth`). This is S0's `ws1_first_other` with the reified relatum given its own reading.

```lean
theorem ws1_other_is_locus (hinf : ℵ₀ ≤ κ) :
    (reifyR {slf, oth, sh} = oth ∧ attendsR (reifyR {slf, oth, sh}) = {slf, oth, sh})  -- seeded by reification; sections
  ∧ oth ≠ slf                                                                   -- distinct from the self
  ∧ (attendsR oth).Nonempty                                                     -- its attention a genuine finite attends
  ∧ (slf ∈ rfield ∧ oth ∈ rfield                                               -- the shared field contains both,
      ∧ (∀ z ∈ attendsR slf, z ∈ rfield) ∧ (∀ z ∈ attendsR oth, z ∈ rfield))   --  and what each attends
  ∧ (∀ x : RCar, Cardinal.mk (↥((outDest hinf attendsR x).1)) < Cardinal.aleph0)  -- finite bound, no cardinal ceiling
```
- **Ambient:** `reifyR`, `attendsR`, `rankR`, `rfield`, `outDest`, `ws1_bound_is_finite_attention` (S0, the
  finite bound reused verbatim).
- **Success condition:** the first four conjuncts by `decide`/`rfl`; the bound conjunct by
  `ws1_bound_is_finite_attention hinf attendsR`.
- **Failure mode:** *a new layer of substance (SERIOUS) or DISCONNECTED.* Foreclosed: `oth : RCar` (same field),
  `attendsR oth : Finset RCar` (a genuine finite attends), the section discharged (`decide`), the bound the S0
  bound (no cardinal ceiling). **Winner.**

### C2, the shared field genuinely contains both and their attentions (the well-formedness half, folded into C1)

The `rfield` conjunct of C1: `slf, oth ∈ rfield` and every relatum either perspective attends is in `rfield`
(`attendsR slf = attendsR oth = {slf,oth} ⊆ rfield`). This is the "reading a shared field that contains both"
clause. Folded into `ws1_other_is_locus`, not a separate theorem.

### C3, the reification section is a genuine `FinReify` fact, not an opaque constructor (the honesty half)

`attendsR (reifyR {slf,oth}) = {slf,oth}` is a real pointwise `FinReify` section (`decide`), exactly as S1's
`section_cycleA`. The other's well-formedness is DISCHARGED from the section, never posited by an opaque
`Nonempty` constructor (the PR1-S2 sin). Injective at the used patterns via `ws1_finreify_injective` where
needed; the section is pointwise (total `FinReify` unsatisfiable on the finite carrier, disclosed as in S0/S1).

### C4, the other as a bare second label (the sin to avoid)

```lean
def ws1_other_bad : RCar := oth   -- oth with attendsR oth quantified out of every payoff
```
- **Failure mode:** *if `attendsR oth` never appears load-bearing in WS2-WS4, `oth` is a point-tag and the
  series builds the self twice (K1, SERIOUS).* **Reject.** Foreclosed downstream: WS2's reader reads via
  `attendsR`, WS4's mutual residue is the joint `attendsR` subtracting `bnd`; the other's attention is
  load-bearing everywhere.

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | other = reified field pattern, locus, sections, reads back, bounded | `reifyR`/`attendsR`/`rankR`, S0 bound | yes, `decide` + S0 lemma | **win** |
| C2 | shared field contains both & attentions | `rfield` | yes, `decide` | **win (folded)** |
| C3 | section is a genuine `FinReify` fact | `attendsR (reifyR …)` | yes, `decide` | **win (folded)** |
| C4 | other a bare label | — | K1 sin | reject (SERIOUS) |

## Winning candidate: C1 (with C2, C3 folded in)

**Proof architecture.** `ws1_other_is_locus` is `decide`/`rfl` on the witness for the reification/distinctness/
field conjuncts, and `ws1_bound_is_finite_attention hinf attendsR` for the finite bound. The other is a relatum
of `RCar` (no new substance), minted by reifying the shared-field pattern that contains the self-relation, its
attention a genuine finite `attends` reading back into the field. Lands `wf = true` for WS5. **Dependencies:**
the carrier (this doc), `ws1_bound_is_finite_attention` (S0), `ws1_rcar_SHNE`, `plainOf_rankLiftR`,
`rankLiftR_val` (built here, used by WS2-WS4).

## Outcome classes (per charter §5)

- **wf = true (the expected WS1 payoff):** the other is a genuine second locus, seeded by reification,
  bounded, reading a shared field containing both.
- **DISCONNECTED (pre-registered, first-class):** if the second locus required importing structure beyond the
  symmetry-breaker (e.g. a new atom, a cardinal ceiling, an opaque non-`FinReify` constructor), reported
  DISCONNECTED with the obstruction precise. Foreclosed here: `oth` is a `Fin 3` relatum minted by a genuine
  `reifyR` section, no import beyond the tower rank.

## Strip test

`ws1_other_is_locus` strips (delete "other," "self," "locus," "field") to *"`reifyR {slf,oth} = oth`, `attendsR
(reifyR {slf,oth}) = {slf,oth}` (a `FinReify` section), `oth ≠ slf`, `attendsR oth` nonempty, `{slf,oth} ⊆
rfield`, and `outDest`'s neighborhoods are `< ℵ₀`"* — a bare reification/attention/finiteness fact. It survives
the strip: no name is a term.

## Deliverable

`formal/P2S2/ws1.lean`: the carrier `RCar`/`slf`/`oth`/`bnd`/`attendsR`/`rankR`/`reifyR`/`rfield`, the carrier
lemmas (`ws1_rcar_SHNE`, `plainOf_rankLiftR`, `rankLiftR_val`), and `ws1_other_is_locus`. The other a relatum of
the same field, seeded by reification, bounded, reading back; no new substance (audit, WS1). Axiom check reduces
through `decide` and the S0 bound to the standard three.
