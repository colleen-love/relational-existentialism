# WS6 — The heuristic ceiling and the program's close

**Design doc. Series 11, the honest boundary and, as the program's terminal series, its close. Owns: the universal and transfinite forms of attention-reality and the endogenous bound, reported where they exceed what is rangeable as defended theses FLOORED by the mechanized core (the Series 04/05/07/08/09/10 pattern); the unification (Series 08's finite hold IS Series 11's attention) as a theorem-or-thesis; and the program-level synthesis (the four-beat arc: Parmenides / diagonal / reification / attention) stating what the whole program established and what it leaves open.**

*Series 11 is standalone; the mechanized core (`ws1_attention_makes_real`, `ws3_no_total_attention`, `ws4_bound_is_holding_not_size`, `ws5_crown_on_finite_stages`) is consumed, not redefined. WS6 adds no new mathematical obligation; it reports the CEILING (what the mechanized core does not reach) and the program's close. The genuinely new content is `ws6_provable_core`, `ws6_universal_theses`, `ws6_unification`, and the prose `summary.md` / `summary-technical.md` at Phase F. WS6 runs after WS1–WS5 and before WS7's verdict.*

## The object at stake

Charter §5.3 (the scope stated honestly), §6 (WS6), §10 (positioning). Two forms of every Series 11 payoff exceed what is rangeable, and WS6 reports them as theses, floored by the mechanized core:

- **Universal attention-reality.** WS1/WS2 discharge attention-reality on a WITNESS (a finite attention distinguishes the reified relatum where the plain quotient collapses, `ws4_free_label_is_import`-shaped, free). The UNIVERSAL — "every finite attention on every κ-free tower reads the reified relatum freely" — is the un-rangeable quantifier, exactly as Series 09's spine and Series 10's constructions were per-witness. WS6 reports it as a defended thesis floored by the witness.
- **Transfinite / universal bound.** WS3/WS4 discharge no-total-attention (an Impossibility, stage-independent) and the κ-free bound on FINITE stages. The transfinite LIMIT (whether an accumulated hold across a limit re-admits a total attention) and the residual carrier branching-κ (§2.7) are the crown's Partial edge (WS5), reported here as the open thesis and the concrete form the terminal fork most likely takes.
- **The unification.** Charter Consequence 3: Series 08's finite hold IS Series 11's finite attention. WS1's `ws1_attention_is_finite_hold` ties the structural objects (a finite attention is a finite reachable hold); the universal equivalence (that every Series 08 finite hold is a Series 11 attention and vice versa, on the reifying field) is a defended thesis, reported here — never a gloss (charter §5.5).

WS6 also owns the program's close: as the terminal series, Phase F writes the four-beat synthesis and states the honest terminus (crown-on-finite-stages / Partial / tragic), what the whole program established, and what it leaves open.

**Ambient theory.** `spec/README.md` §2–§3; WS1–WS5 payoffs. All from §6.

## Candidates

### C1 — The provable core, bundled (the floor)

```lean
/-- **The provable core (the floor).** The mechanized results Series 11 discharges: attention-reality on a
    witness (distinguishes where the plain quotient collapses, free), no-total-attention (Impossibility,
    κ-free), the κ-free bound on finite stages (holding-not-size). Everything WS6's theses stand on. -/
theorem ws6_provable_core {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hinf : ℵ₀ ≤ κ) (hfree : ¬ Recoverable dest) :
    (∃ x y : ULift Bool, (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
       ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y))                    -- attention-reality (witness), WS1/WS2
  ∧ (¬ ∃ t, SelfTotal insp t)                                            -- no-total-attention (Impossibility), WS3
  ∧ (¬ Assembled insp)                                                    -- the bound (holding-not-size), WS4
  ∧ (¬ Recoverable dest) :=                                              -- free distinction, WS1/WS5
  ⟨⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩,
   ws1_no_self_total_hold (plainOf dest) insp, ws4_no_completed_totality (plainOf dest) insp, hfree⟩
```
The floor: the mechanized results, bundled, that every thesis stands on. Attention-reality on a witness, no-total-attention (Impossibility), the κ-free bound on finite stages, the free distinction. WS6's theses (C2) are what these do not reach.

- **Ambient:** WS1–WS5 payoffs.
- **Success condition (Discharged):** the conjunction typechecks from the consumed payoffs.
- **Failure mode:** *none — this is the floor.* **Winner (the floor).**

### C2 — The universal theses, floored (the ceiling, honestly named)

```lean
/-- **The universal theses (the ceiling).** Stated as the un-rangeable universals floored by the core:
    universal attention-reality (every finite attention on every κ-free tower reads freely) and the
    transfinite bound (no-total-attention survives every limit) are DEFENDED THESES, not theorems — the
    witness (C1) is the floor. Recorded as the honest boundary, never claimed as discharged. -/
def ws6_universal_theses : Prop :=
    (∀ {Q X : Type u} (dest : X → LkObj κ Q X),
       (¬ Recoverable dest) → /- universal attention-reality: thesis -/ True)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
       /- transfinite no-total-attention: thesis, floored by the stage-independent NT -/ (¬ ∃ t, SelfTotal insp t))
```
The ceiling, honestly named: the universal attention-reality and the transfinite bound are theses, not theorems. The transfinite no-total-attention thesis is FLOORED by the stage-independent NT (`ws1_no_self_total_hold` holds at every stage, so the thesis' floor is a theorem; the OPEN part is the accumulated-hold-across-a-limit, which the stage-independent form does not by itself close). The universal attention-reality thesis is floored by the witness (C1). WS6 states which part is a theorem and which is a thesis, never blurring them.

- **Ambient:** the core (C1); `ws1_no_self_total_hold`.
- **Success condition (thesis, floored):** the theses are stated as theses, with the mechanized floor named. No universal is claimed discharged.
- **Failure mode:** *a thesis claimed as a theorem (overclaim, charter §5.3).* The trap is reporting the universal as discharged. C2 states them as theses floored by the witness/finite-stage core, the honest boundary. **Winner (the ceiling, honestly named).**

### C3 — The unification, a theorem tying the objects (Consequence 3)

```lean
/-- **The unification (Consequence 3).** Series 08's finite hold IS Series 11's finite attention: a finite
    attention is a finite reachable hold (the structural tie, a theorem, `ws1_attention_is_finite_hold`),
    and the tower is what it proliferates by reifying residues. The universal equivalence is a defended
    thesis; the structural identification is a theorem, never a gloss (charter §5.5). -/
theorem ws6_unification {Q X : Type u} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ws1_attention_is_finite_hold dest att
```
The unification, tied as a theorem: a finite attention IS a finite reachable hold (the Series 08 finite hold), now reading a GROWING (reifying) field rather than a fixed one. Series 08 got a Partial because a finite hold on a fixed field could not generate plurality; Series 11's finite attention on the reifying tower both reads (the reified residues) and bounds (finitude of holding). The structural identification is a theorem; the universal equivalence (every Series 08 hold is a Series 11 attention) is a defended thesis. Never a gloss.

- **Ambient:** `ws1_attention_is_finite_hold`, `FiniteAttention`.
- **Success condition (Discharged, structural; thesis, universal):** the structural tie is a theorem; the universal equivalence a thesis.
- **Failure mode:** *the unification a gloss (§5.5).* If the tie were merely asserted, Consequence 3 would be a gloss. C3 makes the structural tie a theorem, the universal a flagged thesis. **Winner (the unification, theorem-and-thesis).**

### C4 — The program's close (the four-beat synthesis, Phase F prose)

The program-level synthesis, written at Phase F in `summary.md` / `summary-technical.md` / the root `README.md`: the four-beat arc and its honest terminus.

- **Beat 1 (Parmenides, Series 07):** symmetric relations collapse to the One (`ws2_import_theorem_static`); "You are loved" is the undifferentiated relatedness before the first gap.
- **Beat 2 (the diagonal, Series 09):** the diagonal individuates a self from the One (`ws1_no_self_total_hold`); "Self is a paradox."
- **Beat 3 (reification, Series 10):** reification turns the diagonal residue into a proliferating tower (`reify`, `reifyStep`), proved Bookkeeping at the plain level (`ws2_reify_bisim_embeds`); "To relate is to create."
- **Beat 4 (attention, Series 11):** finite attention reads the reified label (rescuing Bookkeeping, WS1/WS2) and bounds the tower by never grasping the whole (no-total-attention, WS3; the κ-free bound, WS4); "To attend is to become."

The honest terminus: attention-reality Discharged-on-witness (the reader Series 10 lacked, certified free), no-total-attention an Impossibility (the bound's engine, κ-free), the κ-free bound Discharged on finite stages, and the crown Partial (finite Discharged, transfinite/carrier-κ open, tragic pre-registered and live). What the program established: self-reference is the engine, its incompletability generates the many (Series 09/10) and forbids the total hold (Series 11), and on finite stages the many is real-at-the-attended-level and bounded-by-the-incompletability from the structure's own resources. What it leaves open: whether that bound survives to the transfinite limit and whether the residual carrier branching-κ is genuinely removed (the crown's Partial/tragic edge) — the reading the bounded formalism may only partly decide.

- **Success condition:** the synthesis states plainly what is proved, what is thesis, and what is open, with the philosophical reading marked as divergent from the machine-checked core (charter §10).
- **Failure mode:** *the synthesis overclaims the crown or hides the ceiling.* C4 states the terminus honestly: Discharged-on-witness / Impossibility / finite-Discharged / Partial, never the full crown as proved. **Winner (the program's close).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the provable core (the floor) | WS1–WS5 payoffs | yes — bundled | **win (the floor)** |
| C2 | the universal theses, floored (the ceiling) | the core, `ws1_no_self_total_hold` | yes — theses named | **win (the ceiling)** |
| C3 | the unification (theorem + thesis) | `ws1_attention_is_finite_hold` | yes | **win (unification)** |
| C4 | the program's close (four-beat synthesis) | WS1–WS5 terminus | prose | **win (program close)** |

## Winning candidates: C1 (floor) + C2 (ceiling) + C3 (unification) + C4 (program close)

### Definitions and obligations (cite `spec/README.md` §2–§3; consume WS1–WS5, add no new obligation)

```lean
namespace Series11.WS6
-- ws1_attention_makes_real, ws1_attention_is_finite_hold, ws3_no_total_attention, ws4_no_completed_totality,
-- ws4_bound_is_holding_not_size, ws5_crown_on_finite_stages, Assembled, FiniteAttention, ws4_free_label_is_import,
-- ws1_no_self_total_hold, Recoverable, labelLoop — consumed (README §6).

/-- **D1 — the provable core (C1, the floor).** -/
theorem ws6_provable_core {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hinf : ℵ₀ ≤ κ) (hfree : ¬ Recoverable dest) :
    (∃ x y : ULift Bool, (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
       ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R x y))
  ∧ (¬ ∃ t, SelfTotal insp t) ∧ (¬ Assembled insp) ∧ (¬ Recoverable dest) :=
  ⟨⟨⟨true⟩, ⟨false⟩, ws4_free_label_is_import hinf⟩,
   ws1_no_self_total_hold (plainOf dest) insp, ws4_no_completed_totality (plainOf dest) insp, hfree⟩

/-- **D2 — the universal theses, floored (C2, the ceiling).** Stated as theses; the transfinite-NT thesis'
    floor (the stage-independent NT) is a theorem, the accumulated-limit part open. -/
def ws6_universal_theses : Prop :=
    (∀ {Q X : Type u} (dest : X → LkObj κ Q X), (¬ Recoverable dest) → True)
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ∃ t, SelfTotal insp t)

/-- **D3 — the unification (C3, theorem + thesis).** -/
theorem ws6_unification {Q X : Type u} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) :
    att.reads.Finite ∧ (∀ z ∈ att.reads, SReaches (plainOf dest) att.focus z) :=
  ws1_attention_is_finite_hold dest att
```

**D1 (the floor)** bundles the mechanized core: attention-reality on a witness, no-total-attention, the κ-free bound, the free distinction. **D2 (the ceiling)** names the universals as theses, with the mechanized floor (the stage-independent NT, the witness) stated, never blurring theorem and thesis. **D3 (the unification)** ties Series 08's finite hold to Series 11's attention as a theorem, the universal a thesis. **C4 (the program's close)** is the Phase F prose synthesis.

## Outcome classes (per charter §7)

- **Discharged (the floor, the unification's structural tie):** D1 (`ws6_provable_core`), D3 (`ws6_unification`). The mechanized core and the structural unification.
- **Partial / thesis (the ceiling, honestly named, charter §5.3):** D2 (`ws6_universal_theses`). Universal attention-reality and the transfinite bound are defended theses floored by the witness/finite-stage core, NOT theorems. The concrete form: the crown Partial (finite Discharged, transfinite/carrier-κ open), the terminal fork's honest boundary.
- **The program's close (C4, Phase F):** the four-beat synthesis, stating the honest terminus (Discharged-on-witness / Impossibility / finite-Discharged / crown Partial, tragic pre-registered and live), what the program established and what it leaves open, with the philosophical reading marked as divergent from the machine-checked core.
- **Strip test.** Delete **"universal" / "the whole tower" / "every attention"** from the theses (D2) and what remains is the mechanized floor: the stage-independent no-total-attention (`ws1_no_self_total_hold`) and the witness attention-reality (`ws4_free_label_is_import`). The theses **do not survive the strip as theorems** — that IS the point: WS6's function is to name the gap between the floor (a theorem) and the ceiling (a thesis), so no universal is laundered as discharged. WS7 records: WS6 is the honest boundary, the mechanized core floored and the un-rangeable universals named as theses, and the program's close stating the terminus without overclaiming the crown.

## Deliverable

`series-11/formal/Series11/ws6.lean`: `ws6_provable_core` (D1), `ws6_universal_theses` (D2), `ws6_unification` (D3); and at Phase F, `summary.md`, `summary-technical.md`, the root `README.md` program synthesis (C4). **Consumes WS1–WS5; adds no new mathematical obligation; names the ceiling.** Axiom check: `#print axioms ws6_provable_core` reduces through the consumed payoffs to the standard three. **WS6 reports the universal and transfinite forms as defended theses floored by the mechanized core, ties the unification as a theorem, and — as the program's terminal series — writes the four-beat synthesis and the honest terminus (crown-on-finite-stages Discharged, the full crown Partial, tragic pre-registered and live), stating what the whole program established and what it leaves open.**
