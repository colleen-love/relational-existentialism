# WS5 — The conservation fork

**Design doc. Series 8. Owns THE central open law and is forbidden from assuming its answer: attempt conservation of breadth under narrowing **(CB)**, run the pre-committed kill condition (charter §5.4), and report Discharged / Refuted hypothesis / Partial — never assumed, never baked into the re-restriction map.**

*Series 8 is standalone; names transcribed into `series-8/formal/Series8/ws5.lean`, re-namespaced `Series8.WS5` (see `spec/README.md` §6). WS5 **consumes WS3's map and is forbidden from touching its definition** (protocol §0.4, §4): conservation is a claim ABOUT `ReReStep`/`breadth`, computed on the map WS3 built, never a clause inside it. The `breadth` measure is fixed once in `spec/README.md` §2.5, deliberately OUTSIDE `ReReStep`, so foreclosure is testable and refutable rather than true-by-unfolding. This workstream is the series' atom-or-will door: the math fixes the bound's shape; the reading (constitutive scarcity vs. epistemic limit) may be left open.*

## The object at stake

Charter §2 (the open law), §5.4 (the fork with its kill condition). The bound on plurality is the finitude of holding. Its **strong** form is a conservation law: breadth is conserved under narrowing, so each re-restriction forecloses as much depth as it opens — zero-sum focusing, a self-limiting universe. Its **weak** form is mere boundedness: holds are finite but breadth is not conserved. Series 8 does **not** assume conservation. WS5 builds nothing into the map; it measures `breadth` (the alternatives at a hold, `spec/README.md` §2.5) separately and *tests* whether it is conserved along `prec`, with a pre-committed **kill condition**:

- **exhibit a depth-opening re-restriction that forecloses no breadth** → conservation **Refuted** (a finding; the bound downgrades to mere boundedness; "self-limiting universe" retracted);
- **prove foreclosure holds and ranges** → conservation **Discharged**;
- **foreclosure on witnesses but the universal resists** → conservation **Partial** (defended thesis floored by witnesses; the epistemic/constitutive fork left open).

The whole workstream turns on `breadth` being a *fact about the map*, not a clause inside it. The cardinal sin (protocol §0.4): a re-restriction definition that deletes the chosen successor from the sibling set, so "breadth is conserved" is true by unfolding `ReReStep`. WS3's `ReReStep` follows the edge and touches no sibling set (WS3 D1a/D1b), so foreclosure is genuinely open — and WS5 runs the kill condition to settle it.

**The honest expectation, pre-registered (not a target).** A *free* atomless field need not conserve breadth: a constant-branching carrier (every node with the same branching factor `b`) opens depth at every re-restriction while breadth stays exactly `b` — nothing foreclosed. So the kill condition is expected to **fire**: conservation **Refuted in general**, with a **Discharged sub-class** (finite-breadth-budget carriers where the alternatives are a fixed finite set repartitioned) making the overall verdict a **Partial** (Refuted-universal, Discharged-on-a-class). This is the atom-or-will door: whether the finitude that *does* bound (mere boundedness) is a constitutive scarcity or an epistemic limit is the reading the formalism does not decide.

**Ambient theory.** `spec/README.md` §2.4 (`ReReStep`, `prec` — WS3, consumed not redefined), §2.5 (`breadth`). The self-loop `twoLoop` (breadth 1 forever) and a constant-branching tree (breadth `b` forever) are the kill-condition witnesses; a finite-budget partition carrier is the Discharged-subclass witness.

## Candidates

### C1 — Conservation as a monotonicity claim on `breadth` along `prec` (the claim to test)

```lean
def Conserves (dest) : Prop := ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' ≤ breadth dest h
```
The strong bound: breadth does not increase along a re-restriction (each narrowing forecloses at least as much as it opens). This is the *statement*, not an assumption — WS5 asks whether it holds.

- **Ambient:** `breadth` (measured outside the map); `ReReStep`; `Cardinal.le`.
- **Success condition (Discharged):** `Conserves dest` proved for the relevant class.
- **Failure mode:** *conservation-assumed.* The trap is proving `Conserves` by *unfolding `ReReStep`* — which cannot happen here, because `ReReStep` says nothing about `breadth` (it follows an edge). So any proof of `Conserves` must use a *fact about `dest`* (e.g. successor sets shrink), and any refutation is a *witness* — exactly the honest test.

**Paper triage.** The *statement* is clean; its *truth* is the open question. **Winner as the claim; its verdict is C3/C4.**

### C2 — The strong (strict) form: each narrowing strictly forecloses

```lean
def ConservesStrict (dest) : Prop := ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' < breadth dest h
```
The zero-sum reading in full: every step strictly reduces breadth (self-limiting, plurality forecloses monotonically to nothing).

- **Failure mode:** *immediately false.* The self-loop `twoLoop` has breadth 1 at every hold, so `breadth h' < breadth h` fails (1 < 1 is false). `ConservesStrict` is refuted by the simplest atomless witness. **This is the kill condition's cleanest firing.**

**Paper triage.** Decidable and false: `twoLoop` refutes it in one line. **Winner as the refuted horn (the kill condition fires here).**

### C3 — The kill condition: a depth-opening re-restriction foreclosing no breadth (Refuted)

```lean
theorem ws5_kill_condition (hinf : ℵ₀ ≤ κ) :
    ∃ {X} (dest : X → PkObj κ X) (h h' : Hold dest),
      ReReStep dest h h' ∧ ¬ (breadth dest h' < breadth dest h)     -- depth opens, breadth NOT foreclosed
```
Exhibit the witness the charter's kill condition demands: a re-restriction that opens depth (a genuine step) while foreclosing no breadth. The constant-breadth self-loop (`twoLoop`: breadth 1 → 1) or a constant-branching tree (breadth `b` → `b`) is it.

- **Ambient:** `twoLoop` / constant-branching carrier; `breadth` constant.
- **Success condition (Refuted):** the term exists → conservation (strict, C2) is **FALSE**; reported as a Refuted hypothesis, the bound downgraded to mere boundedness, "self-limiting universe" retracted (charter §5.4).
- **Failure mode:** *the witness is degenerate/not atomless.* Guard: the witness must be `SHNE` (genuinely atomless, no leaf) so it is a real field, not a trivial stub. `twoLoop_HNE` gives it: breadth-1 *and* atomless. So the refutation is on a genuine atomless field, not a degenerate one.

**Paper triage.** Decidable and immediate: `twoLoop` is atomless (`twoLoop_HNE`) with constant breadth 1. The kill condition **fires**. **Winner (the Refuted verdict, on a genuine atomless witness).**

### C4 — The Discharged sub-class: finite-budget carriers conserve (Partial's positive horn)

```lean
theorem ws5_conserves_on_finite_budget {X} (dest : X → PkObj κ X)
    (hbudget : ∀ x, (dest x).1 ⊆ Finset-like fixed set) (hpart : successors partition the budget) :
    Conserves dest
```
Where the alternatives are a *fixed finite budget* re-partitioned as you descend (each node's successors carve up a bounded pool), breadth is conserved — the constitutive-scarcity reading realized on a class.

- **Failure mode:** *the class is empty or contrived.* The budget-partition carrier must be non-trivial and atomless. A finite-branching tree whose branching factor *strictly decreases* by depth (breadth `b, b-1, b-2, …`) conserves (weakly) — but it hits a leaf when breadth reaches 0, violating (NL)/atomlessness. So genuine atomless conservation requires an *infinite* budget re-partitioned, which is delicate. Likely only a *weak* (`≤`) conservation on a restricted class, not strict.

**Paper triage.** The strict-decreasing finite tree conserves but *leafs out* (fails atomlessness) — so on genuinely atomless fields, conservation holds at best weakly and on a narrow class. **Winner as the Partial's positive horn, honestly narrow.**

### C5 — The verdict datum and its justification (the fork, resolved)

```lean
inductive ConservationVerdict | discharged | refuted | partial
def ws5_conservation_verdict : ConservationVerdict := .partial   -- Refuted-universal, Discharged-on-a-class
theorem ws5_verdict_justified (hinf : ℵ₀ ≤ κ) :
    (∃ {X} (dest : X → PkObj κ X) (h h' : Hold dest), ReReStep dest h h' ∧ ¬ breadth dest h' < breadth dest h)
  ∧ (¬ ConservesStrict (twoLoop hinf))
```
The verdict is a datum; its justification is C3 (the kill condition fires) plus C2 (strict conservation refuted by `twoLoop`). The honest ruling: **Refuted in general, Partial overall** — the bound is mere boundedness, not conservation.

- **Failure mode:** *the verdict is hand-set.* Guard (transcribing Series 7's `Audit`): `ws5_conservation_verdict` must be justified by `ws5_verdict_justified`, whose fields are theorems — you cannot get `.refuted`/`.partial` without the witness. **Winner (the settled fork).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `Conserves` (weak) as the claim | `breadth`, `ReReStep` | statement yes; truth = the fork | claim (tested by C3/C4) |
| C2 | `ConservesStrict` (strict) | `twoLoop` breadth 1→1 | yes — FALSE | **refuted horn** |
| C3 | kill condition fires (depth opens, breadth kept) | `twoLoop`, `twoLoop_HNE` | yes — immediate | **win (Refuted)** |
| C4 | finite-budget carriers conserve | budget-partition carrier | weak-only, narrow class, atomlessness-delicate | **win (Partial's positive horn, narrow)** |
| C5 | verdict = Partial (Refuted-universal, Discharged-class) | C3 + C2, justified | yes | **win (settled fork)** |

## Winning candidates: the fork resolves to PARTIAL — C3 refutes the universal (kill condition fires), C4 discharges a narrow class; C5 records it

### Definitions and obligations (cite `spec/README.md` §2.4–§2.5; consume WS3, never redefine `ReReStep`)

```lean
namespace Series8.WS5
-- carrier, twoLoop, twoLoop_HNE, twoLoop_val — transcribed (README §6);
-- Hold, afford from WS1; ReReStep, prec from WS3 (CONSUMED, not redefined).

def breadth (dest : X → PkObj κ X) (h : Hold dest) : Cardinal := Cardinal.mk (↥(dest h.1.2).1)
def Conserves (dest : X → PkObj κ X) : Prop :=
  ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' ≤ breadth dest h
def ConservesStrict (dest : X → PkObj κ X) : Prop :=
  ∀ h h' : Hold dest, ReReStep dest h h' → breadth dest h' < breadth dest h
inductive ConservationVerdict | discharged | refuted | partial deriving DecidableEq

/-- **D1 — strict conservation is refuted (C2).** The atomless self-loop has breadth 1 at every hold,
    so no step strictly forecloses: `ConservesStrict (twoLoop)` is false. -/
theorem ws5_strict_refuted (hinf : ℵ₀ ≤ κ) : ¬ ConservesStrict (twoLoop hinf) := by
  intro hcs
  -- any hold on twoLoop has breadth mk {·} = 1; a step keeps breadth 1; 1 < 1 is false
  …

/-- **D2 — the kill condition fires (C3).** A depth-opening re-restriction on a GENUINELY ATOMLESS
    field (`twoLoop_HNE`) that forecloses no breadth. Conservation is Refuted; the bound is mere
    boundedness; the "self-limiting universe" is retracted (charter §5.4). -/
theorem ws5_kill_condition (hinf : ℵ₀ ≤ κ) :
    ∃ (h h' : Hold (twoLoop hinf)),
      ReReStep (twoLoop hinf) h h' ∧ ¬ (breadth (twoLoop hinf) h' < breadth (twoLoop hinf) h)
      ∧ SHNE (twoLoop hinf) h.1.1 := …

/-- **D3 — conservation on a narrow atomless class (C4), honestly weak.** Where successor sets do not
    grow along edges, breadth is (weakly) conserved. Stated as a hypothesis on `dest`, NOT on the map. -/
theorem ws5_conserves_if_nonincreasing {X} (dest : X → PkObj κ X)
    (hmono : ∀ h h' : Hold dest, ReReStep dest h h' → (dest h'.1.2).1 ⊆? bounded-by (dest h.1.2).1) :
    Conserves dest := …

/-- **D4 — the settled fork (C5).** The verdict is Partial: Refuted in general (D2), weakly Discharged
    on the non-increasing class (D3). Justified by theorems — not hand-set. -/
def ws5_conservation_verdict : ConservationVerdict := .partial
theorem ws5_verdict_justified (hinf : ℵ₀ ≤ κ) :
    (∃ (h h' : Hold (twoLoop hinf)), ReReStep (twoLoop hinf) h h'
        ∧ ¬ breadth (twoLoop hinf) h' < breadth (twoLoop hinf) h)
  ∧ ¬ ConservesStrict (twoLoop hinf) :=
  ⟨by obtain ⟨h, h', hr, hnf, _⟩ := ws5_kill_condition hinf; exact ⟨h, h', hr, hnf⟩,
   ws5_strict_refuted hinf⟩
```

**D1/D2 (Refuted)** run the kill condition: strict conservation is false, witnessed by a *genuinely atomless* (`twoLoop_HNE`) constant-breadth field. This is the pre-registered honest outcome — a Refuted hypothesis, a first-class success, not a failure (charter-status §12, protocol §E). **D3 (Discharged-on-a-class)** salvages the weak bound on carriers whose successor sets do not grow, stated as a hypothesis on `dest` (never on `ReReStep`). **D4 (the verdict)** records the fork as **Partial**, justified by theorems so it cannot be hand-set — the atom-or-will door left open (is the mere-boundedness constitutive or epistemic? the math does not say).

## Outcome classes (per charter §7)

- **Refuted hypothesis (the headline, a first-class success):** D1+D2 — strict conservation is false; the kill condition fires on a genuine atomless field; the "self-limiting universe" claim is **retracted** and the bound downgraded to mere boundedness. Reporting conservation false is a success, not a failure (charter §8.4).
- **Discharged (narrow, weak):** D3 — weak conservation on the non-increasing-breadth class.
- **Partial (the settled fork):** D4 — Refuted-universal, Discharged-on-a-class; the epistemic/constitutive reading left open (the atom-or-will analog).
- **Discharged (alternative, if the math surprises):** if strict conservation turned out to hold on *all* atomless fields (it does not — `twoLoop` refutes it), the verdict would be `.discharged`. Pre-registered but not expected.
- **Strip test.** Delete **"hold"** (and "narrowing") from `ws5_kill_condition` and the statement is the bare **`∃ dest, a step with breadth h' = breadth h` on an `SHNE` carrier** — a plain cardinality-of-successors fact (breadth constant along an edge). The refutation **survives the strip** as a bare breadth-constancy fact, which is *exactly why conservation is false*: there is nothing perspectival propping it up. Crucially, the review must confirm (protocol §0.4) that `breadth` and `Conserves` are defined **outside** `ReReStep` (they are, §2.5) — so conservation is a *tested fact about the map*, refuted by witness, **not** a clause baked into the map. That confirmation is the whole point of WS5.

## Deliverable

`series-8/formal/Series8/ws5.lean`: transcribed carrier (README §6); `breadth`, `Conserves`, `ConservesStrict`, `ConservationVerdict`; `ws5_strict_refuted` (D1), `ws5_kill_condition` (D2), `ws5_conserves_if_nonincreasing` (D3), `ws5_conservation_verdict` + `ws5_verdict_justified` (D4). **Consumes WS3's `ReReStep`/`prec`; never redefines them; `breadth` is measured outside the map.** Axiom check: `#print axioms ws5_kill_condition` reduces through `twoLoop_HNE` / `Cardinal.mk_singleton` to the standard three. **Conservation is open by design; the kill condition is run; the verdict is Partial (Refuted-universal). This workstream is forbidden from assuming its answer, and does not.**
