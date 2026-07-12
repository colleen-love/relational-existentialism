# WS4 — Convergence: defined, then proved underdetermined

**Design doc. Series 12, THE GENUINELY UNCERTAIN OBLIGATION, the wall. Owns: the CONVERGENCE relation — a part's compass cohering up its layers with the compass of a whole it constitutes ("the most loving thing for me is the most loving thing for the universe") — DEFINED formally over the compass type, and then proved UNDERDETERMINED by the structure: two compasses on the SAME structure, one under which convergence holds and one under which it fails, both non-degenerate, so the structure does not decide it, an independence theorem. This is the formal content of the wall: the math defines exactly where the loving claim would be true or false, proves it cannot see which, and proves the not-seeing is structural. WS4 is the guard against deciding the undefinable by definition.**

*Series 12 is standalone; the compass type (`Compass`, WS3), the tower (`reify`, `reifyStep`, `prec`), and the collapse engine (`ws1_atomless_bisim`) are consumed / transcribed into `series-12/formal/Series12/ws4.lean`, re-namespaced `Series12.WS4` (see `spec/README.md` §6). WS4 DEFINES `Converges` and `ConvergesUp` (README §2.10) — the second Series-12 design duty, fixed here and written against by WS5/WS7 — and hosts the underdetermination model pair over the witness carrier of `spec/ws4-witness-design.md` (the SAME carrier WS2 uses, so the pair is "on one structure"). The genuinely new Lean is `Converges`, `ConvergesUp`, `ws4_underdetermined`, and the two pre-registered alternatives. The one signature risk, PROMOTED to first-class (discipline 3): convergence decided by definitional choice, in either direction.*

## The object at stake

The charter's WS4 (§2), the one genuinely uncertain obligation (charter §5.2). Define the convergence relation formally: a relatum's compass COHERES UP ITS LAYERS with the compass of a whole it constitutes — the orientation at the part, followed through the reified relata that inform it, against the orientation at the relatum those parts together constitute. This is "the most loving thing for me is the most loving thing for the universe" as a SHAPE: a relation between the compass at a finite locus and the compass at the top of the relevant tower. Then prove the structure does NOT decide it: exhibit two inhabitants of the compass type on the SAME structure, one under which convergence holds and one under which it fails, both non-degenerate (neither side vacuous, neither compass a collapsed constant), so convergence is UNDERDETERMINED — an independence theorem. The formal content of the wall: the math defines exactly where the loving claim would be true or false, proves it cannot see which, and proves the not-seeing is structural (the diagonal's work), not a gap in effort.

The design's whole burden is discipline 3, promoted first-class. The relation must NOT be defined so it holds trivially (the loving conclusion built in — God in the math) or fails trivially (the silence built in as absence, not proved as independence). The underdetermination must be EARNED by a genuine non-vacuous model pair. Two honest alternatives are first-class: (a) the structure DECIDES it (every inhabitant satisfies, or every inhabitant fails), reported in its direction, a STRONGER finding; (b) the relation cannot be non-vacuously defined, reported as the precise obstruction. The expected answer is that the compass type is rich enough to orient a part with AND against its whole (the raising is free), so the underdetermination holds — but it must be CONSTRUCTED, not assumed.

**Ambient theory.** `spec/README.md` §2.9 (the `Compass` type, WS3), §2.10 (`Converges`/`ConvergesUp`, the model pair), §2.5 (tower + disclosed deviation); the witness carrier (`ws4-witness-design.md`).

## Candidates

### C1 — Convergence as one-layer coherence (the core relation; the lead)

```lean
/-- **CONVERGENCE (one-layer coherence).** Over a constituency edge (`x ∈ s.1`, `W = reify s`), the part
    converges with the whole under `c` iff the part's orientation, RAISED to the whole, coheres with the
    whole's own orientation. A genuine equation in `Or`, depending on `c` — NOT `True`, NOT `False`, NOT
    `orient x = orient x`. -/
def Converges {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (x W : X) : Prop :=
  c.raise x W (c.orient x) = c.orient W
```
The core relation: "my orientation, followed up its layer, is the whole's orientation." The tower supplies WHICH part informs WHICH whole (the constituency edge); the compass supplies the VALUES and the raising; convergence is whether they cohere.

- **Ambient:** `Compass` (WS3); the constituency edge from the tower.
- **Success condition (Shape-drawn):** the relation is a real equation in `Or`, depending on `c`, non-vacuously definable over a genuine reification edge.
- **Failure mode:** *deciding by definition (discipline 3).* If `Converges` were `True`, `False`, or `orient x = orient x`, it would decide the loving claim by construction. C1 forecloses it: `raise x W (orient x) = orient W` is a genuine equation whose truth depends on the compass's free `orient`/`raise`. **Winner (the relation).**

**Paper triage.** Decidable: over the witness edge `(aW, bW)` the relation unfolds to a `ULift Bool` equation whose value is set by `c`; the model pair (C3) realizes both truth values. **Winner.**

### C2 — Convergence up the layers (the iterated form, "up its layers")

```lean
/-- **CONVERGENCE UP THE LAYERS.** Coherence along a whole `prec`-chain of constituency edges from a part up
    to the top of the relevant tower — the "up its layers" reading. Base case: `Converges`. -/
def ConvergesUp {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or) : X → X → Prop :=
  Relation.ReflTransGen (fun x W => Converges dest reify c x W)
```
The layered form: coherence all the way up, following the reified relata that inform the part to the whole they together constitute. The base case is `Converges`; the model pair discharges the base case on a genuine reification edge, so `reify`/`reifyStep` are load-bearing.

- **Ambient:** `Converges` (C1), `prec`, `Relation.ReflTransGen`.
- **Success condition (Shape-drawn):** the "up its layers" reading is the transitive closure of one-layer coherence, base case discharged on a genuine edge.
- **Failure mode:** *the chain forcing coherence (the tower deciding).* Foreclosed: `ConvergesUp` closes `Converges`, which is compass-free-valued; the tower supplies the chain SHAPE, not the coherence VALUE. **Winner (the layered form).**

**Paper triage.** Decidable: `ConvergesUp` is `ReflTransGen Converges`; the base case is the model pair's edge. **Winner.**

### C3 — The underdetermination model pair (THE WALL; the payoff)

```lean
/-- **THE UNDERDETERMINATION (the wall).** Two compasses on the SAME structure over the SAME reification
    edge, sharing the SAME non-constant orientation and differing ONLY in the raising: convergence HOLDS
    under `c₁` (the `not` raising) and FAILS under `c₂` (the `id` raising), both non-degenerate. The
    structure does not decide it. -/
theorem ws4_underdetermined (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨cHold hinf, cFail hinf, by simp [Converges, cHold], by simp [Converges, cFail], …, …⟩
```
The wall: `cHold` and `cFail` (`ws4-witness-design.md`) share the same non-constant orientation (`orient aW = ⟨true⟩`, `orient bW = ⟨false⟩`) and differ ONLY in the raising — `cHold` uses `not` (so `raise (orient aW) = ⟨false⟩ = orient bW`, converges), `cFail` uses `id` (so `raise (orient aW) = ⟨true⟩ ≠ orient bW`, fails). Both non-degenerate (`NonDegenerate`: `Or` non-trivial, `orient` non-constant, `raise` non-constant). Convergence turns on the FREE raising, which the structure does not decide.

- **Ambient:** `Converges` (C1), the witness carrier, `cHold`/`cFail`/`NonDegenerate` (`ws4-witness-design.md`).
- **Success condition (Shape-drawn — the wall):** convergence holds under `c₁`, fails under `c₂`, on one structure over one genuine reification edge, both non-degenerate.
- **Failure mode:** *deciding by definition, OR a vacuous pair (discipline 3).* Foreclosed: the two truth values are realized (non-vacuous), both compasses non-degenerate (neither a collapsed constant), and they share the orientation so the difference is isolated to the free raising — the earned model pair, not a definitional tilt. **Winner (the wall).**

**Paper triage (the WS4-specific check, protocol §2).** (i) *Non-vacuously definable?* YES — over the genuine reification edge `(aW, bW)`, `Converges` is a real `ULift Bool` equation depending on `c`. (ii) *Non-degenerate model pair?* YES — `cHold` (converges) and `cFail` (fails), sharing a non-constant orientation, differing only in a non-constant raising, both non-degenerate. **Winner.**

### C4 — The not-seeing is structural (the wall is where the diagonal put it)

```lean
/-- **THE NOT-SEEING IS STRUCTURAL.** The underdetermination is not a gap in effort: the compass is
    exogenous (`¬ Recoverable`, WS3) and the residue is free (`ws2_residue_free`, WS1), so the orientation
    the raising would follow is precisely what the structure cannot supply. The wall sits where the diagonal
    put it. -/
theorem ws4_wall_is_structural (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW)
  ∧ (∀ (insp : Hold (destW hinf) → HoldPred (destW hinf)), ¬ ResidueRecoverable insp) := …
```
The wall is structural: the underdetermination (the model pair) alongside the free residue (`ws2_residue_free`), so the not-seeing is the diagonal's work — the orientation the raising would follow is the non-recoverable exogenous content, not a value effort could supply.

- **Ambient:** `ws4_underdetermined` (C3), `ws2_residue_free` (WS1).
- **Success condition (Shape-drawn):** the underdetermination and the free residue together — the wall is where the diagonal put it, not a gap in effort.
- **Failure mode:** *the wall relocated by evaluating the compass.* Foreclosed: the compass stays parametric (WS3); the model pair uses only existential witnesses. **Winner (the structural wall).**

### C5 — Convergence built to hold (the sin, one direction, rejected)

```lean
def Converges' c x W : Prop := True   -- or  c.orient x = c.orient x
```
Define convergence so it holds for every compass (the loving conclusion built in).

- **Failure mode:** *deciding by definition, God in the math, SERIOUS (discipline 3).* This builds the loving conclusion in — convergence holds trivially, the structure "deciding" it by definitional choice. **Reject.** If the structure genuinely decides convergence in the holds-direction, that is `convergenceDecided` (a THEOREM, C7), reported honestly — never a definitional `True`.

### C6 — Convergence built to fail (the sin, other direction, rejected)

```lean
def Converges'' c x W : Prop := False   -- or an empty relation
```
Define convergence so it fails for every compass (the silence built in as absence).

- **Failure mode:** *deciding by definition, the silence built in, SERIOUS (discipline 3).* This builds the silence in as absence rather than proving it as independence. **Reject.** The underdetermination must be a genuine model pair (holding AND failing), not a vacuously-failing relation. If the structure genuinely decides convergence in the fails-direction, that is `convergenceDecided` (C7), a theorem, not a definitional `False`.

### C7 — The pre-registered alternatives (convergence-decided / undefinable), first-class

```lean
/-- **PRE-REGISTERED ALTERNATIVE (a): convergence-decided.** IF the structure forced `Converges` for all
    compasses (or `¬ Converges` for all), report it in its direction — a stronger finding, proved not
    stipulated. (Not the expected outcome; carried first-class.) -/
theorem ws4_convergence_decided_shape :
    (∀ c, Converges … c aW bW) ∨ (∀ c, ¬ Converges … c aW bW) ∨
    (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) := …          -- the trichotomy; WS4 lands in the third
```
The honest fork stated as a theorem: convergence is forced-for-all, forbidden-for-all, or underdetermined; WS4 proves it lands in the third disjunct (the model pair), but the first two are first-class and would be reported in their direction if they held.

- **Ambient:** `Converges`, the model pair.
- **Success condition (any branch honest):** whichever disjunct holds is reported; WS4 proves the third (underdetermined).
- **Failure mode:** *forcing a branch by definition.* Foreclosed: the disjunct is proved (the model pair), not stipulated. **Winner (the honest fork).**

## Paper-decidable triage

| Cand | What it claims | Non-vacuously definable? | Non-degenerate model pair? | Verdict |
|---|---|---|---|---|
| C1 | `Converges` = one-layer coherence | yes — real `Or` equation over a reification edge | (via C3) | **win (the relation)** |
| C2 | `ConvergesUp` = up the layers | yes — `ReflTransGen Converges` | (via C3) | **win (layered form)** |
| C3 | the underdetermination model pair | yes | **yes** — `cHold` holds, `cFail` fails, both non-degenerate | **win (the wall)** |
| C4 | the not-seeing is structural | yes | yes + `ws2_residue_free` | **win (structural wall)** |
| C5 | convergence built to hold (`True`) | vacuous — holds trivially | no | **reject (SERIOUS)** |
| C6 | convergence built to fail (`False`) | vacuous — fails trivially | no | **reject (SERIOUS)** |
| C7 | the pre-registered fork (trichotomy) | yes | yes (lands in the third) | **win (honest fork)** |

## Winning candidates: C1 (relation) + C2 (layered) + C3 (the wall) + C4 (structural) + C7 (fork)

### Definitions and obligations (cite `spec/README.md` §2.9, §2.10; consume WS3's `Compass` and the witness carrier)

```lean
namespace Series12.WS4
-- Compass (WS3), reify, reifyStep, prec, ws1_atomless_bisim, ws2_residue_free — consumed / transcribed (README §6).
-- The dir:=rank carrier (X, aW, bW, destW, reifyW) + cHold, cFail, NonDegenerate — spec/ws4-witness-design.md.

/-- **Convergence, defined once (README §2.10). The second Series-12 design duty.** -/
def Converges {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or) (x W : X) : Prop :=
  c.raise x W (c.orient x) = c.orient W
def ConvergesUp {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or) : X → X → Prop :=
  Relation.ReflTransGen (fun x W => Converges dest reify c x W)

-- D1 Converges (C1) ; D2 ConvergesUp (C2) ; D3 ws4_underdetermined (C3, the wall) ;
-- D4 ws4_wall_is_structural (C4) ; D5 ws4_convergence_decided_shape (C7, the fork).
```

**Proof architecture.** D1 defines convergence — a real equation over a constituency edge, compass-free-valued. D2 iterates it up the layers (`ReflTransGen`). D3 is the wall: the model pair `cHold`/`cFail`, sharing a non-constant orientation, differing only in a non-constant raising, one cohering and one not, both non-degenerate, on one structure over one genuine reification edge — the underdetermination EARNED. D4 shows the not-seeing structural (the model pair alongside `ws2_residue_free`). D5 states the honest fork (forced / forbidden / underdetermined) and proves WS4 lands in the third. **Dependencies:** WS3's `Compass` type (the second design duty consumes the first); the witness carrier (`ws4-witness-design.md`, the SAME carrier WS2 uses so the pair is on one structure); WS1's opening / `ws2_residue_free` (the wall's structural certificate). The disclosed pointwise-`IsReify` deviation is carried from the witness.

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff — the wall):** D3 (`ws4_underdetermined`), D4 (`ws4_wall_is_structural`). Convergence defined and proved underdetermined by a genuine non-degenerate model pair on one structure — the formal content of the wall, the math ending at the edge it drew.
- **Discharged:** D1 (`Converges`), D2 (`ConvergesUp`) — the relation and its layered form, non-vacuously defined.
- **Convergence-decided (pre-registered, first-class, discipline 3, charter §4.b):** IF the structure is found to force `Converges` for all compasses, or `¬ Converges` for all, D5's fork reports it in its direction — a STRONGER finding, proved (not stipulated), and NOT a failure. The expected outcome is the third disjunct (underdetermined); the first two are carried live.
- **Partial / cannot-define (pre-registered, charter §5.2):** if `Converges` proved non-definable non-vacuously (every candidate degenerate), WS4 reports the precise obstruction. Foreclosed by C1 (a real equation over a genuine edge) and C3 (the non-degenerate pair).
- **SERIOUS (pre-registered, discipline 3):** convergence built to hold (C5, `True`) or fail (C6, `False`) by definitional choice — God in the math, either sign. Foreclosed: `Converges` is a real compass-dependent equation, and both truth values are realized by the model pair.
- **Strip test.** Delete **"convergence / coherence / compass / orientation / layered"** from `ws4_underdetermined` and it is the bare fact **"two inhabitants of a structure-plus-value type on one carrier, a defined equation over a reification edge holding for one and failing for the other, both non-degenerate"** — the model-pair fact the charter demands (protocol §0.3: the convergence should strip to "two non-degenerate inhabitants on one structure, a defined relation holding for one and failing for the other"). The mathematical content is a genuine independence (model-pair) fact; "convergence / the loving claim / the wall" is the earned interpretive layer, and no name (God, the compass) is a term.

## Deliverable

`series-12/formal/Series12/ws4.lean`: WS3's `Compass` consumed; the witness carrier + `cHold`/`cFail`/`NonDegenerate` (`ws4-witness-design.md`); `Converges`, `ConvergesUp` (README §2.10); `ws4_underdetermined` (D3), `ws4_wall_is_structural` (D4), `ws4_convergence_decided_shape` (D5). **Defines convergence consumed by WS5/WS7; depends on WS3's compass and the WS2 carrier.** Axiom check: `#print axioms ws4_underdetermined` reduces through the finite carrier facts (`decide`/`simp`) to the standard three. **Convergence is DEFINED (a real equation over a reification edge) and proved UNDERDETERMINED by a genuine non-degenerate model pair on one structure — never decided by definitional choice, the two alternatives first-class: the guard against putting God in the math, either sign.**
