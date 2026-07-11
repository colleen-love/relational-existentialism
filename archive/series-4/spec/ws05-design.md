# WS5 — The self-bounding of the world

**Design doc. Series 4. Owns the "grain, not wall" thesis: that the world is set-sized because faces are parts of sources, not because a size was imposed. Adjudicates three bounding mechanisms.**

*References: `PkObj`, `Coalg`, `IsTerminalCoalg`, `lambek`, `exists_terminal_coalg`, `omegaCoalg` (ws1); `Reaches`, `ReachSet`, `level`, `ws12_reachable_card_le`, `carrier_card_ge` (ws10/ws12); `face`, `ws1_omega_face` (WS1). The conceptual target is the charter's §3.2 (three mechanisms) and §5.3 (self-cost).*

## The object at stake

Series 3 bounded the world by **fiat**: it chose `PkObj κ` (a cardinal cap) rather than the full powerset, because the full-powerset final coalgebra provably does not exist as a set (Lambek + Cantor). WS5 asks: **can the same set-sizedness be obtained from the face structure instead of from the cap?** If yes, the bound is the world's grain (you can only face part of yourself toward another) rather than a wall (we capped it). This is the most *philosophically* load-bearing workstream and the one with the subtlest failure mode (a hidden well-foundedness that betrays groundlessness).

## The three mechanisms (charter §3.2), as candidates

### M1 — Contraction: the face-carrying functor is not size-increasing
The Cantor wall is powered by successors ranging over the *whole carrier*. If the face component ranges over sub-objects of the *source*, the functor may fail to strictly increase cardinality, so Lambek permits a set-sized fixed point *without* a cap.
```lean
/-- The restriction functor does not strictly increase cardinality. -/
theorem ws5_not_size_increasing (X) : Cardinal.mk (RFObj κ X) ≤ (bound in terms of X, not 2^X)
```
**Paper triage.** Decidable to state; the check is whether `RFObj`'s face component is bounded by `X`'s own structure. *But there is a trap, decidable on paper:* the successor component of `RFObj` is *still* a powerset-like `PkObj κ X` (a state still has a set of successors drawn from the carrier). Faces constrain the *decoration*, not the *branching*. So M1 as "the functor isn't size-increasing" is **false unless the face constraint also tames the successor set** — which it does not, on the R2/R3 readings. **Verdict: M1 does not eliminate the cap by itself.** The successor breadth still needs bounding; faces alone don't do it. Record this as a sharp negative: *faces bound the quality, not the branching, so contraction alone cannot free the bound.*

### M2 — Congruence collapse: quotient by same-face identifies the redundant multiplicity
Reachable-face is a congruence; two edges with the same face are relationally identical. Quotienting the *uncapped* carrier by same-face might collapse it to set size.
```lean
def SameFace (e₁ e₂ : Edge) : Prop := face_of e₁ = face_of e₂
theorem ws5_quotient_set_sized : Cardinal.mk (UncappedCarrier / SameFace) < someBound
```
**Paper triage.** Decidable-leaning-negative. The quotient identifies edges with equal faces, but distinct *states* (with distinct hereditary face-structure) survive, and WS3's plurality shows there are many — plausibly still a proper class if uncapped. The quotient tames edge-redundancy, not state-proliferation. **Verdict: M2 helps count edges, not states; insufficient alone.** Another honest negative.

### M3 — Ordinal (rank) bound with a groundless diagonal (the real candidate)
If faces are *strictly smaller* along relations off the self-loops, the face-defining recursion is well-founded *in the quality dimension* while objects stay groundless *in the state dimension*. A rank function on faces bounds the world by an ordinal, replacing the cardinal cap — **provided** faces stay *improper* exactly on the self-loops (so `Ω↾(Ω,Ω)=Ω`, ws1's `ws1_omega_face`, and groundlessness survives on the diagonal).
```lean
/-- Off the diagonal, the face is a strict sub-object of the source. -/
def FaceShrinks : Prop := ∀ x y, y ∈ succ x → x ≠ y → face x y ⊊ ReachSet x
/-- On the diagonal, the face is improper. -/
theorem ws5_diagonal_improper : ∀ x, x ∈ succ x → face x x = ReachSet x → (x is a self-loop spine point)
```
**Paper triage — the decisive one.** M3 is the only mechanism that could genuinely make the bound endogenous, and it carries the charter's named trap (§3.2, §9): if `FaceShrinks` holds *everywhere including the diagonal*, there is a global rank function, the world is well-founded, and it **has atoms-in-disguise** (the rank-minimal faces) — betraying charter point 3. The escape is that `FaceShrinks` must hold **off** the diagonal and *fail* **on** it. So the paper-decidable test is:

> Is there a coherent structure where faces strictly shrink along every non-loop edge but are improper on loops?

This is decidable to *state* precisely and is the actual mathematical content of WS5. The self-loops (Ω and its kin) are the fixed points of "face = whole"; everything else shrinks. Whether this is consistent — whether a carrier with exactly this profile exists and is groundless — is the theorem.

**Winner: M3, with M1 and M2 reported as sharp negatives (they clarify *why* only M3 can work — faces tame quality, not branching, so only a rank-on-quality with a groundless diagonal can convert the bound).**

## The M3 construction, in detail

```lean
namespace Series4.WS5

/-- Rank of a state by the well-founded depth of its off-diagonal faces. -/
noncomputable def faceRank (x : (νPk κ).X) : Ordinal := ...
  -- defined by well-founded recursion on the strict-shrink relation off the diagonal

/-- Off-diagonal shrink + on-diagonal improperness. -/
structure GroundlessDiagonal where
  shrinks_off  : ∀ x y, y ∈ succ x → x ≠ y → face x y ⊊ ReachSet x
  improper_on  : ∀ x, x ∈ succ x → (self-loop) → face x x = ReachSet x
  groundless   : ∀ x, HereditarilyNonempty x   -- no atoms, despite the rank

/-- The payoff: a set-sized groundless world whose bound is the face-rank,
    not an imposed cardinal. -/
theorem ws5_endogenous_bound (G : GroundlessDiagonal) :
    (the carrier is set-sized) ∧ (∀ x, HereditarilyNonempty x)
```

### The consistency question (the crux, paper-decidable to frame)

`GroundlessDiagonal` looks self-contradictory at first glance: `groundless` says no atoms (descent never terminates), while `faceRank` is well-founded (descent in *faces* terminates). The resolution — and the reason it is *consistent* — is that these are **two different descents**: the *state* descent (successors) is infinite (groundless), the *quality* descent (faces shrinking) is well-founded (bounded). The self-loops are where the two decouple: Ω descends forever in states (Ω → Ω → …) but its face never shrinks (improper), so Ω has no face-rank drop yet is maximally groundless. **Paper-decidable check:** the two relations (successor, face-strict-subset) are distinct, and well-foundedness of one is compatible with ill-foundedness of the other — yes, standard (a relation can be well-founded while a different relation on the same set is not). So `GroundlessDiagonal` is *not* obviously inconsistent, and the design task is to *exhibit* a witness.

### Witness candidate

```lean
-- A "shrinking tree with loops at the leaves-that-aren't-leaves":
-- states of finite face-rank r > 0 face strictly-smaller-rank parts;
-- rank-0 states are self-loops (Ω-like), improper-faced, groundless.
def shrinkingWitness : Coalg κ := ...
theorem ws5_witness_groundless_diagonal : GroundlessDiagonal (from shrinkingWitness)
```
**Paper triage:** the witness must have *every* rank-0 state be a self-loop (so groundlessness is carried entirely by the diagonal) and every positive-rank state shrink. Decidable to construct; the risk is that shrinking + groundless forces *all* states onto the diagonal (i.e. the only groundless states are loops), collapsing plurality. If so, WS5 delivers a *conditional* bound (endogenous on the loop-spine, but plurality lives off it where the bound is not yet endogenous) — an honest Partial.

## The coincidence duty / trivialization guard (charter §7)

WS5's trivialization risk is specific: declaring the bound "endogenous" by *defining* `faceRank` and *asserting* it bounds. The forced form: prove the M1/M2 negatives (faces don't tame branching or state-count), so that M3's rank is doing *non-trivial* work that the cap was doing before — and prove the `GroundlessDiagonal` witness exists rather than positing it. WS7 audits that `ws5_endogenous_bound` is not secretly re-importing `carrier_card_ge`'s cap.

## Outcome classes

- **Discharged:** M1/M2 negatives + `ws5_endogenous_bound` with an exhibited `GroundlessDiagonal` witness → the bound is grain, headline positive.
- **Partial (plausible honest status):** endogenous bound proved on the self-loop spine, but plurality-bearing off-spine states still need the cap — the bound is *partly* endogenous. Named residue: extend the groundless diagonal to carry plurality.
- **Impossibility proved:** if `GroundlessDiagonal` is inconsistent (shrink + groundless forces all states onto the diagonal, killing plurality) — a sharp negative meaning the bound *cannot* be freed from fiat while keeping plurality. This would be a major (if disappointing) finding, directly answering the charter's central question in the negative.

## Deliverable

`series-4/formal/ws5.lean`: `ws5_not_size_increasing` (M1 negative), `ws5_quotient` (M2 negative), `faceRank`, `GroundlessDiagonal`, `shrinkingWitness`, `ws5_witness_groundless_diagonal`, `ws5_endogenous_bound`. Each of M1/M2 recorded as a *reportable negative*, not a silent drop. Axiom check owed; the well-founded `faceRank` recursion is the spot to watch for hidden `Classical` use.
