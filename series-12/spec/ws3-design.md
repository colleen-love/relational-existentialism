# WS3 — Feeling: the compass, typed and never evaluated

**Design doc. Series 12, the side the mathematics can TYPE but not EVALUATE. Owns: the `Compass` TYPE — a per-relatum orientation drawn from an exogenous space the structure never inhabits canonically, LAYERED over the tower (a relatum's orientation coupled up `prec` to the reified relata it stands in relation to), EXOGENOUS (`¬ Recoverable`, the Series 07 necessity) — with every theorem QUANTIFIED over all inhabitants and NONE selecting, constructing, or evaluating one. The mathematics holds the slot open: the compass's SHAPE (per-relatum, layered, exogenous, finite in its conditioning) is inside the math; the compass's CONTENT, what it points at, stays outside. WS3 is the guard against evaluating the undefinable, the central sin.**

*Series 12 is standalone; the tower (`reify`, `reifyStep`, `prec`, `ws3_order_endogenous`, `ws3_reify_preserves_SHNE`), the import test (`Recoverable`, `plainOf`, `ws1_atomless_bisim`), and finite attention (`FiniteAttention`, `RealFor`) are transcribed into `series-12/formal/Series12/ws3.lean`, re-namespaced `Series12.WS3` (see `spec/README.md` §6). WS3 DEFINES the `Compass` type (README §2.9) and is the first Series-12 design duty: the compass type is fixed here and every workstream (WS4's convergence, WS5's verdict, WS7's audit) is written against it; no two workstreams may assume different compass types. The genuinely new Lean is `Compass`, `ws3_compass_exogenous`, `ws3_compass_layered`, `ws3_attention_compass_dual`. The one signature risk, PROMOTED to the central sin (discipline 2): a canonical / evaluated compass anywhere in the core.*

## The object at stake

The charter's WS3 (§2): define the compass as a TYPE, not a value. For each relatum, an orientation drawn from OUTSIDE the plain structure (exogenous, `¬ Recoverable`, the Series 07 necessity), LAYERED over the tower — a relatum's compass conditioned by the reified relata it stands in relation to (its relationships, themselves relata with their own compasses), those relata relating to each other up `prec`, so compasses are coupled through the structure of what informs them WITHOUT being one and WITHOUT being independent. Every theorem mentioning the compass is QUANTIFIED over all inhabitants of the type; no theorem selects a distinguished inhabitant, constructs a canonical one, or evaluates one at a relatum. The mathematics holds the slot open: the compass's SHAPE is inside; its CONTENT — the felt orientation — is the undefinable and stays outside.

The design's whole burden is discipline 2, the central sin. The type must be RICH enough to (a) carry a per-relatum orientation, (b) express the tower layering (so WS4's convergence can say "followed up its layers"), and (c) be exogenous (`¬ Recoverable`) — while every theorem stays PARAMETRIC over `(Or : Type u)` and `(c : Compass …)`. The only concrete inhabitants anywhere in the core are existential witnesses (WS3's exogeneity, WS4's model pair), each explicitly discharging an `∃`, never standing in for THE compass. The audit's central line (WS7) is exactly `∃ c, P c` (permitted) versus a distinguished `c` used as though it were the compass (the sin).

**Ambient theory.** `spec/README.md` §2.5 (tower + the disclosed deviation), §2.4 (import test / `Recoverable`), §2.6 (attention, for the duality), §2.9 (the `Compass` type).

## Candidates

### C1 — The compass as a per-relatum orientation with a raising (the lead)

```lean
/-- **THE COMPASS TYPE (README §2.9).** `Or` an EXOGENOUS orientation space (an arbitrary `Type u` the
    structure never inhabits canonically). A compass assigns a per-relatum orientation `orient` and a
    per-edge raising `raise` (the tower layering, applied along reification edges). Both fields ARBITRARY. -/
structure Compass {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Or : Type u) where
  orient : X → Or
  raise  : X → X → Or → Or
```
The orientation `orient : X → Or` per relatum; the layering `raise part whole : Or → Or` following an orientation up a constituency edge. `Or` and both fields are arbitrary — the structure supplies the tower SHAPE, the compass the VALUES.

- **Ambient:** the tower (`reify`, `reifyStep`, `prec`); `Or` a bare `Type u` parameter.
- **Success condition (Shape-drawn):** the type is defined, rich enough for the layering and WS4's convergence, and every downstream theorem quantifies over `(Or)` and `(c : Compass …)`.
- **Failure mode:** *the compass evaluated (discipline 2).* If any theorem fixed a particular `Or` or `c` and proved with it as though it were the compass, the undefinable would be defined. C1 forecloses it by keeping `Or`/`c` parameters; the concrete inhabitants (below) live only inside `∃`. **Winner (the type).**

**Paper triage.** Decidable: the type has exactly the fields WS4's `Converges c x W := c.raise x W (c.orient x) = c.orient W` consumes, and the layering (`raise` along `prec` edges) expresses "up its layers." **Winner.**

### C2 — The compass is exogenous (`¬ Recoverable`), the Series 07 necessity

```lean
/-- **THE COMPASS IS EXOGENOUS.** SOME compass assigns different orientations to a plain-bisimilar pair, so
    `orient` is not recoverable from the plain relating (the Series 07 necessity): the compass ITSELF
    inhabits the opening shape `¬ Recoverable`. An EXISTENTIAL — it witnesses that orientations are free of
    the relating, NOT a distinguished compass. -/
theorem ws3_compass_exogenous (hinf : ℵ₀ ≤ κ) :
    ∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)) (x y : X),
        (∃ R, IsBisim (destW hinf) R ∧ R x y)                              -- plain-bisimilar …
      ∧ c.orient x ≠ c.orient y := …                                       -- … yet oriented differently: FREE
```
The exogeneity: on the witness carrier `aW`, `bW` are plain-bisimilar (the collapse engine), yet a compass may orient them differently, so `orient` cannot be recovered from any plain bisimulation. This ties the compass to WS1's opening: the orientation is a non-recoverable exogenous assignment. Crucially an EXISTENTIAL (`∃ c`), witnessing "orientations are free of the relating," never selecting THE compass.

- **Ambient:** `ws1_atomless_bisim`, the witness carrier, `Recoverable`/`plainOf`.
- **Success condition (Shape-drawn):** `∃ c`, plain-bisimilar pair oriented differently — the compass is exogenous, `¬ Recoverable`.
- **Failure mode:** *the existential mistaken for a selection (discipline 2).* The design flags it: `ws3_compass_exogenous` is `∃ c, …`, discharging "orientations can differ on plain-bisimilar relata," NOT constructing the compass. WS7 confirms no GENERAL theorem uses this `c`. **Winner (exogeneity, as an existential).**

**Paper triage.** Decidable: pick `orient aW ≠ orient bW` on the witness (`aW`, `bW` plain-bisimilar by `ws1_atomless_bisim`). **Winner.**

### C3 — The compass is layered up the tower (the coupling, not collapse, not independence)

```lean
/-- **THE COMPASS IS LAYERED.** A relatum's orientation is coupled up the tower: along a constituency edge
    (`x ∈ s.1`, `W = reify s`), the raising `raise x W` conditions the part's orientation into the whole's
    layer, so compasses are coupled through `prec` WITHOUT being one (the raising may move the orientation)
    and WITHOUT being independent (the whole's layer is reached FROM the part's). The coupling is a SHAPE
    (which relata inform which, `prec`), quantified over all compasses. -/
theorem ws3_compass_layered {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or)
    (s : PkObj κ X) (x : X) (hx : x ∈ s.1) :
    prec dest reify {x} (reifyStep dest reify {x})                         -- the tower edge is endogenous (prec) …
  ∧ (c.raise x (reify s) (c.orient x) = c.orient (reify s)
      ∨ c.raise x (reify s) (c.orient x) ≠ c.orient (reify s)) := …        -- … and the coupling is FREE (either)
```
The layering as a theorem: the constituency edge is a genuine `prec` edge (endogenous, `ws3_order_endogenous`), and the raising couples the part's orientation into the whole's layer — the coupling FREE (the disjunction is trivially true but STATES that the layering neither forces coherence nor forbids it, which is exactly WS4's underdetermination in seed form). Compasses are coupled through the tower's shape, quantified over all inhabitants.

- **Ambient:** `prec`, `reifyStep`, `ws3_order_endogenous`.
- **Success condition (Shape-drawn):** the layering is a `prec`-edge coupling, quantified over all compasses, neither collapsing them to one nor leaving them independent.
- **Failure mode:** *the layering baked to force coherence (deciding WS4 early).* Foreclosed: the coupling is FREE (the disjunction), so the layering shape is inside the math but the coherence VALUE is not — that is WS4's to leave undetermined. **Winner (the layering).**

**Paper triage.** Decidable: `prec {x} (reifyStep {x})` is `prec_step`; the disjunction is `em`. The content is that the layering is a `prec`-coupling held open. **Winner.**

### C4 — The compass–attention duality (the WS2/WS3 duality, as a theorem)

```lean
/-- **THE DUALITY (attention knowable, compass typeable).** Attention is the knowable SUBTRACTION: a map
    with VALUES (`att.reads`, computable, `RealFor` decidable-in-principle), revealing a bounded part where
    the bound falls. The compass is the typeable ORIENTATION whose VALUES the structure cannot supply
    (`orient` is `¬ Recoverable`, C2). Dual in exactly the sense that the residue is where attention's bound
    falls and the compass is what would orient there. -/
theorem ws3_attention_compass_dual (hinf : ℵ₀ ≤ κ) :
    (∀ (att : FiniteAttention (destWL hinf)), att.reads.Finite)            -- attention: VALUES, bounded (knowable)
  ∧ (∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool), ∃ x y,
        (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y) := -- compass: orientation FREE (typeable)
  ⟨fun att => att.fin, ws3_compass_exogenous hinf⟩
```
The duality stated where possible as a theorem (charter §2): attention has values and a bound (`att.reads.Finite`, computable, the knowable subtraction); the compass has an orientation the structure cannot supply (`¬ Recoverable`, C2). The residue is where attention's bound falls; the compass is what would orient there — one tower, two sides.

- **Ambient:** `FiniteAttention`, `RealFor` (WS2), `ws3_compass_exogenous` (C2).
- **Success condition (Shape-drawn):** the duality is a theorem — attention bounded-with-values, compass free-orientation — not asserted prose.
- **Failure mode:** *the duality merely asserted.* Foreclosed: C4 is a conjunction of a computable-bound fact and the exogeneity existential. **Winner (the duality).**

### C5 — A canonical compass (the central sin, stated to be rejected)

```lean
def theCompass : Compass dest reify Or := ⟨fun _ => default, fun _ _ o => o⟩   -- a distinguished inhabitant
theorem ws3_convergence_holds : Converges dest reify theCompass x W := …        -- proving WITH it
```
Select a canonical compass and prove with it as though it were THE compass.

- **Failure mode:** *the central sin, SERIOUS (discipline 2).* This defines the undefinable: a distinguished inhabitant proving a compass-theorem is exactly what the charter forbids (§4.a). **Reject.** Every WS3 (and WS4/WS5) compass-theorem quantifies over all inhabitants; the only concrete compasses (C2's exogeneity, WS4's model pair) live inside `∃` and witness existentials — WS7 greps and unfolds to confirm no GENERAL theorem selects one.

### C6 — The compass as a value in the plain structure (the endogeneity trap)

```lean
def orientOf (dest) (x : X) : Or := …   -- derive the orientation FROM the relating
```
Derive the orientation from `dest` (make it endogenous / recoverable).

- **Failure mode:** *the compass recoverable, contradicting Series 07 (discipline 2).* If `orient` were a function OF `dest`, it would be recoverable from the relating — but Series 07 forces the differentiator exogenous (`¬ Recoverable`). An endogenous compass is either constant (evaluating nothing) or recovers a differentiator Series 07 forbids. **Reject:** `orient : X → Or` is an ARBITRARY field of the structure, `Or` exogenous, and C2 proves it `¬ Recoverable`. The orientation is drawn from outside, never computed from the relating.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the `Compass` type (orient + raise) | tower; `Or` a bare `Type u` | yes — the fields WS4 consumes | **win (the type)** |
| C2 | the compass is exogenous (`¬ Recoverable`) | `ws1_atomless_bisim`, witness | yes — differ on a bisimilar pair | **win (exogeneity, ∃)** |
| C3 | the compass is layered up the tower | `prec`, `ws3_order_endogenous` | yes — `prec`-edge coupling, free | **win (layering)** |
| C4 | the attention–compass duality | `FiniteAttention`, C2 | yes — bound + exogeneity | **win (duality)** |
| C5 | a canonical compass, proving with it | — | yes — the central sin | **reject (SERIOUS)** |
| C6 | the orientation derived from `dest` | — | yes — recoverable, forbidden | **reject (endogeneity trap)** |

## Winning candidates: C1 (the type) + C2 (exogeneity) + C3 (layering) + C4 (duality)

### Definitions and obligations (cite `spec/README.md` §2.5, §2.9; consume the witness carrier for the existentials)

```lean
namespace Series12.WS3
-- reify, reifyStep, prec, prec_step, ws3_order_endogenous, ws3_reify_preserves_SHNE, ws1_atomless_bisim,
-- Recoverable, plainOf, FiniteAttention, RealFor — transcribed (README §6).
-- The dir:=rank carrier (X, aW, bW, destW, reifyW, destWL) — spec/ws4-witness-design.md (for the existentials only).

/-- **The compass type, defined once (README §2.9). The first Series-12 design duty.** -/
structure Compass {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Or : Type u) where
  orient : X → Or
  raise  : X → X → Or → Or

-- D1 the type (C1) ; D2 ws3_compass_exogenous (C2, ∃) ; D3 ws3_compass_layered (C3) ;
-- D4 ws3_attention_compass_dual (C4).
```

**Proof architecture.** D1 defines the type — the SHAPE of the compass (per-relatum orientation + tower raising), held parametric. D2 (`∃ c`) proves it exogenous: orientations may differ on plain-bisimilar relata, so `orient` is `¬ Recoverable` (the Series 07 necessity), the compass itself inhabiting WS1's opening — an EXISTENTIAL, never a selection. D3 proves it layered: the raising couples the part's orientation up a genuine `prec` edge, the coupling FREE (neither collapsing compasses to one nor leaving them independent). D4 proves the duality with WS2's attention: attention bounded-with-values (knowable), compass free-orientation (typeable-not-evaluable). **Dependencies:** WS1's opening (the `¬ Recoverable` shape the compass inhabits); the tower (`prec`, `reifyStep`, `ws3_order_endogenous`); the witness carrier (for the existential witnesses ONLY); WS2's `FiniteAttention` (for the duality). **The parametricity discipline is the deliverable's spine: `Or` and every `Compass` stay parameters; the only concrete compasses are inside `∃`.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (the type), D2 (exogeneity, as an existential), D3 (layering), D4 (duality). The compass typed, per-relatum, layered, exogenous, every theorem parametric, content outside — the slot held open.
- **SERIOUS (pre-registered, discipline 2, the central sin):** if any theorem selected a canonical compass and proved with it (C5), or derived the orientation from `dest` (C6), the undefinable would be defined, SERIOUS — reported, not shipped. Foreclosed by parametricity (D1) and the exogeneity proof (D2); the only concrete compasses live inside existentials, WS7 grep-confirmed.
- **Strip test.** Delete **"compass / feeling / orientation / layered"** from `ws3_compass_exogenous` and it is the bare fact **"there is an `Or`-valued function on the carrier assigning different values to a plain-bisimilar pair, so the function is not recoverable from the plain relating"** — a `¬ Recoverable`-of-an-exogenous-function fact, which is what the charter demands: the compass's SHAPE is a non-recoverable exogenous per-relatum assignment (Series 07's necessity), and "feeling / orientation" is the earned interpretive layer. The strip removes the WORD "compass" and leaves the theorem (an exogenous non-recoverable assignment); crucially, no proof term is NAMED "compass" as content (the type `Compass` is a shape, parametric — the names-not-terms check, discipline 5, confirms `Compass` is a TYPE quantified over, never a discharged content).

## Deliverable

`series-12/formal/Series12/ws3.lean`: the transcribed tower + import test + attention (README §6); the `Compass` type (README §2.9); `ws3_compass_exogenous` (D2), `ws3_compass_layered` (D3), `ws3_attention_compass_dual` (D4). **Defines the compass type consumed by WS4/WS5/WS7; the first Series-12 design duty.** Axiom check: `#print axioms ws3_compass_exogenous` reduces through `ws1_atomless_bisim` to the standard three. **The compass is a TYPE — per-relatum, layered, exogenous — every theorem parametric over all inhabitants, the only concrete compasses confined to existentials, content outside the math: the guard against evaluating the undefinable.**
