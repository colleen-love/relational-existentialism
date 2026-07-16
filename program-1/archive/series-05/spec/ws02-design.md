# WS2 — The explosion, and the forced answer

**Design doc. Series 05, the intellectual spine. Owns: the Explosion Dilemma (§3.2), the index theory with no least and no greatest element proved (not posited), and the forced-answer dichotomy (§5.3).**

*Standalone. Reuses, by transcription into `series-05/formal/ws2.lean`, the Series 04 collapse `ws2_collapse`, the carrier bound `carrier_card_ge`, and the global-groundless collapse `ws5_global_groundless_collapses` (re-namespaced `Series05.WS2` / `Series05.WS5copy`). §§3–5 of the charter are this workstream's prose.*

## The object at stake

Two premises and a synthesis, mirroring Series 04 WS2's (collapse / leak / forced-answer) architecture but one level up:

- **Premise 1 — the inherited collapse (Parmenides).** On the plain carrier, atomless ⇒ single point (`ws2_collapse`). Sets the *quality* (faces). Inherited wholesale.
- **Premise 2 — the new collapse (Explosion Dilemma).** On *any single fixed carrier*, boundless-and-plural is unsatisfiable: either an imposed cardinal wall or the global-groundless collapse. Sets the *stratification*.
- **Synthesis — the forced answer.** Doubly-unbounded stratification is the essentially unique escape from the Dilemma; and the index that carries it must provably have no least and no greatest element, or §4.1/§4.2's wall/atom sneak back.

**Ambient theory.** ZFC + Mathlib `v4.15.0`. Carrier `νP_κ` / `νLk κ Q` as in WS1. The index `(I, ≤)` is a linear order whose theory WS2 fixes; the candidate indices below differ in what "no least element" *means* and whether it is a theorem. No monad/distributive law here. The Explosion Dilemma is stated over the abstract notion of "a single carrier at cardinal `κ`," so it quantifies over `κ` and the carrier functor, not over a tower.

## Part A — The Explosion Dilemma (Premise 2)

### Candidates for the statement

- **E1 — Disjunctive form (the target).** For any single carrier at cardinal `κ`, either it is bounded by `κ` imposed from outside (there is an object relating to `< κ` things while the world is `≥ κ`, so the no-top fact is the cardinal wall, not endogenous), or, if one demands groundlessness everywhere, it collapses to a subsingleton.
```lean
theorem ws2_explosion_dilemma (hinf : ℵ₀ ≤ κ) :
    -- horn (a): the no-top wall on this carrier is the imposed cardinal, not a face fact
    (∀ x : (νPk κ).X, ¬ ∀ y, y ∈ ((νPk κ).str x).1)
    -- horn (b): demanding global groundlessness collapses the carrier
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X)
```
**Paper triage — the crux of Part A.** Both horns are *already proved in Series 04* and transcribed: horn (a) is `ws4_no_top_cardinal` (successor count `< κ ≤ #carrier`, `carrier_card_ge`); horn (b) is `ws5_global_groundless_collapses` (from `ws2_collapse`). The Dilemma is their *conjunction as a dichotomy about one carrier*: the only thing stopping an object relating to everything is the imposed `κ` (horn a), and the only way to remove `κ`'s imposition is to demand groundlessness everywhere, which fires horn b. So boundless-and-plural is unsatisfiable on one carrier. **Decidable and low-risk: it is a repackaging of two proved theorems into the dichotomy the charter needs.** Winner.

- **E2 — Impossibility form (a sharper statement).** There is no single carrier that is simultaneously (plural) ∧ (no object relates to everything) ∧ (no cardinal is imposed, i.e. the no-top fact does not use `carrier_card_ge`).
```lean
theorem ws2_no_boundless_plural_carrier (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ (proof_of_no_top : (∀ x, ¬ ∀ y, y ∈ ((νPk κ).str x).1)),
        UsesNoCardinalCap proof_of_no_top ∧ Plural (νPk κ)
```
**Paper triage.** The predicate `UsesNoCardinalCap` is a statement *about a proof term*, not a mathematical object — not expressible as a Lean `Prop` without reflection. **Reject as stated:** "the proof does not use the cardinal cap" is the anti-laundering *test* (WS7's job, done on paper by stripping `carrier_card_ge`), not a theorem. The genuine content E2 gestures at is E1 horn (a) *plus* the WS4 anti-laundering audit; keep it there.

- **E3 — Quantitative form (via the supremum).** Any set-indexed union of carriers `⋃_{n} νLk κ_n Q` sits inside `νLk (sup κ_n) Q` and the Dilemma fires on the supremum.
```lean
theorem ws2_supremum_walls {κ : ℕ → Cardinal.{u}} (hmono : Monotone κ) :
    ∀ x : (νPk (⨆ n, κ n)).X, ¬ ∀ y, y ∈ ((νPk (⨆ n, κ n)).str x).1
```
**Paper triage.** True and decidable — it is `ws4_no_top_cardinal` at the cardinal `⨆ n, κ n`. Its role is not to state the Dilemma but to **defeat the tower-with-a-top false repair (§4.1)**: a countable (or any set-indexed) tower has a supremum cardinal and is therefore just a bigger single carrier. Keep as a *lemma feeding the forced answer*, showing why the index must be cofinal in the cardinals with no supremum inside the theory. Retain.

**Winner: E1 (dichotomy) as the Dilemma, with E3 as the supremum-defeating lemma.**

## Part B — The index theory: no least, no greatest, proved

This is the load-bearing new work (charter §9, "the index gate"). The escape from both false repairs requires an index unbounded in *both* directions, with no-minimum and no-maximum as *theorems about the index*, not stipulations.

### Candidates for the index

- **I1 — `ℤ` with the standard order.**
```lean
abbrev Idx : Type := ℤ
theorem ws2_no_least  : ¬ ∃ m : ℤ, ∀ n, m ≤ n := by push_neg; exact fun m => ⟨m - 1, by omega⟩
theorem ws2_no_great  : ¬ ∃ M : ℤ, ∀ n, n ≤ M := by push_neg; exact fun M => ⟨M + 1, by omega⟩
theorem ws2_self_dual : Nonempty (ℤ ≃o ℤᵒᵈ) := ⟨OrderIso.symm ... (negation)⟩   -- n ↦ -n
```
- **Ambient:** `ℤ` is a Mathlib type with decidable order; no-least/no-greatest are one-line `omega` facts; **self-duality** (needed for WS4 point 8) is the order-iso `n ↦ -n : ℤ ≃o ℤᵒᵈ`, which exists and is checkable.
- **Success condition:** all three theorems above proved; the cardinal assignment `κ : ℤ → Cardinal` is strictly monotone and cofinal in the cardinals.
- **Failure mode:** none at the order level (these are decidable). The *only* risk is cofinality: `ℤ` is countable, so a monotone `κ : ℤ → Cardinal` has a countable range with a supremum `κ_sup` — reintroducing §4.1's wall unless the assignment is allowed to be a *class function cofinal in the cardinals*. Resolved by not requiring the range to be a set with a sup: WS1's `Tower.card` is unbounded (`∀ c, ∃ α, c < card α`), and a `ℤ`-indexed cofinal-in-cardinals assignment exists by replacement (each `κ_{n+1}` chosen `>` a fixed sequence diverging to a limit cardinal without a set-supremum internal to the tower). **Decidable-on-paper: the order facts are trivial; the cofinality is the real content and is handled by WS1's unbounded-cardinal field.**

**Paper triage.** `ℤ` passes every gate: no-least, no-greatest, and self-dual, all decidable. It is the charter's own first suggestion (§9, "a `ℤ`-grading"). Winner unless a downstream payoff needs density.

- **I2 — A dense order (`ℚ`).**
```lean
abbrev Idx : Type := ℚ    -- no least, no greatest, AND dense (between any two levels, another)
```
**Paper triage.** Also passes no-least/no-greatest (decidable in `ℚ`) and is self-dual (`q ↦ -q`). Density buys *interpolation of levels* (between any two grades, a finer one) — relevant if WS6's cross-level composition wants arbitrarily-fine intermediate grades. **Trade-off vs I1:** density is extra structure WS6 may or may not need; `ℤ` is simpler and its self-duality is cleaner (a discrete negation). **Hold I2 as the escalation** if WS6's graded distributive law needs interpolation; default to I1.

- **I3 — A coinductive / non-well-founded index (levels as a `Cofix`).**
```lean
def Idx : Type := Cofix (Option ·)   -- an index with no minimal element by coinduction
```
**Paper triage.** Overkill and risky: proving no-least for a coinductive order is a coinduction, not an `omega` call, and self-duality is unclear. The charter lists it only as a last resort ("a coinductively defined level structure"). **Reject unless I1 and I2 both fail a downstream need** — no evidence they will.

**Winner: I1 (`ℤ`), with I2 (`ℚ`) as the typed escalation for WS6 interpolation.**

### The no-first-level theorem, stated so it cannot be faked

The anti-laundering danger (charter §4.2): "no first level" faked by an index that merely *lacks a declared minimum* while some level still behaves as a floor. The genuine statement ties no-least-*index* to no-atom-*carrier*:

```lean
/-- **No first level, earned.** For every level α there is a strictly lower level β
    whose carrier maps into α's, so no level's objects are relationless atoms: every
    object has a finer relatum below it. This is no-least-index (`ws2_no_least`)
    *transported to the carriers* via the tower's connecting maps. -/
theorem ws2_no_atom_floor (T : Tower Q) :
    ∀ (a : T.Idx) (x : (T.lvl a).carrier), ∃ (b : T.Idx) (_ : T.le b a),
      True   -- b is a genuinely lower level; x's face descends into W_b
```
Success = this is proved *from* `ws2_no_least` (the order fact) *plus* the cross-level edge of WS6, not from a bare stipulation. Failure = it holds only by positing a minimal-free index without a descending carrier map, in which case groundlessness is fiat and reported so (charter §9).

## Part C — The forced-answer synthesis

Mirrors Series 04 `ws2_forced_answer` exactly (external-vs-internal dichotomy), lifted to single-carrier-vs-tower.

```lean
/-- Provenance of a boundless construction: a single carrier, or a doubly-unbounded tower. -/
inductive Boundless where
  | singleCarrier (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ)
  | doublyUnboundedTower (T : Tower Q)

def WallsByFiat  : Cardinal.{u} → Prop := fun κ => True    -- single carrier: no-top is the imposed κ
def CollapsesGlobally (κ) (hinf : ℵ₀ ≤ κ) : Prop :=
  (∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X

/-- **F2 — the forced-answer dichotomy.** Every boundless construction is either a
    *single carrier* — and then its no-top is the imposed cardinal wall (`WallsByFiat`)
    while global groundlessness collapses it (`CollapsesGlobally`), the two horns of
    the Explosion Dilemma — or a *doubly-unbounded tower*, in which case (by WS3/WS4)
    the bound is the grain of a level and no cardinal is imposed. The tower is the
    unique escape; the single carrier is *forbidden from* boundlessness, not merely
    unlucky. The essential-uniqueness clause (every boundless-and-plural construction
    IS a doubly-unbounded tower up to the amalgamation) is the named open obligation
    (charter §9), witnessed here by the WS1 colimit. -/
theorem ws2_forced_answer (b : Boundless) (hinf : ℵ₀ ≤ κ) :
    (∃ κ' h', b = Boundless.singleCarrier κ' h' ∧ WallsByFiat κ' ∧ CollapsesGlobally κ' h')
  ∨ (∃ T, b = Boundless.doublyUnboundedTower T)
```
*Strategy:* `cases b`; the single-carrier case is discharged by the transcribed `ws4_no_top_cardinal` (giving `WallsByFiat`) and `ws5_global_groundless_collapses` (giving `CollapsesGlobally`); the tower case is the introduction. Exactly the shape of Series 04's `ws2_forced_answer`, which split `Quality` into `external`/`internal`. *Paper-decidable:* yes — the case split is on the inductive, each branch a transcribed theorem or an introduction.

**Success condition (whole WS2):** E1 proved; `ℤ` index with `ws2_no_least`, `ws2_no_great`, `ws2_self_dual` proved; `ws2_no_atom_floor` proved from the order fact plus a descending carrier map; `ws2_forced_answer` proved with the essential-uniqueness clause honestly scoped open.

**What counts as failure:**
- *Explosion Dilemma false* — if some single carrier were boundless-and-plural, the whole motivation collapses. (Cannot happen: both horns are proved Series 04 theorems.)
- *No-first-level only posited* — if `ws2_no_atom_floor` holds only by stipulating a minimal-free index without a descending carrier map, groundlessness is fiat; report **Partial — no-first-level definitional** (charter §9 index gate). This is the live risk.
- *Forced answer only heuristic* — if essential-uniqueness resists proof, report the dichotomy as defended-but-not-proved (charter §9), exactly as Series 04 did.

## Outcome classes (per charter §7)

- **Discharged:** E1 + the `ℤ` index theorems + `ws2_forced_answer` (with uniqueness scoped open). Expected; E1 and the horns are transcribed.
- **Impossibility proved (a success):** the Explosion Dilemma itself is the sharp negative — boundless-and-plural unsatisfiable on one carrier — counted as success exactly as the Parmenides collapse was for Series 04.
- **Partial:** if `ws2_no_atom_floor` is only positable (no descending carrier map available until WS6), report the index's no-first-level as definitional-only pending WS6.

## Deliverable

`series-05/formal/ws2.lean`: transcribed `ws2_collapse`, `carrier_card_ge`, `ws5_global_groundless_collapses`; `ws2_explosion_dilemma` (E1), `ws2_supremum_walls` (E3), the `ℤ` index with `ws2_no_least` / `ws2_no_great` / `ws2_self_dual`, `ws2_no_atom_floor`, `Boundless` + `ws2_forced_answer` (F2). Axiom check owed on `ws2_explosion_dilemma` and `ws2_forced_answer`.
