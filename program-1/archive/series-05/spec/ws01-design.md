# WS1 — The tower and its colimit

**Design doc. Series 05, blocking workstream. Owns: the directed system of faced carriers `W_α`, the connecting maps `ι_{α,β}`, the colimit carrier `W_∞`, the coalgebra-structure gate on which the whole program is conditional, and the recovery of Ω inside `W_∞`.**

*Series 05 is standalone. It carries its own copy of every Series 04 carrier lemma it needs (charter §1: "it is ok to copy theorems from 4 into 5"). The Series 04 names reproduced here — `PkObj`, `PkMap`, `Coalg`, `IsTerminalCoalg`, `lambek`, `Bisim`, `bisim_eq`, `νPk`, `νPk_terminal`, `Reaches`, `ReachSet`, `face`, `LkObj`, `LkMap`, `νLk`, `lstr`, `Cofix.corec`, `Cofix.dest`, `qpfLk`, `carrier_card_ge` — are transcribed into `series-05/formal/ws1.lean` verbatim from `series-04/formal/{ws1,ws3}.lean` and re-namespaced `Series05.WS1`. Nothing is imported from `series-04/` or `archive/`.*

## The object at stake

Series 04 built a single faced carrier: `νLk κ Q = Cofix (X ↦ P_κ(Q × X))`, the terminal coalgebra of the labelled powerset functor (`series-04/formal/ws3.lean`). That carrier has one fixed cardinal `κ` and one fixed label set `Q`; the Explosion Dilemma (WS2) proves any *single* such carrier is either capped by fiat or collapsed. Series 05's carrier is not a coalgebra but a **directed system** of them,

> `α ↦ W_α`, with `W_α` a Series-04-style faced carrier at cardinal `κ_α`, connected by `ι_{α,β} : W_α → W_β` for `α ≤ β`,

and the world is the colimit `W_∞ = colim_α W_α`. The design question is which shape of directed system (a) makes `W_∞` **carry a coalgebra** (a structure map `W_∞ → F(W_∞)` for the appropriate `F`), (b) keeps **bisimulation-is-identity** on `W_∞` (charter point 1 / criterion iii — the analogue of Series 04's weak-pullback gate), and (c) recovers **Ω = {Ω}** as a genuine inhabitant, so the tower refines rather than abandons the Series 04 object.

The gate (a)+(b) is existential for the program (charter §9, "the colimit gate is existential"). Every candidate below is triaged first on a decidable-on-paper version of it.

**Ambient theory (shared by all candidates).** ZFC as encoded by Lean 4 + Mathlib `v4.15.0`; the non-well-founded carrier is the QPF `Cofix` construction (final coalgebra of a bounded-powerset polynomial functor), exactly as Series 04 — no separate AFA axiom is assumed; anti-foundedness is *modelled* by the terminal coalgebra, following Aczel via Rutten/Jacobs. The base functor at level `α` is `F_α = (X ↦ P_{κ_α}(Q × X))` (labelled powerset, Series 04 `LkObj`). The index is a linear order `(I, ≤)` fixed abstractly here and pinned by WS2; WS1 assumes only that `I` is directed (every pair has an upper bound), which every candidate index of WS2 satisfies. No monad `T` or distributive law `λ` is needed in WS1 (those enter at WS6); WS1 is pure carrier-and-colimit.

## Candidates

### C1 — Set-indexed chain, union carrier (`I = ℕ`, `W_∞ = ⋃_n W_n`)

```lean
-- levels at strictly increasing cardinals κ₀ < κ₁ < …, connecting maps the
-- coalgebra inclusions νL(κ_n) ↪ νL(κ_{n+1}); carrier = the set-theoretic union
def Wsup (κ : ℕ → Cardinal.{u}) (Q) : Type (u+1) := Σ n : ℕ, νLk (κ n) Q   -- quotiented by ι
```
The tower is a countable chain; `W_∞` is the colimit over `ℕ`.

- **Ambient `F`:** at the colimit, `F_∞ = X ↦ P_{sup_n κ_n}(Q × X)` — the successor bound is the supremum cardinal `sup_n κ_n`.
- **Success condition:** `W_∞` carries `F_∞`-coalgebra structure with `bisim_eq`; Ω recovered.
- **Failure mode:** *the supremum is a genuine cardinal.* `sup_n κ_n = κ_ω` is a cardinal that lives *inside the theory*, so `W_∞ ⊆ νLk κ_ω Q` and the Explosion Dilemma (WS2) fires on `κ_ω`. This is the **tower-with-a-top** of charter §4.1 — "no last level" faked by a last cardinal.

**Paper triage.** Fails the program-level requirement, not the coalgebra gate: the coalgebra structure *does* exist (the union of a chain of coalgebras over a supremum cardinal is a coalgebra), so (a)+(b) pass. But (c′), the charter's "no imposed size," fails: `W_∞` sits inside one carrier `νLk κ_ω Q`, so WS3/WS4's endogenous-boundlessness payoff is unstatable — a higher level never "overshoots any candidate cap," because `κ_ω` *is* a cap. **Reject as the carrier: it makes the coalgebra gate a non-event but reintroduces exactly the wall WS2 forbids.** Retain the fact "a chain colimit over a supremum carries a coalgebra" as the *technical core* the real candidate reuses cofinally.

### C2 — Ordinal-cofinal directed system, colimit carrier (`I` cofinal in the ordinals, no top)

```lean
-- one carrier per level, the index a proper class / large directed set with no
-- greatest element; W_∞ the directed colimit, NOT contained in any single νLk
structure Tower (Q : Type u) where
  Idx    : Type u
  le     : Idx → Idx → Prop
  card   : Idx → Cardinal.{u}                 -- κ_α, unbounded: ∀ c, ∃ α, c < card α
  carrier: Idx → Type u                        -- W_α := νLk (card α) Q
  ι      : ∀ {α β}, le α β → carrier α → carrier β
  ι_coalg: ∀ {α β} (h : le α β), CoalgMorphism (ι h)   -- connecting maps preserve dest
```
The index has no greatest element and its cardinals are unbounded, so `W_∞` has no supremum cardinal.

- **Ambient `F`:** *there is no single `F_∞`.* Each object of `W_∞` lives at some level `α` and there carries `< κ_α` successors; the colimit has no global successor bound. The coalgebra structure on `W_∞` is a *level-indexed family* of structure maps cohered by the `ι`, not one map into a fixed `P_κ`.
- **Success condition:** the directed colimit `W_∞ = colim ι` exists as a type, carries a coalgebra structure `dest_∞` such that `ι_α` are coalgebra morphisms, and bisimulation on `W_∞` is identity.
- **Failure mode:** **the colimit fails to carry the structure.** Terminal coalgebras do not glue into a terminal coalgebra for free (charter §5.5): if `F` is not finitary / accessible enough, `colim (Cofix F_α)` need not be `Cofix F_∞`, `dest_∞` may not exist, and "an object is its relating" breaks — an *Impossibility proved for the colimit carrier*, redirecting the amalgamation.

**Paper triage.** This is the honest carrier. The decidable-on-paper gate: *is `P_κ` (the bounded powerset functor) `κ`-accessible, and do the connecting maps `ι` preserve `dest` on the nose?* Both are checkable. `P_{κ_α}` is `κ_α`-accessible (a `< κ_α`-bounded powerset is a `κ_α`-small-colimit-preserving-enough functor — this is exactly why `Cofix` exists at each level, Series 04 `exists_terminal_coalg`); and the connecting map at hand, `ι_{α,β} =` "reindex a `< κ_α`-bounded successor set as a `< κ_β`-bounded one" (`κ_α ≤ κ_β`), is a *pure inclusion of bounded-powerset objects*, which commutes with `dest` definitionally because it does not touch edges, only relaxes the bound. So (a) passes *for the inclusion connecting maps specifically*. (b) passes because bisimulation-is-identity is a *level-local* property (`bisim_eq` at each `W_α`) that transports across the colimit precisely when the `ι` are injective coalgebra morphisms — and bound-relaxing inclusions are injective. **This is the shape that makes the gate discharge to a level-local fact plus injectivity of inclusions.** Winner, subject to picking the connecting map as bound-relaxation (below).

### C3 — Single carrier with an internal grading (`W_∞ = νLk κ (ℤ × Q)`, levels as a label coordinate)

```lean
-- fake the tower inside one Series 04 carrier: absorb the level into the label
def Wgraded (κ) (Q) : Type u := νLk κ (ULift ℤ × Q)   -- "level" is just a ℤ-valued face coordinate
```
No colimit at all: one Series 04 carrier whose labels carry a `ℤ`-grade, "levels" read off the grade coordinate.

- **Ambient `F`:** `F = X ↦ P_κ((ℤ × Q) × X)`, a single Series 04 labelled functor.
- **Success condition:** would be that grade-slices behave as levels with no first/last grade.
- **Failure mode:** **collapse via the Explosion Dilemma.** `Wgraded` is a *single carrier at one κ*; WS2's dilemma fires on it directly. "No first grade" is a fact about `ℤ`-*labels*, not about the carrier's size or groundedness, so the anti-laundering test (charter §5.4, WS4) fails immediately: strip "level" and it is one Series 04 carrier with a fancy label set. It cannot state "no imposed size."

**Paper triage.** Passes the coalgebra gate trivially (it *is* a Series 04 carrier, gate inherited). Fails (c′) and the anti-laundering discipline exactly as C1 does, but worse: here there is not even a supremum-cardinal fig-leaf; the boundlessness is painted onto the label alphabet. **Reject.** Its one salvage — that a `ℤ`-grade on the *label* is cheap — is retained as the definition of the **depth-grade on faces** in WS6, where grading labels is the right move *because* WS6 is about cross-level edges, not about the carrier's boundlessness.

### C4 — Two-sided limit-colimit tower (bidirectional, for the self-dual pole, `I = ℤ`)

```lean
-- W_∞ built to carry BOTH a colimit (ascending, no top) and a limit (descending,
-- no bottom); the connecting maps run both ways so the ℤ-index is self-dual
structure BiTower (Q : Type u) extends Tower Q where
  ι_op   : ∀ {α β}, le α β → carrier β → carrier α      -- a descending cofiltered leg
  section_ι : ∀ {α β} (h : le α β), Function.LeftInverse (ι_op h) (ι h)
```
The `ℤ`-index is order-isomorphic to its reverse; `W_∞` is simultaneously the ascending colimit and the descending limit, so that "no first" and "no last" are one fact (charter point 8, self-duality).

- **Ambient `F`:** as C2 for the colimit leg; additionally a *limit* leg `lim_α W_α` for descent.
- **Success condition:** colimit and limit coincide (a *biproduct*/zero-object-like coincidence at the layer level), making the poles one.
- **Failure mode:** **no coincidence — the poles split** (charter point 8 honest alternative). If the ascending colimit and descending limit are not canonically isomorphic (the functor does not commute with the reversal), the tower is lopsided, self-duality is *false*, and point 8 is reported as a genuine two-pole negative. Also risks **non-existence** of the descending limit if `F` is not continuous.

**Paper triage.** The colimit leg is exactly C2 (passes). The *limit* leg is the live question: does the descending cofiltered limit `lim_α νLk κ_α Q` exist and carry a coalgebra? Decidable-on-paper: a cofiltered limit of coalgebras exists when `F` preserves cofiltered limits; `P_κ` (bounded powerset) *does not* preserve arbitrary cofiltered limits (the bound interacts badly with infinite descending intersections). **Verdict: the limit leg is negative-leaning; do not build `W_∞` as a bidirectional biproduct.** Instead realize self-duality (point 8) *at the index level only* — prove `(I, ≤) ≅ (I, ≥)` as orders (decidable for `I = ℤ`) and read descent/ascent as the same colimit construction applied to the reversed index, rather than as a literal categorical limit. **Retain C4's insight (index self-duality) for WS4; reject C4 as the carrier shape.**

## Winning candidate: C2 (ordinal-cofinal directed colimit) with bound-relaxing inclusions, index self-duality handled order-theoretically per C4

The decisive moves, both of which convert the existential gate to already-safe facts:

1. **The connecting maps are bound-relaxations, not arbitrary coalgebra morphisms.** `ι_{α,β}` reindexes a `< κ_α`-successor set as a `< κ_β`-successor set (`κ_α ≤ κ_β`). This is an *inclusion* that commutes with `dest` by construction and is injective — so both halves of the gate (structure exists; bisimulation is identity) reduce to level-local Series 04 facts plus "inclusions are injective."
2. **The colimit is directed, not a supremum.** Because the index has no greatest element and the cardinals are unbounded (WS2's job), `W_∞` is not contained in any `νLk κ_α Q`, so no Explosion Dilemma fires on it — unlike C1/C3.

### Definitions

```lean
namespace Series05.WS1
-- carrier machinery (PkObj, PkMap, Coalg, νLk, lstr, Cofix, Reaches, ReachSet,
-- face, carrier_card_ge, bisim_eq) transcribed verbatim from Series 04; see header.

variable {Q : Type u}

/-- A **level**: a Series-04 faced carrier at a cardinal `κ_α ≥ ℵ₀`. -/
structure Level (Q : Type u) where
  card  : Cardinal.{u}
  hinf  : ℵ₀ ≤ card

/-- The carrier of a level is the labelled terminal coalgebra `νLk κ_α Q`. -/
noncomputable def Level.carrier (L : Level Q) : Type u := νLk L.card Q

/-- The **directed tower**: an index with no greatest element, unbounded cardinals,
    and bound-relaxing connecting maps. (No-least-element is WS2's obligation; WS1
    needs only directedness.) -/
structure Tower (Q : Type u) where
  Idx      : Type u
  le       : Idx → Idx → Prop
  [ord     : IsLinearOrder Idx le]
  directed : ∀ a b, ∃ c, le a c ∧ le b c
  lvl      : Idx → Level Q
  mono     : ∀ {a b}, le a b → (lvl a).card ≤ (lvl b).card
  ι        : ∀ {a b}, le a b → (lvl a).carrier → (lvl b).carrier
  ι_dest   : ∀ {a b} (h : le a b) (x : (lvl a).carrier),
               lstr (ι h x) = LkMap (ι h) (lstr x)         -- coalgebra-morphism law
  ι_refl   : ∀ {a} (x : (lvl a).carrier), ι (le_refl' a) x = x
  ι_trans  : ∀ {a b c} (hab : le a b) (hbc : le b c) (x),
               ι hbc (ι hab x) = ι (le_trans' hab hbc) x
  ι_inj    : ∀ {a b} (h : le a b), Function.Injective (ι h)

/-- The colimit carrier `W_∞`: the quotient of the disjoint union `Σ α, W_α` by the
    directed-system relation `x ~ y` iff they agree at some common upper level. -/
def TowerColimRel (T : Tower Q) : (Σ a, (T.lvl a).carrier) → (Σ a, (T.lvl a).carrier) → Prop :=
  fun p q => ∃ c (hpc : T.le p.1 c) (hqc : T.le q.1 c), T.ι hpc p.2 = T.ι hqc q.2

def Winf (T : Tower Q) : Type u := Quot (TowerColimRel T)

/-- Injection of a level into the colimit. -/
def toColim (T : Tower Q) {a} (x : (T.lvl a).carrier) : Winf T := Quot.mk _ ⟨a, x⟩
```

### The three obligations, each decidable-on-paper

**D1 — `TowerColimRel` is an equivalence and `toColim` are compatible (colimit exists).**
```lean
theorem ws1_colim_equiv (T : Tower Q) : Equivalence (TowerColimRel T)
```
*Strategy:* reflexivity from `ι_refl`; symmetry immediate; transitivity from `directed` (find a common upper bound of the two witnessing levels) plus `ι_trans` and `ι_inj` (to reconcile the two mediating maps). Directedness is exactly what a colimit of a directed system needs. *Paper-decidable:* yes — it is the standard directed-colimit construction; every step is a finite diagram chase using the four `ι` laws.

**D2 — the gate: `W_∞` carries `dest_∞` and bisimulation is identity.**
```lean
/-- The colimit structure map: an object at level α unfolds via its level's `lstr`,
    its successors reindexed into the colimit. Well-defined because `ι` are
    coalgebra morphisms (`ι_dest`). -/
noncomputable def destInf (T : Tower Q) : Winf T → Σ' a, LkObj (T.lvl a).card Q (Winf T)

theorem ws1_bisim_eq_colim (T : Tower Q)
    (R : Winf T → Winf T → Prop) (hR : ColimBisim T R) :
    ∀ x y, R x y → x = y
```
*Strategy:* `destInf` is well-defined on the quotient because `ι_dest` says the connecting maps commute with `dest`, so the level-α unfolding of a representative agrees (after reindexing) with the level-β unfolding of any equivalent representative — this is the one place `ι_dest` is load-bearing. For `ws1_bisim_eq_colim`: a bisimulation `R` on `W_∞` pulls back along `toColim_a` to a bisimulation on each `W_α = νLk κ_α Q`; by the level-local `bisim_eq` (transcribed Series 04 fact) each pullback is contained in the diagonal; because `ι_inj` the diagonals cohere, so `R` is the colimit diagonal. **The gate is thus: level-local `bisim_eq` + injectivity of connecting maps.** *Paper-decidable:* yes — reduces to a proved Series 04 theorem applied levelwise plus injectivity, no new coinduction.
- *Failure recorded if it were to fail:* `destInf` ill-defined (some `ι` not a coalgebra morphism) ⇒ Impossibility proved for the colimit carrier, redirect to a different amalgamation (charter §9). The bound-relaxation choice is exactly what forecloses this.

**D3 — Ω recovered inside `W_∞`, with an honest local bound.**
```lean
/-- The self-loop Ω lives at every level (its single self-edge needs only `2 < κ_α`),
    and all its level-copies are identified in the colimit. -/
noncomputable def omegaInf (T : Tower Q) (q : Q) : Winf T :=
  toColim T (Series05.WS1.loopState (a := T.someIdx) q (T.lvl _).hinf)

theorem ws1_omega_selfloop (T : Tower Q) (q : Q) :
    -- Ω's colimit unfolding is the self-singleton {Ω}
    destInf T (omegaInf T q) = ⟨_, ⟨{(q, omegaInf T q)}, _⟩⟩

theorem ws1_local_bound (T : Tower Q) (x : Winf T) :
    ∃ a (y : (T.lvl a).carrier), x = toColim T y ∧
      Cardinal.mk ↥(lstr y).1 < (T.lvl a).card         -- honest < κ_α relating at its level
```
*Strategy:* Ω is the `loopState` of Series 04 (transcribed), which exists at any level with `ℵ₀ ≤ κ_α`; its copies at different levels are `TowerColimRel`-related because the bound-relaxing `ι` sends a self-loop to a self-loop. `ws1_local_bound` is immediate: every colimit point has a representative at some level, where its successor set is `< κ_α` by the `νLk` bound (`s.2` in `PkObj`). *Paper-decidable:* yes.

### Why C2 and not C1

C1 (union over `ℕ`) makes the coalgebra gate a non-event, exactly as C2's bound-relaxation does — but C1's colimit is *contained in* `νLk κ_ω Q`, so it has a supremum cardinal and the Explosion Dilemma fires on it (WS2). C1 is the tower-with-a-top (charter §4.1): "no last level" faked by a last cardinal. C2 pays for genuine unboundedness by taking the index cofinal in the cardinals with no greatest element — the coalgebra structure is then *level-indexed*, not a single map into one `P_κ`, which is precisely what lets WS3/WS4 state "no imposed size." The design principle (inherited from Series 04 WS1's R2-over-R3 choice): **take the amalgamation that keeps the gate level-local and injective, and pay for boundlessness in the index rather than in a bespoke colimit functor.**

### The one place C2 might be too weak (routed to fallback)

C2's `destInf` lands in a *level-dependent* codomain `Σ' a, LkObj κ_α Q (Winf T)` — the successor bound depends on which level the representative was drawn from. If WS6's cross-level composition needs a *single* structure map `W_∞ → F_∞(W_∞)` for one functor `F_∞` (e.g. to state a graded distributive law uniformly), the level-dependent `destInf` may not suffice, and a genuine colimit functor `F_∞ = X ↦ (Σ α, P_{κ_α}(Q × X))` with its own QPF structure is required. Decidable-on-paper trigger, checked at WS6 kickoff: *does the graded distributive law quantify over one functor `F_∞`, or is it stated level-wise and glued?* If the former, escalate to the colimit-functor fallback and pay a QPF-accessibility proof; if the latter, C2's level-indexed `destInf` suffices. **Pre-registered:** WS1 reports C2 as the carrier and records the colimit-functor `F_∞` as a typed fallback with an open `AccessibleColimitFunctor` obligation, exactly as Series 04 WS1 registered its R3 fallback.

## Outcome classes (per charter §7)

- **Discharged:** D1–D3 proved on C2 with bound-relaxing inclusions (expected; the gate reduces to level-local `bisim_eq` + `ι_inj`).
- **Impossibility proved:** reachable only if `destInf` cannot be made well-defined for *any* admissible connecting map — a sharp negative redirecting the amalgamation. Not expected via bound-relaxation, whose coalgebra-morphism law holds definitionally.
- **Partial:** C2 carrier delivered, colimit-functor `F_∞` escalation flagged open for WS6's uniform distributive law.

## Deliverable

`series-05/formal/ws1.lean`: the transcribed Series 04 carrier machinery (self-contained); `Level`, `Tower`, `TowerColimRel`, `Winf`, `toColim`, `destInf`; `ws1_colim_equiv` (D1), `ws1_bisim_eq_colim` (D2), `ws1_omega_selfloop` + `ws1_local_bound` (D3); the colimit-functor `F_∞` fallback typed but unbuilt. Axiom check: `#print axioms ws1_bisim_eq_colim` should reduce to the transcribed `bisim_eq` record (`propext, Classical.choice, Quot.sound`).
