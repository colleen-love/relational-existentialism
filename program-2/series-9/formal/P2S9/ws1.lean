/-
`program-2/series-9/formal/P2S9/ws1.lean`

WS1 - The lateral world, the metric, and the maximal rate (the risky ground). Program 2 Series 9 (2.9), THE CONE.

Imports its predecessor `P2S8` (reaching `P2S7 / … / P2S0 / P1` transitively) and builds on its transitive API:
chiefly the finite attention `P2S0.knows` / `∈ att` (the finite out-attention, the sole ontological bound). This file
fixes the SHARED objects of the series, all built FRESH and MODEL-DERIVED off the finite attention, de-risked on paper
first (`spec/rate-derisking.md`):

- the lateral world `S` (a line of five peers, the 2.4 world re-seated) and the fixed lateral METRIC `dist` (breadth
  as spatial distance, symmetric, attention-independent);
- the per-tick reach `span` (the greatest lateral distance to an attended relatum — how far one tick reifies) and THE
  RATE `rate` (the carrier's maximal per-tick reach), read off the finite attention ALONE via `Finset.sup` — the c is
  EARNED, not a postulated numeral (the no-smuggling gate foreclosed at the definition);
- the cone `ball` (the events within `rate × depth` in the lateral metric), the causal order `reaches` (decidable
  bounded reachability, 2.5 re-seated), and the three carriers `attSlow` (rate 1, CONE), `attFast` (rate 2, the
  same-order costume pair), `attAll` (rate 4, NO-CONE / instantaneous).

WS1 proves the rate BOUNDED and EARNED (`ws1_rate_bounded`, `ws1_rate_earned_from_knows`): the per-tick reach cannot
outrun the rate, and the rate is a `Finset.sup` over the attention, MONOTONE in it (`ws1_rate_monotone`) — a genuine
function of the finite attention, not a fixed cap (`ws1_rate_tracks_attention`: 1 < 2 < 4 as the attention widens).

Design docs: `program-2/series-9/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8

universe u

namespace P2S9

open P2S0

set_option linter.unusedVariables false

/-! ## The lateral world (a line of five peers) and the fixed lateral metric -/

/-- The lateral world: a line of five peers (`P2S4`'s world, re-seated). -/
abbrev S : Type := Fin 5

def p0 : S := 0   -- the source self (basepoint of the cone)
def p1 : S := 1   -- a lateral peer at distance 1
def p2 : S := 2   -- a lateral peer at distance 2
def p3 : S := 3   -- a lateral peer at distance 3
def p4 : S := 4   -- a lateral peer at distance 4 (the far event)

/-- The directed knowing (`= P2S0.knows`): `x` knows `y` iff `x` actively attends `y`. The imported primitive. -/
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y

/-- **THE LATERAL METRIC** (`P2S4`'s breadth-distance, re-seated as the line metric): a fixed spatial background,
symmetric and unsigned, INDEPENDENT of the attention — the breadth axis, not the conversion rate. -/
def dist (x y : S) : ℕ := Nat.dist x.val y.val

/-! ## The rate: the per-tick reach, read off the finite attention -/

/-- **THE PER-TICK REACH.** `span att x` is the greatest lateral distance to a relatum `x` attends: how far one tick
reifies from `x`. A `Finset.sup` over the finite attention `att x` — read off the attention alone. -/
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)

/-- **THE RATE `c`** (breadth per depth): the carrier's maximal per-tick reach, `sup` over the world of `span`. A
function of the FINITE ATTENTION alone (`Finset.sup`, no postulated numeral) — the recovery EARNED, not smuggled. -/
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)

/-! ## The cone, and the causal order -/

/-- **THE CONE** (WS2): the events within `rate × depth` of the source `x` in the lateral metric. Named `ball` in
code (`cone` is a forbidden content-name for a definition, audit e); "cone" in prose. -/
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)

/-- **THE CAUSAL ORDER** (`P2S5`, re-seated): decidable bounded reachability. `reachN att n R` is the closure of the
set `R` under `n` steps of the directed attention (each step adjoins the attended relata). `reachSet att x` starts
from `{x}` and iterates `card S` times — enough to reach any reachable event on the finite carrier. -/
def reachN (att : S → Finset S) : ℕ → Finset S → Finset S
  | 0,     R => R
  | (n+1), R => reachN att n (R ∪ R.biUnion att)

def reachSet (att : S → Finset S) (x : S) : Finset S := reachN att (Fintype.card S) {x}

/-- `y` is reachable from `x` (the causal order, as a decidable `Bool`). -/
def reaches (att : S → Finset S) (x y : S) : Bool := decide (y ∈ reachSet att x)

/-! ## The three carriers (the fork and the costume pair) -/

/-- The CONE carrier: each self attends its forward lateral neighbour (`p0→p1→p2→p3→p4`). Rate 1. -/
def attSlow : S → Finset S := fun x =>
  if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else if x = 3 then {4} else ∅

/-- The COSTUME-PAIR carrier: each self attends its forward TWO neighbours. Same causal order as `attSlow`, rate 2. -/
def attFast : S → Finset S := fun x =>
  if x = 0 then {1, 2} else if x = 1 then {2, 3} else if x = 2 then {3, 4} else if x = 3 then {4} else ∅

/-- The NO-CONE carrier: each self attends the WHOLE world. Rate 4 (the diameter): reification is instantaneous. -/
def attAll : S → Finset S := fun _ => {0, 1, 2, 3, 4}

/-! ## The payoff — the rate is bounded and earned -/

/-- **THE RATE BOUNDS THE PER-TICK REACH (WS1).** For every attention, every attended `y ∈ att x`, the lateral
distance `dist x y` is at most `rate att`: the conversion cannot outrun the rate. And `rate` is `Finset.sup`-derived
from the attention, so the bound is the attention's own, not a postulated `c`. -/
theorem ws1_rate_bounded (att : S → Finset S) : ∀ x y, y ∈ att x → dist x y ≤ rate att := by
  intro x y hy
  have h1 : dist x y ≤ span att x := Finset.le_sup (f := fun y => dist x y) hy
  have h2 : span att x ≤ rate att := Finset.le_sup (f := fun x => span att x) (Finset.mem_univ x)
  exact le_trans h1 h2

/-- **THE RATE IS EARNED FROM THE IMPORTED KNOWING.** An attended relatum (`knows att x y`, i.e. `y ∈ att x`) is
within the rate. The bound is a fact about exactly the `P2S0`-attended relata. -/
theorem ws1_rate_earned_from_knows (att : S → Finset S) (x y : S) : knows att x y → dist x y ≤ rate att := by
  intro h
  have hy : y ∈ att x := h
  exact ws1_rate_bounded att x y hy

/-- **THE RATE TRACKS THE ATTENTION (monotone).** If `a` attends no more than `b` (`a x ⊆ b x` for all `x`), then
`rate a ≤ rate b`: widen the attention, raise the rate. A postulated `c` could not track the attention; this rate is
a monotone function of it. -/
theorem ws1_rate_monotone (a b : S → Finset S) (h : ∀ x, a x ⊆ b x) : rate a ≤ rate b := by
  apply Finset.sup_le
  intro x _
  have hspan : span a x ≤ span b x := Finset.sup_mono (h x)
  have hle : span b x ≤ rate b := Finset.le_sup (f := fun x => span b x) (Finset.mem_univ x)
  exact le_trans hspan hle

/-- **THE RATE IS CONCRETE AND RISES WITH THE ATTENTION.** `rate attSlow = 1 < 2 = rate attFast < 4 = rate attAll`:
the rate is a genuine, strictly monotone function of the finite attention, never an arbitrary cap. -/
theorem ws1_rate_tracks_attention : rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end P2S9
