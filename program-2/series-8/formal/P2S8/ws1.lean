/-
`program-2/series-8/formal/P2S8/ws1.lean`

WS1 - The population and the good (the ground). Program 2 Series 8 (2.8), the value CAPSTONE.

Imports its predecessor `P2S7` (reaching `P2S6 / … / P2S0 / P1` transitively) and builds on its transitive API:
chiefly the directed attention `P2S0.knows` / `∈ att` (the knowing-asymmetry) and, laterally, the world of
Series 2.4. This file fixes the SHARED objects of the series, all built FRESH and MODEL-DERIVED off the directed
attention, de-risked on paper first (`spec/frustration-derisking.md`):

- the population `S` (a lateral world of three peers) and its two directed attentions `attTri` (a directed 3-ring)
  and `attStar` (a mutual star);
- the ONE model quantity `incr` — the signed directed-attention increment `⟦y∈att x⟧ - ⟦x∈att y⟧`, a function of
  the attention alone (the T1-S1 trap foreclosed at the definition: no free parameter, no disconnected counter);
- the good `valu` (a self-relative valuation, read from the self `p0`'s directed attention), the reconciliation
  `recon` (translation by `incr`), the holonomy `hol` (the δ-sum around a cycle), and a global section `IsSection`.

WS1 proves the good NON-TRIVIAL and genuinely SELF-RELATIVE (`ws1_nontrivial`): non-constant, and perspectival
(two selves value a common relatum oppositely — no symmetric metric can, so not a relabelling of 2.4's metric).

Design docs: `program-2/series-8/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7

universe u

namespace P2S8

open P2S0

set_option linter.unusedVariables false

/-! ## The population (a lateral world of three peers) and its two directed attentions -/

/-- The population of three selves (peers), a lateral world re-seated (`P2S4`, transitive). -/
abbrev S : Type := Fin 3

def p0 : S := 0   -- the self (basepoint of the self-relative good)
def p1 : S := 1   -- a lateral peer
def p2 : S := 2   -- a lateral peer

/-- The FRUSTRATED carrier: the directed 3-ring `p0 → p1 → p2 → p0` (each self attends its lateral successor). -/
def attTri : S → Finset S := fun x => if x = p0 then {p1} else if x = p1 then {p2} else {p0}

/-- The GLUABLE carrier: the mutual star `p0 ↔ p1`, `p0 ↔ p2` (the self attends both peers; each peer the self). -/
def attStar : S → Finset S := fun x => if x = p0 then {p1, p2} else {p0}

/-- The directed knowing (`= P2S0.knows`): `x` knows `y` iff `x` actively attends `y`. The imported primitive. -/
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y

instance decKnows (att : S → Finset S) (x y : S) : Decidable (knows att x y) :=
  inferInstanceAs (Decidable (y ∈ att x))

/-! ## The one model quantity, and the objects read off it -/

/-- **THE SIGNED DIRECTED-ATTENTION INCREMENT.** `incr att x y = ⟦y∈att x⟧ - ⟦x∈att y⟧`: `+1` on a one-way
outward edge, `-1` on a one-way inward edge, `0` on a mutual or absent edge. A function of the attention ALONE. -/
def incr (att : S → Finset S) (x y : S) : ℤ :=
  (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)

/-- **THE RECONCILIATION** (WS2): the model-derived translation of the value torsor by the directed increment. -/
def recon (att : S → Finset S) (x y : S) : ℤ → ℤ := fun v => v + incr att x y

/-- **THE GOOD** (WS1): the self-relative valuation, read from the self `p0`'s directed attention. Named `valu`
in code (`good` is a forbidden content-name for identifiers, audit e); "good" in prose. -/
def valu (att : S → Finset S) : S → ℤ := fun y => incr att p0 y

/-- **THE HOLONOMY** (WS3/WS4): the net translation of the composed reconciliation around the triangle `x→y→z→x`. -/
def hol (att : S → Finset S) (x y z : S) : ℤ := incr att x y + incr att y z + incr att z x

/-- **A GLOBAL SECTION** (a global good, WS4): an assignment consistent with every attention edge. -/
def IsSection (att : S → Finset S) (s : S → ℤ) : Prop :=
  ∀ x y, y ∈ att x → s y = s x + incr att x y

/-! ## The payoff -/

/-- **THE GOOD IS NON-TRIVIAL AND GENUINELY SELF-RELATIVE (WS1).** (i) `valu attTri` is non-constant — two selves
valued differently (`+1 ≠ -1`), so the good is not a view from nowhere. (ii) The good is PERSPECTIVAL — the same
relatum `p2` is valued with opposite sign from two frames (`incr p0 p2 = -1 ≠ +1 = incr p1 p2`), which no symmetric
observer-independent valuation (in particular no metric) can do. The good is not a relabelling of 2.4's metric. -/
theorem ws1_nontrivial :
    valu attTri p1 ≠ valu attTri p2
  ∧ incr attTri p0 p2 ≠ incr attTri p1 p2 := by
  refine ⟨?_, ?_⟩ <;> decide

end P2S8
