/-
`series-12/formal/Series12/ws4.lean`

WS4 - Convergence: defined, then proved underdetermined over a constrained class (the wall). Series 12,
the uncertain obligation.

Consumes WS3 (the compass type, `ConstituentOf`) and WS2 (the carrier). Defines the convergence relation
`Converges` (a real equation over a constituency edge, the second design duty) and its layered closure
`ConvergesUp` (restricted to `ConstituentOf` edges, Finding 2).

The independence is stated over a COMPASS CLASS that carries a genuine structural constraint, `Faithful`
(the raising is the identity: a part's orientation is carried UNCHANGED up to the whole, so convergence
tests genuine orientation-coherence and not a free re-labelling). At the genuine part-and-whole edge
`(aW, bW)` the fork is a TWO-ZONE fork whose boundary is Series 07's import boundary
(program-review-2 PR2-S1): over the full faithful class convergence is UNDERDETERMINED (two faithful
compasses sharing the identical raising, differing only in the orientation the structure does not fix, one
cohering and one not, both non-degenerate, `ws4_underdetermined`); over the IN-SIGHT faithful sub-class
(`BisimInvariant`) it is DECIDED, forced to hold (`ws4_decided_within_sight`), and every faithful DISSENT at
the edge is a genuine import (`ws4_dissent_is_import`, `¬ Recoverable` of `orientLift`, Series 07's work as a
proof term). `ws4_two_zone` packages this; `ws5_verdict_reaches_both` reaches BOTH verdict values at the
SAME edge, so SHAPE-DRAWN is EARNED and FALSIFIABLE where the verdict is computed. On this every-moment
atomless carrier the in-sight class is inhabited (`ws4_insight_inhabited`) and its members are
orientation-UNIFORM (`ws4_sight_is_uniform`: what the structure can see is the One at the orientation level),
so the decided zone is decided BECAUSE sight collapses to the uniform orientation. `ws4_wall_is_structural`
proves the real independence (shared faithful raising, opposite verdicts on the free orientation) with the
bridge IN the proof term; `ws4_fork_open` (a reflexive locus) is kept only as a remark, no longer
load-bearing (PR2-S1/PR3-R2).

Design doc: `series-12/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws3

universe u

namespace Series12.WS4

open Series12.WS1 Series12.WS2 Series12.WS3 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The convergence relation (the second design duty, README §2.10) -/

/-- **Convergence (one-layer coherence, the core relation).** Over a constituency edge, the part converges
with the whole iff the part's orientation, RAISED to the whole, coheres with the whole's own orientation. A
genuine equation in `Or`, depending on `c`; NOT `True`, NOT `False`, NOT `orient x = orient x`. -/
def Converges {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (x W : X) : Prop :=
  c.raise x W (c.orient x) = c.orient W

/-- **Convergence up the layers (restricted to constituency edges, Finding 2).** Coherence along a chain of
genuine `ConstituentOf` edges: `reify` is load-bearing in the definition. -/
def ConvergesUp {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) : X → X → Prop :=
  Relation.ReflTransGen (fun x W => ConstituentOf dest reify x W ∧ Converges dest reify c x W)

/-- **The faithful class (the structural constraint, PR1-S1).** A compass is `Faithful` iff its raising is
the identity on `Or`: the part's orientation is carried UNCHANGED up to the whole. This is the minimal
class condition that makes convergence a genuine test of orientation-coherence (`Converges c x W ↔
c.orient x = c.orient W`) rather than a free re-labelling, so the trichotomy over the class is genuinely
open (`ws4_fork_open` inhabits the forced arm on a reflexive locus). Non-empty and non-degenerate: `id` is
injective, so a faithful compass is never a collapsed constant on the raising. -/
def Faithful {X : Type u} {dest : X → PkObj κ X} {reify : PkObj κ X → X} {Or : Type u}
    (c : Compass dest reify Or) : Prop := ∀ x W : X, c.raise x W = id

/-- Under `Faithful`, convergence is exactly orientation-coherence: `Converges c x W ↔ orient x = orient W`. -/
theorem faithful_converges_iff {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (hf : Faithful c) (x W : X) :
    Converges dest reify c x W ↔ c.orient x = c.orient W := by
  unfold Converges; rw [hf x W]; exact Iff.rfl

/-- Non-degeneracy: `Or` non-trivial, `orient` not a collapsed constant, `raise` not a collapsed constant. -/
structure NonDegenerate {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (x W : X) : Prop where
  or_nontrivial   : ∃ o₁ o₂ : Or, o₁ ≠ o₂
  orient_nonconst : ∃ p q : X, c.orient p ≠ c.orient q
  raise_nonconst  : ∃ o₁ o₂ : Or, c.raise x W o₁ ≠ c.raise x W o₂

/-! ## The model pair on the witness carrier (both FAITHFUL, differing only in the orientation) -/

/-- The cohering faithful compass: identity raising, orientation AGREEING on the edge (`orient aW = orient
bW = ⟨true⟩`), non-constant globally (`orient aW' = ⟨false⟩`). -/
noncomputable def cHoldF (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW' then ⟨false⟩ else ⟨true⟩
  raise  := fun _ _ o => o

/-- The failing faithful compass: identity raising, orientation DIFFERING on the edge (`orient aW = ⟨true⟩ ≠
⟨false⟩ = orient bW`). Same (identity) raising as `cHoldF`. -/
noncomputable def cFailF (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => o

lemma cHoldF_faithful (hinf : ℵ₀ ≤ κ) : Faithful (cHoldF hinf) := fun _ _ => rfl
lemma cFailF_faithful (hinf : ℵ₀ ≤ κ) : Faithful (cFailF hinf) := fun _ _ => rfl

-- The `orient` values reduce by the kernel (WCar has computable `DecidableEq`), so `rfl`/`up_tf` suffice:
-- `(cHoldF).orient aW ≡ ⟨true⟩ ≡ (cHoldF).orient bW`; `(cFailF).orient aW ≡ ⟨true⟩`, `(cFailF).orient bW ≡ ⟨false⟩`.
lemma cHoldF_converges (hinf : ℵ₀ ≤ κ) : Converges (destW hinf) (reifyW hinf) (cHoldF hinf) aW bW := rfl

lemma cFailF_not_converges (hinf : ℵ₀ ≤ κ) :
    ¬ Converges (destW hinf) (reifyW hinf) (cFailF hinf) aW bW := up_tf

lemma cHoldF_nondeg (hinf : ℵ₀ ≤ κ) : NonDegenerate (destW hinf) (reifyW hinf) (cHoldF hinf) aW bW :=
  ⟨⟨⟨true⟩, ⟨false⟩, up_tf⟩, ⟨aW, aW', up_tf⟩, ⟨⟨true⟩, ⟨false⟩, up_tf⟩⟩

lemma cFailF_nondeg (hinf : ℵ₀ ≤ κ) : NonDegenerate (destW hinf) (reifyW hinf) (cFailF hinf) aW bW :=
  ⟨⟨⟨true⟩, ⟨false⟩, up_tf⟩, ⟨aW, aW', up_tf⟩, ⟨⟨true⟩, ⟨false⟩, up_tf⟩⟩

/-! ## The underdetermination over the faithful class (the wall) -/

/-- **THE UNDERDETERMINATION (the wall), over the FAITHFUL class.** Over the genuine constituency edge
`(aW, bW)` between distinct relata, convergence holds under `cHoldF` and fails under `cFailF`, on the SAME
structure, BOTH FAITHFUL (identical identity raising) and both non-degenerate: the structure fixes the
faithful raising but does not fix the orientation, so it does not decide convergence at this edge. This is
independence FROM the (non-empty) faithful theory, not a typing tautology (PR1-S1). -/
theorem ws4_underdetermined (hinf : ℵ₀ ≤ κ) :
    ConstituentOf (destW hinf) (reifyW hinf) aW bW
  ∧ ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c₁ ∧ Faithful c₂
      ∧ Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨ws3_edge_aW_bW hinf, cHoldF hinf, cFailF hinf,
   cHoldF_faithful hinf, cFailF_faithful hinf,
   cHoldF_converges hinf, cFailF_not_converges hinf, cHoldF_nondeg hinf, cFailF_nondeg hinf⟩

/-- The bare holding-and-failing faithful pair (the projection used by WS5/WS6). -/
theorem ws4_underdetermined_pair (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨cHoldF hinf, cFailF hinf, cHoldF_converges hinf, cFailF_not_converges hinf⟩

/-- **REMARK (NOT load-bearing, PR2-S1).** At the reflexive locus `(aW, aW)` every faithful compass coheres
by `rfl` (the part is the whole). This is a trivial arm at a NON-edge (`aW → aW` is not a `ConstituentOf`
edge; the witness tower has no self-membered reified pattern), so it does NOT carry the falsifiability of the
verdict. The genuine falsifiability lives at the actual edge `(aW, bW)` via the two-zone fork below
(`ws4_decided_within_sight` / `ws4_dissent_is_import`); this lemma is kept only as a remark. -/
theorem ws4_fork_open (hinf : ℵ₀ ≤ κ) :
    ∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
      Faithful c → Converges (destW hinf) (reifyW hinf) c aW aW := by
  intro c hf
  show c.raise aW aW (c.orient aW) = c.orient aW
  rw [hf aW aW]; rfl

/-- **THE NOT-SEEING IS STRUCTURAL (real independence, the bridge IN the proof term).** The two faithful
compasses share the IDENTICAL raising (`rfl`, both the identity, so the sharing is IN the theorem) over the
IDENTICAL structure, everything the structure supplies fixed, yet the verdicts flip on the orientation the
structure does not fix. -/
theorem ws4_wall_is_structural (hinf : ℵ₀ ≤ κ) :
    (cHoldF hinf).raise = (cFailF hinf).raise
  ∧ Converges (destW hinf) (reifyW hinf) (cHoldF hinf) aW bW
  ∧ ¬ Converges (destW hinf) (reifyW hinf) (cFailF hinf) aW bW :=
  ⟨rfl, cHoldF_converges hinf, cFailF_not_converges hinf⟩

/-! ## The TWO-ZONE fork at the genuine edge: decided within sight, an import across the boundary (PR2-S1) -/

/-- **Bisimulation-invariant orientation (what the structure can SEE).** An orientation is within the
structure's sight iff it agrees on every plain-bisimilar pair: plain bisimilarity (the collapse engine) is
exactly what the relating can detect, so a `BisimInvariant` orientation is one the structure fixes. -/
def BisimInvariant {X : Type u} (dest : X → PkObj κ X) {reify : PkObj κ X → X} {Or : Type u}
    (c : Compass dest reify Or) : Prop :=
  ∀ x y : X, (∃ R, IsBisim dest R ∧ R x y) → c.orient x = c.orient y

/-- **DISSENT FROM CONVERGENCE IS AN IMPORT (Series 07's work, as a proof term, PR2-S1).** EVERY faithful
compass that FAILS convergence at the genuine edge `(aW, bW)` does so by a genuine import: its orientation,
lifted to labels, is `¬ Recoverable`. The not-seeing is therefore literally Series 07's import necessity
(`orientLift_not_recoverable`, resting on the plain-bisimilarity of `aW`, `bW`), not a gap. Universally
quantified over compasses (the parametricity discipline holds in the fix). -/
theorem ws4_dissent_is_import (hinf : ℵ₀ ≤ κ) :
    ∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
      Faithful c → ¬ Converges (destW hinf) (reifyW hinf) c aW bW →
      ¬ Recoverable (orientLift (destW hinf) c.orient) := by
  intro c hf hdiss
  have hne : c.orient aW ≠ c.orient bW := fun h =>
    hdiss ((faithful_converges_iff (destW hinf) (reifyW hinf) c hf aW bW).mpr h)
  exact orientLift_not_recoverable (destW hinf) c.orient aW bW
    (ws_SHNE hinf aW) (ws_SHNE hinf bW) hne

/-- **CONVERGENCE IS DECIDED WITHIN SIGHT (the holding direction, PR2-S1).** Every faithful compass whose
orientation is within the structure's sight (`BisimInvariant`) COHERES at the genuine edge `(aW, bW)`:
`aW` and `bW` are plain-bisimilar (the collapse engine), so a sight-bound orientation is forced to agree on
them, and the faithful raising then makes convergence hold. So over the in-sight faithful sub-class the fork
at the SAME edge is CLOSED (convergence-decided), per charter §2-WS4 alternative (a) at the sub-class level.
DISCLOSED (PR3-R1): on THIS every-moment-atomless carrier the in-sight class is inhabited but its members
are orientation-UNIFORM (`ws4_insight_inhabited`, `ws4_sight_is_uniform`), so the coherence in fact holds at
EVERY pair, not only the edge; the edge is where the underdet arm lives, the decided arm merely also passes
through it. -/
theorem ws4_decided_within_sight (hinf : ℵ₀ ≤ κ) :
    ∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
      Faithful c → BisimInvariant (destW hinf) c →
      Converges (destW hinf) (reifyW hinf) c aW bW := by
  intro c hf hbi
  rw [faithful_converges_iff (destW hinf) (reifyW hinf) c hf aW bW]
  exact hbi aW bW (ws1_atomless_bisim (destW hinf) aW bW (ws_SHNE hinf aW) (ws_SHNE hinf bW))

/-- **THE IN-SIGHT CLASS IS INHABITED (PR3-R1).** The constant-orientation faithful compass is in the
in-sight sub-class (`Faithful ∧ BisimInvariant`), so `s12_fork_insight` / `convergenceDecided` rest on a
genuinely inhabited class, not a vacuously-quantified `forcedHolds`. An existential (witnesses the class,
never discharges a `∀`-obligation). -/
theorem ws4_insight_inhabited (hinf : ℵ₀ ≤ κ) :
    ∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
      Faithful c ∧ BisimInvariant (destW hinf) c :=
  ⟨⟨fun _ => ⟨true⟩, fun _ _ o => o⟩, (fun _ _ => rfl), (fun _ _ _ => rfl)⟩

/-- **WITHIN SIGHT IS THE ONE, AT THE ORIENTATION LEVEL (PR3-R1, and it strengthens the reading).** On this
carrier every state is `SHNE`, so every pair is plain-bisimilar (the collapse engine merges the whole
carrier); hence a `BisimInvariant` orientation is UNIFORM (constant on all of `WCar`). The decided zone is
decided BECAUSE what the structure can see admits only the One orientation, Series 07 replayed at the
orientation level. This exposes that every member of the in-sight class is orientation-constant, the
`NonDegenerate.orient_nonconst` degeneracy, disclosed here rather than hidden on the decided side. -/
theorem ws4_sight_is_uniform (hinf : ℵ₀ ≤ κ) :
    ∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
      BisimInvariant (destW hinf) c → ∀ x y : WCar, c.orient x = c.orient y := by
  intro c hbi x y
  exact hbi x y (ws1_atomless_bisim (destW hinf) x y (ws_SHNE hinf x) (ws_SHNE hinf y))

/-- **THE TWO-ZONE FORK, at the genuine edge `(aW, bW)` (PR2-S1).** The fork is open AT THE EDGE where the
verdict is computed, and its boundary is structurally defined (Series 07's import boundary), not a reflexive
triviality: (i) over the full faithful class convergence is UNDERDETERMINED (the `cHoldF`/`cFailF` pair);
(ii) over the in-sight faithful sub-class (`BisimInvariant`) it is DECIDED, forced to hold
(`ws4_decided_within_sight`), so `shape-drawn` is FALSIFIABLE at the edge (restricting to what the structure
sees closes the fork); (iii) every faithful dissent at the edge is a genuine import (`ws4_dissent_is_import`),
so the underdetermination is EXACTLY the import Series 07 characterizes. -/
theorem ws4_two_zone (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c₁ ∧ Faithful c₂
      ∧ Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW)
  ∧ (∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c → BisimInvariant (destW hinf) c →
        Converges (destW hinf) (reifyW hinf) c aW bW)
  ∧ (∀ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c → ¬ Converges (destW hinf) (reifyW hinf) c aW bW →
        ¬ Recoverable (orientLift (destW hinf) c.orient)) :=
  ⟨⟨cHoldF hinf, cFailF hinf, cHoldF_faithful hinf, cFailF_faithful hinf,
     cHoldF_converges hinf, cFailF_not_converges hinf⟩,
   ws4_decided_within_sight hinf, ws4_dissent_is_import hinf⟩

/-- **THE HONEST FORK (the trichotomy), over the faithful class.** Convergence is forced-for-all-faithful,
forbidden-for-all-faithful, or underdetermined within the faithful class; WS4 proves it lands in the third
disjunct at the edge `(aW, bW)` (the model pair), while `ws4_fork_open` inhabits the first at `(aW, aW)`. -/
theorem ws4_convergence_decided_shape (hinf : ℵ₀ ≤ κ) :
    (∀ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)),
        Faithful c → Converges (destW hinf) (reifyW hinf) c aW bW)
  ∨ (∀ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)),
        Faithful c → ¬ Converges (destW hinf) (reifyW hinf) c aW bW)
  ∨ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c₁ ∧ Faithful c₂
      ∧ Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  Or.inr (Or.inr ⟨cHoldF hinf, cFailF hinf, cHoldF_faithful hinf, cFailF_faithful hinf,
    cHoldF_converges hinf, cFailF_not_converges hinf⟩)

/-! ## The LAYERED underdetermination (`ConvergesUp`, up the tower edges) — SR1-2 -/

/-- **Edge classification from `aW`.** The only constituency edge out of `aW` on the witness carrier goes to
`bW`: any `s` with the pointwise reification fact and `aW ∈ s.1` forces `reifyW s = bW`. (The tower graph is
the path `aW → bW → cW`.) -/
private lemma constituentOf_aW (hinf : ℵ₀ ≤ κ) {y : WCar}
    (h : ConstituentOf (destW hinf) (reifyW hinf) aW y) : y = bW := by
  obtain ⟨s, hpt, hmem, hy⟩ := h
  by_cases h1 : s.1 = {aW}
  · rw [hy]; simp only [reifyW]; rw [if_pos h1]
  · by_cases h2 : s.1 = {bW}
    · rw [h2, Set.mem_singleton_iff] at hmem; exact absurd hmem (by decide)
    · exfalso
      have hrs : reifyW hinf s = aW := by simp only [reifyW]; rw [if_neg h1, if_neg h2]
      rw [hrs, destW_aW] at hpt
      exact h1 (by rw [← hpt]; exact toPk_val hinf {aW})

/-- Positive side of the layered pair: `cHoldF` coheres up the single tower edge `aW → bW`. -/
private lemma up_cHoldF (hinf : ℵ₀ ≤ κ) :
    ConvergesUp (destW hinf) (reifyW hinf) (cHoldF hinf) aW bW :=
  Relation.ReflTransGen.single ⟨ws3_edge_aW_bW hinf, cHoldF_converges hinf⟩

/-- Negative side of the layered pair: `cFailF` does not cohere up any tower chain from `aW` to `bW`. The
only first edge is `aW → bW` (`constituentOf_aW`), whose `Converges cFailF` step fails. -/
private lemma no_up_cFailF (hinf : ℵ₀ ≤ κ) :
    ¬ ConvergesUp (destW hinf) (reifyW hinf) (cFailF hinf) aW bW := by
  intro h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨y, hR, _⟩
  · exact absurd heq (by decide)
  · obtain ⟨hcon, hconv⟩ := hR
    have hy : y = bW := constituentOf_aW hinf hcon
    subst hy
    exact cFailF_not_converges hinf hconv

/-- **THE LAYERED UNDERDETERMINATION (SR1-2).** Convergence UP THE LAYERS is underdetermined too, over the
faithful class: two faithful compasses on one structure, one cohering up the tower edge and one not.
Existential (the concrete faithful compasses confined to the witness, never named in the statement). -/
theorem ws4_underdetermined_up (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Faithful c₁ ∧ Faithful c₂
      ∧ ConvergesUp (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ ConvergesUp (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨cHoldF hinf, cFailF hinf, cHoldF_faithful hinf, cFailF_faithful hinf,
   up_cHoldF hinf, no_up_cFailF hinf⟩

end Series12.WS4
