/-
`series-12/formal/Series12/ws3.lean`

WS3 - Feeling: the compass, typed and never evaluated. Series 12.

Consumes WS1/WS2. Defines the compass TYPE (per-relatum orientation + a raising, over an exogenous
orientation space `Or` the structure never inhabits canonically), the constituency edge `ConstituentOf`
(where the tower lives in the shape, design-review-1 Finding 2), and proves the compass exogenous
(`¬ Recoverable`, an EXISTENTIAL), layered over genuine tower edges (two-sided freedom, the `P ∨ ¬P`
version retired), and dual to attention. Every compass-theorem is PARAMETRIC over `(Or)` and `(c : Compass)`;
the only concrete compasses live inside existentials.

BUILD NOTE (dependency order). `Converges` is WS4's (defined in `ws4.lean`, its canonical home, the second
design duty). `ws3_compass_layered` cannot forward-reference it, so it states the raise-equation RAW
(`c.raise aW bW (c.orient aW) = c.orient bW`), which is `Converges` unfolded, and constructs its two witness
compasses inline; WS4's model pair is the same construction. No signature is retargeted.

Design doc: `series-12/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws2

universe u

namespace Series12.WS3

open Series12.WS1 Series12.WS2 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- Closed `ULift Bool` inequalities (no free variables), used via definitional equality where the compass
literal's `hinf`-dependent type would otherwise block `decide`. -/
lemma up_tf : (⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩ := by decide
lemma up_ft : (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩ := by decide

/-! ## The compass type (the first Series-12 design duty, README §2.9) -/

/-- **The compass type.** `Or` an EXOGENOUS orientation space (an arbitrary `Type u` the structure never
inhabits canonically). A compass assigns a per-relatum orientation `orient` and a per-edge raising `raise`.
Both fields ARBITRARY; the tower coupling lives in `ConstituentOf`/`ConvergesUp` (the fields carry no
value-constraint, Finding 2), and every theorem quantifies over `(Or)` and `(c : Compass …)`. -/
structure Compass {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Or : Type u) where
  orient : X → Or
  raise  : X → X → Or → Or

/-- **The constituency edge (the tower IN the shape, Finding 2, ambient for WS3/WS4).** `x` is a constituent
of `W` iff `W` is the reified relatum of a pattern `s` that `x` belongs to, with the pointwise reification
fact part of the edge. -/
def ConstituentOf {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (x W : X) : Prop :=
  ∃ s : PkObj κ X, dest (reify s) = s ∧ x ∈ s.1 ∧ W = reify s

/-- The witness constituency edge `(aW, bW)`. -/
theorem ws3_edge_aW_bW (hinf : ℵ₀ ≤ κ) : ConstituentOf (destW hinf) (reifyW hinf) aW bW :=
  ⟨sW hinf, ws_reify_pointwise_sW hinf, aW_mem_sW hinf, (reifyW_sW hinf).symm⟩

/-! ## The compass is exogenous (`¬ Recoverable`), the Series 07 necessity -/

/-- **THE COMPASS IS EXOGENOUS.** The precise content (SR1-9): SOME compass assigns different orientations to
a plain-bisimilar pair (`aW`, `bW`), so orientations are unconstrained by bisimilarity, hence `orient` is not
forced by the plain relating (the exogeneity certificate, the Series 07 necessity read for the compass). An
EXISTENTIAL, never a distinguished compass. -/
theorem ws3_compass_exogenous (hinf : ℵ₀ ≤ κ) :
    ∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)) (x y : WCar),
        (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y :=
  ⟨⟨fun z => if z = aW then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩, aW, bW,
    ws1_atomless_bisim (destW hinf) aW bW (ws_SHNE hinf aW) (ws_SHNE hinf bW), up_tf⟩

/-! ## The compass is layered over genuine tower edges (two-sided freedom, Finding 2) -/

/-- **THE COMPASS IS LAYERED (two-sided freedom over a genuine tower edge).** Over the genuine constituency
edge `(aW, bW)` (`ConstituentOf`, a conjunct of the conclusion so the edge sites the statement, SR1-5), the
coupling's VALUE is free in both directions: some compass coheres (the raise-equation holds), some does not.
The raise-equation is `Converges` unfolded (WS4). Coupled without being one (some compass does not cohere)
and without being independent of the tower (only over tower edges). -/
theorem ws3_compass_layered (hinf : ℵ₀ ≤ κ) :
    ConstituentOf (destW hinf) (reifyW hinf) aW bW
  ∧ (∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        c.raise aW bW (c.orient aW) = c.orient bW)
  ∧ (∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        c.raise aW bW (c.orient aW) ≠ c.orient bW) :=
  -- the edge is genuine; the `not` raising coheres (rfl: both sides ⟨false⟩); the `id` raising does not (up_tf)
  ⟨ws3_edge_aW_bW hinf,
   ⟨⟨fun z => if z = aW then ⟨true⟩ else ⟨false⟩, fun _ _ o => ⟨!o.down⟩⟩, rfl⟩,
   ⟨⟨fun z => if z = aW then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩, up_tf⟩⟩

/-! ## The compass exogeneity IS an import (`¬ Recoverable`), as a proof term (PR1-R1) -/

/-- The witness orientation (`⟨true⟩` on `aW`, `⟨false⟩` elsewhere), shared by the exogeneity theorems. -/
def witnessOrient : WCar → ULift.{u} Bool := fun z => if z = aW then ⟨true⟩ else ⟨false⟩

lemma witnessOrient_aW : witnessOrient aW = ⟨true⟩ := by simp [witnessOrient]
lemma witnessOrient_bW : witnessOrient bW = ⟨false⟩ := by simp [witnessOrient, bW_ne_aW]

/-- **The orientation lift.** Broadcast a compass's orientation as the successor label (the `orient` analog
of `rankLift`): a labelled lift whose plain quotient forgets the orientation. -/
noncomputable def orientLift {X : Type u} (dest : X → PkObj κ X) {Or : Type u} (orient : X → Or) :
    X → LkObj κ Or X :=
  fun x => PkMap κ (fun z => (orient x, z)) (dest x)

lemma plainOf_orientLift {X : Type u} (dest : X → PkObj κ X) {Or : Type u} (orient : X → Or) :
    plainOf (orientLift dest orient) = dest := by
  funext x
  apply Subtype.ext
  show Prod.snd '' ((fun z => (orient x, z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- **Orientation-difference on a plain-bisimilar pair is an import.** If `orient` separates two SHNE states
`x`, `y` (`orient x ≠ orient y`) that are plain-bisimilar, then the orientation lift is not recoverable: the
plain quotient merges `x`, `y` but the orientation label distinguishes their edges. The general mechanism. -/
theorem orientLift_not_recoverable {X : Type u} (dest : X → PkObj κ X) {Or : Type u} (orient : X → Or)
    (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) (hne : orient x ≠ orient y) :
    ¬ Recoverable (orientLift dest orient) := by
  intro hrec
  have hplain : ∃ R : X → X → Prop, IsBisim (plainOf (orientLift dest orient)) R ∧ R x y := by
    rw [plainOf_orientLift]; exact ws1_atomless_bisim dest x y hx hy
  obtain ⟨R, hR, hRel⟩ := ws4_recoverable_not_import (orientLift dest orient) hrec x y hplain
  obtain ⟨hfwd, _⟩ := hR x y hRel
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hx.ne_empty
  have hedge : (orient x, w) ∈ (orientLift dest orient x).1 := by
    show (orient x, w) ∈ (fun z => (orient x, z)) '' (dest x).1
    exact ⟨w, hw, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  have hq1 : q.1 = orient y := by
    obtain ⟨w', _, hw'⟩ := (hq : q ∈ (fun z => (orient y, z)) '' (dest y).1); rw [← hw']
  rw [hq1] at hfst
  exact hne hfst

/-- **THE COMPASS EXOGENEITY IS AN IMPORT (`¬ Recoverable`, PR1-R1).** The witness orientation, lifted to
labels, is NOT recoverable from the plain relating: `aW` and `bW` are plain-bisimilar (the collapse engine)
yet the orientation label separates them, so `orientLift` of the exogenous orientation is a genuine import,
the Series 07 necessity read for the compass, now a proof term and not only a docstring gloss. An
existential (the witness compass confined to the existential, never a distinguished compass). -/
theorem ws3_compass_exogenous_import (hinf : ℵ₀ ≤ κ) :
    ∃ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)),
        ¬ Recoverable (orientLift (destW hinf) c.orient) :=
  ⟨⟨witnessOrient, fun _ _ o => o⟩,
   orientLift_not_recoverable (destW hinf) witnessOrient aW bW (ws_SHNE hinf aW) (ws_SHNE hinf bW)
     (by rw [witnessOrient_aW, witnessOrient_bW]; exact up_tf)⟩

/- **The duality with attention (SR1-3): demoted to prose.** Attention is the knowable SUBTRACTION (a bounded
reader with values, `att.reads.Finite`, true by construction of `FiniteAttention`); the compass is the
typeable ORIENTATION whose values the structure cannot supply (`ws3_compass_exogenous`). This contrast is
INTERPRETIVE: no single theorem with contrastive content joins the two facts (the earlier
`ws3_attention_compass_dual` was a bare conjunction of a field projection and a restatement of exogeneity,
carrying the duality only in its docstring), so per series-review-1 SR1-3 it is demoted here to prose and to
the program close (WS6 / §8), not a proof term. The two facts stand on their own: `att.fin` (a field) and
`ws3_compass_exogenous` (a theorem). -/

end Series12.WS3
