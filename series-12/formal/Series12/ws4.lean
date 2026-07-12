/-
`series-12/formal/Series12/ws4.lean`

WS4 - Convergence: defined, then proved underdetermined (the wall). Series 12, the uncertain obligation.

Consumes WS3 (the compass type, `ConstituentOf`) and WS2 (the carrier). Defines the convergence relation
`Converges` (a real equation over a constituency edge, the second design duty) and its layered closure
`ConvergesUp` (restricted to `ConstituentOf` edges, Finding 2), and proves it UNDERDETERMINED: two compasses
on the SAME structure, sharing the same non-constant orientation and differing ONLY in the free raising, one
cohering and one not, both non-degenerate. `ws4_wall_is_structural` (Finding 3) proves the real independence
(shared orient, opposite verdicts) with the bridge IN the proof term. Never decided by definition.

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

/-- Non-degeneracy: `Or` non-trivial, `orient` not a collapsed constant, `raise` not a collapsed constant. -/
structure NonDegenerate {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (x W : X) : Prop where
  or_nontrivial   : ∃ o₁ o₂ : Or, o₁ ≠ o₂
  orient_nonconst : ∃ p q : X, c.orient p ≠ c.orient q
  raise_nonconst  : ∃ o₁ o₂ : Or, c.raise x W o₁ ≠ c.raise x W o₂

/-! ## The model pair on the witness carrier (same `orient`, differing only in the raising) -/

/-- The cohering compass: the `not` raising (`raise (orient aW) = ⟨false⟩ = orient bW`). -/
noncomputable def cHold (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => ⟨!o.down⟩

/-- The failing compass: the `id` raising (`raise (orient aW) = ⟨true⟩ ≠ orient bW`). Same `orient` as `cHold`. -/
noncomputable def cFail (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => o

-- `up_tf`/`up_ft` are the closed `ULift Bool` inequalities (from WS3), used via definitional equality:
-- `(cHold).orient aW ≡ ⟨true⟩`, `(cHold).orient bW ≡ ⟨false⟩`, `(cHold).raise aW bW ⟨true⟩ ≡ ⟨false⟩`, etc.
lemma cHold_converges (hinf : ℵ₀ ≤ κ) : Converges (destW hinf) (reifyW hinf) (cHold hinf) aW bW := rfl

lemma cFail_not_converges (hinf : ℵ₀ ≤ κ) :
    ¬ Converges (destW hinf) (reifyW hinf) (cFail hinf) aW bW := up_tf

lemma cHold_nondeg (hinf : ℵ₀ ≤ κ) : NonDegenerate (destW hinf) (reifyW hinf) (cHold hinf) aW bW :=
  ⟨⟨⟨true⟩, ⟨false⟩, up_tf⟩, ⟨aW, bW, up_tf⟩, ⟨⟨true⟩, ⟨false⟩, up_ft⟩⟩

lemma cFail_nondeg (hinf : ℵ₀ ≤ κ) : NonDegenerate (destW hinf) (reifyW hinf) (cFail hinf) aW bW :=
  ⟨⟨⟨true⟩, ⟨false⟩, up_tf⟩, ⟨aW, bW, up_tf⟩, ⟨⟨true⟩, ⟨false⟩, up_tf⟩⟩

/-- **THE UNDERDETERMINATION (the wall).** Over the genuine constituency edge `(aW, bW)`, convergence holds
under `cHold` and fails under `cFail`, on the SAME structure, both non-degenerate: the structure does not
decide it. -/
theorem ws4_underdetermined (hinf : ℵ₀ ≤ κ) :
    ConstituentOf (destW hinf) (reifyW hinf) aW bW
  ∧ ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨ws3_edge_aW_bW hinf, cHold hinf, cFail hinf,
   cHold_converges hinf, cFail_not_converges hinf, cHold_nondeg hinf, cFail_nondeg hinf⟩

/-- The bare holding-and-failing pair (the projection used by WS5/WS6). -/
theorem ws4_underdetermined_pair (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨cHold hinf, cFail hinf, cHold_converges hinf, cFail_not_converges hinf⟩

/-- **THE NOT-SEEING IS STRUCTURAL (real independence, the bridge IN the proof term, Finding 3).** The two
compasses share the IDENTICAL `orient` (`rfl`) over the IDENTICAL structure, everything the structure
supplies fixed, yet the verdicts flip on the exogenous raising alone. -/
theorem ws4_wall_is_structural (hinf : ℵ₀ ≤ κ) :
    (cHold hinf).orient = (cFail hinf).orient
  ∧ Converges (destW hinf) (reifyW hinf) (cHold hinf) aW bW
  ∧ ¬ Converges (destW hinf) (reifyW hinf) (cFail hinf) aW bW :=
  ⟨rfl, cHold_converges hinf, cFail_not_converges hinf⟩

/-- **THE HONEST FORK (the trichotomy).** Convergence is forced-for-all, forbidden-for-all, or
underdetermined; WS4 proves it lands in the third disjunct (the model pair). -/
theorem ws4_convergence_decided_shape (hinf : ℵ₀ ≤ κ) :
    (∀ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)),
        Converges (destW hinf) (reifyW hinf) c aW bW)
  ∨ (∀ (c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool)),
        ¬ Converges (destW hinf) (reifyW hinf) c aW bW)
  ∨ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  Or.inr (Or.inr (ws4_underdetermined_pair hinf))

end Series12.WS4
