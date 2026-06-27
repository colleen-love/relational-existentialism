/-
# Lived identity `≈` and the shared world `𝔼` — theorem 3.2

A faithful mechanization of [spec 3.2](../../docs/spec/03-theorems.md): the lived
identity is the **greatest fixed point of a monotone operator on the complete
lattice of relations** — i.e. the greatest bisimulation, `≈ := νΘ`. Concretely we use
mathlib's `OrderHom.gfp` (Knaster–Tarski), which is exactly the `ν`-modality the spec
needs (the doctrine's `ν` for `≈` is gfp-on-a-lattice, not codata).

We then derive:
* `bisim_unfold` — `≈` is a fixed point of one-step indistinguishability (`Θ ≈ = ≈`);
* `bisim_coind` — **coinduction**: every bisimulation is contained in `≈` (the proof
  principle "to show two states share a lived identity (bisimilar), exhibit a bisimulation");
* `bisim_refl/symm/trans` — `≈` is an equivalence; hence
* `World := D/≈` — the **shared world `𝔼`** as a quotient (3.2).

This needs only `Mathlib.Order.FixedPoints` (already compiled), so it builds fast.
-/
import Mathlib.Order.FixedPoints

namespace RelExist.We

variable {X O : Type*}

/-- One unfolding `Θ` of one-step bisimulation (behaving the same now and onward), as a **monotone operator
on the complete lattice of relations** `X → X → Prop`. Here `obs : X → O` is the
immediate observation and `step a a'` reads "`a'` is a one-step successor of `a`".
`Θ R a b` holds iff `a` and `b` agree on `obs` and each one's successors are
`R`-matched by the other's — one step of "behaving the same". -/
def Step (obs : X → O) (step : X → X → Prop) :
    (X → X → Prop) →o (X → X → Prop) where
  toFun R a b :=
    obs a = obs b ∧
      (∀ a', step a a' → ∃ b', step b b' ∧ R a' b') ∧
      (∀ b', step b b' → ∃ a', step a a' ∧ R a' b')
  monotone' := by
    intro R S hRS a b hab
    obtain ⟨ho, hf, hbk⟩ := hab
    refine ⟨ho, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', hr⟩ := hf a' ha'
      exact ⟨b', hb', hRS a' b' hr⟩
    · intro b' hb'
      obtain ⟨a', ha', hr⟩ := hbk b' hb'
      exact ⟨a', ha', hRS a' b' hr⟩

/-- **Lived identity `≈ := νΘ`** — the greatest bisimulation (theorem 3.2). -/
def bisim (obs : X → O) (step : X → X → Prop) : X → X → Prop :=
  (Step obs step).gfp

/-- `≈` is a fixed point of one-step indistinguishability: `Θ ≈ = ≈`. -/
theorem bisim_unfold (obs : X → O) (step : X → X → Prop) :
    (Step obs step) (bisim obs step) = bisim obs step :=
  (Step obs step).map_gfp

/-- **Coinduction**, raw form: any post-fixed point of `Θ` (any bisimulation) is
below `≈`. -/
theorem bisim_coind (obs : X → O) (step : X → X → Prop)
    {R : X → X → Prop} (hR : R ≤ (Step obs step) R) : R ≤ bisim obs step :=
  (Step obs step).le_gfp hR

/-- **Coinduction**, usable form. To prove two states share a lived identity (bisimilar), give
a relation `R` relating them that is closed under one step (a bisimulation). -/
theorem bisim_of_bisimulation (obs : X → O) (step : X → X → Prop)
    {R : X → X → Prop}
    (hR : ∀ a b, R a b →
      obs a = obs b ∧
        (∀ a', step a a' → ∃ b', step b b' ∧ R a' b') ∧
        (∀ b', step b b' → ∃ a', step a a' ∧ R a' b'))
    {a b : X} (h : R a b) : bisim obs step a b :=
  bisim_coind obs step (fun x y hxy => hR x y hxy) a b h

/-- `≈` is reflexive: the diagonal is a bisimulation (a state behaves like itself). -/
theorem bisim_refl (obs : X → O) (step : X → X → Prop) (a : X) :
    bisim obs step a a :=
  bisim_of_bisimulation obs step
    (R := fun x y => x = y)
    (by rintro x y rfl; exact ⟨rfl, fun x' h => ⟨x', h, rfl⟩, fun y' h => ⟨y', h, rfl⟩⟩)
    (rfl)

/-- `≈` is symmetric. -/
theorem bisim_symm (obs : X → O) (step : X → X → Prop) {a b : X}
    (h : bisim obs step a b) : bisim obs step b a := by
  refine bisim_of_bisimulation obs step (R := fun x y => bisim obs step y x) ?_ h
  intro x y hxy
  have hxy' : (Step obs step) (bisim obs step) y x := by rw [bisim_unfold]; exact hxy
  obtain ⟨ho, hyf, hyb⟩ := hxy'
  exact ⟨ho.symm, hyb, hyf⟩

/-- `≈` is transitive: relational composition of bisimulations is a bisimulation. -/
theorem bisim_trans (obs : X → O) (step : X → X → Prop) {a b c : X}
    (hab : bisim obs step a b) (hbc : bisim obs step b c) : bisim obs step a c := by
  refine bisim_of_bisimulation obs step
    (R := fun x z => ∃ y, bisim obs step x y ∧ bisim obs step y z) ?_ ⟨b, hab, hbc⟩
  rintro x z ⟨y, hxy, hyz⟩
  have hxy' : (Step obs step) (bisim obs step) x y := by rw [bisim_unfold]; exact hxy
  have hyz' : (Step obs step) (bisim obs step) y z := by rw [bisim_unfold]; exact hyz
  obtain ⟨hoxy, hxf, hxb⟩ := hxy'
  obtain ⟨hoyz, hyf, hyb⟩ := hyz'
  refine ⟨hoxy.trans hoyz, ?_, ?_⟩
  · intro x' hx'
    obtain ⟨y', hyy', hx'y'⟩ := hxf x' hx'
    obtain ⟨z', hzz', hy'z'⟩ := hyf y' hyy'
    exact ⟨z', hzz', y', hx'y', hy'z'⟩
  · intro z' hz'
    obtain ⟨y', hyy', hy'z'⟩ := hyb z' hz'
    obtain ⟨x', hxx', hx'y'⟩ := hxb y' hyy'
    exact ⟨x', hxx', y', hx'y', hy'z'⟩

/-- `≈` is an equivalence relation, hence a genuine `Setoid` on the state space. -/
def bisimSetoid (obs : X → O) (step : X → X → Prop) : Setoid X where
  r := bisim obs step
  iseqv := ⟨bisim_refl obs step, bisim_symm obs step, bisim_trans obs step⟩

/-- **The shared world `𝔼 := D/≈`** (theorem 3.2): states quotiented by lived
identity — the objective world as the overlap of perspectives. -/
abbrev World (obs : X → O) (step : X → X → Prop) : Type _ :=
  Quotient (bisimSetoid obs step)

end RelExist.We
