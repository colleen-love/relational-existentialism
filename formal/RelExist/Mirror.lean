/-
# The mirror that can't close — Lawvere's diagonal (theorem T3, σ-side)

Mechanizes the *knowing* side of [T3](../../docs/spec/theorems.md) and the cartesian
"mirror that can't close" of [00 §0.4.2](../../docs/spec/00-doctrine.md): **Lawvere's
fixed-point theorem** and its contrapositive. The whole content is the diagonal
argument — `Type`-level, no mathlib — which is exactly the point: the obstruction is
*cartesian* (it needs copying, `g a a`), and it is what makes self-knowledge leave a
remainder.

* `lawvere`              — a complete self-model forces every endomap to have a fixed
                          point.
* `no_complete_selfModel` — contrapositive: a fixed-point-free endomap ⇒ **no** complete
                          self-model exists (the mirror cannot close).
* `selfModel_remainder`  — for *any* attempted self-model, the diagonal family escapes
                          it: something is always left out of the look.
-/

namespace RelExist.Mirror

universe u v
variable {A : Type u} {B : Type v}

/-- A **complete self-model**: a map `g : A → (A → B)` that realizes *every*
`A`-indexed family — point-surjectivity, spelled out to keep this module mathlib-free. -/
def PointSurjective (g : A → A → B) : Prop := ∀ h : A → B, ∃ a, g a = h

/-- **Lawvere's fixed-point theorem.** If a system `A` admits a *complete self-model* —
a point-surjective `g : A → (A → B)` realizing every `A`-indexed family — then every
endomap `f : B → B` has a fixed point. (The fixed point is the diagonal value
`g a a`.) -/
theorem lawvere (g : A → A → B) (hg : PointSurjective g) (f : B → B) :
    ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := hg (fun a => f (g a a))
  exact ⟨g a a, (congrFun ha a).symm⟩

/-- **The mirror that can't close.** If some endomap `f : B → B` has *no* fixed point,
then `A` admits *no* complete self-model: there is no point-surjective `A → (A → B)`.
Self-representation always leaves a remainder — not for want of effort, but as the
contrapositive of a theorem. -/
theorem no_complete_selfModel (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ g : A → A → B, PointSurjective g := by
  rintro ⟨g, hg⟩
  obtain ⟨b, hb⟩ := lawvere g hg f
  exact hf b hb

/-- The explicit **remainder**: for *any* attempted self-model `g` and any
fixed-point-free `f`, the diagonal family `fun a => f (g a a)` lies in **no** row of `g`
— the very act of looking creates the thing that escapes the look. -/
theorem selfModel_remainder (g : A → A → B) (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ a, g a = fun a' => f (g a' a') := by
  rintro ⟨a, ha⟩
  have h : f (g a a) = g a a := (congrFun ha a).symm
  exact hf (g a a) h

end RelExist.Mirror
