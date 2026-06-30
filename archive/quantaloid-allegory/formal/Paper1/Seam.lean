/-
# Theorem 6 — The seam (reflexive opacity)

**A self cannot fully model the relation that includes it.** This is **Lawvere's diagonal argument**, and it
is **arena-independent** — Lawvere is Lawvere — so it ports from the archived (traced-SMC) development
verbatim, depending on **no axioms** and on nothing about `Q`. It is the most directly portable result.

Three faces are claimed for the seam (`spec/03-theorem-debt.md`): (6a) reflexive opacity — proved here; (6b)
the relational route (knowing another is partial self-knowledge); (6c) the relational bound (you cannot wholly
know another's knowing of you). The conjecture is that these are **one irreducibility read three ways**; only
(6a) is established arena-independently here — (6b)/(6c) need the quantitative converse structure and are
recorded as open.
-/
import Paper1.Arena

namespace Paper1.Seam

variable {A B : Type*}

/-- A **complete self-model**: a map `g` realizing *every* `A`-indexed family of `B`-values — a self that can
represent every way it could relate. -/
def PointSurjective (g : A → A → B) : Prop := ∀ f : A → B, ∃ a, g a = f

/-- **Lawvere's fixed-point theorem.** A complete self-model forces every endomap `f : B → B` to have a fixed
point (the diagonal value `g a a`). Pure, **0 axioms**. -/
theorem lawvere (g : A → A → B) (hg : PointSurjective g) (f : B → B) : ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := hg (fun a => f (g a a))
  exact ⟨g a a, (congrFun ha a).symm⟩

/-- **Theorem 6a (reflexive opacity).** If some endomap `f : B → B` has *no* fixed point, then there is **no
complete self-model** `A → A → B`. Self-representation always leaves a remainder — the **seam** — not for want
of effort but as the contrapositive of Lawvere. Arena-independent; **0 axioms**. -/
theorem reflexive_opacity (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ g : A → A → B, PointSurjective g := by
  rintro ⟨g, hg⟩
  obtain ⟨b, hb⟩ := lawvere g hg f
  exact hf b hb

end Paper1.Seam
