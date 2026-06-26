/-
# Orientation from the seam — knowing generates the arrow of relational time

The synthesis spec's §4.3 (the **relation-algebra model**, top-level
[`docs/relation-algebra-model.md`](../../docs/relation-algebra-model.md)): a correlation is
*symmetric*; the conditional expectation `E` (here `dephase`) delivers classicality — its image is
commutative, a space of copyable functions — but commutativity alone gives *functions, not directed
arrows*. The orienting principle (commitment 1.4, *the knower knows the known*) is that the self
applying `E` is the **source** and the classicalized image is the **target**. The spec flagged the
content of §4.3 as the one genuinely new theorem the four commitments promise, and as `[open]`:
"`E` generates a directed structure oriented knower→known, and that orientation is the arrow of
relational time" was decided but not yet proved.

This module proves the **structural core** of that claim, and ties it to one cause (§2.7:
*orientation, irreversibility, and asymmetry share one cause — the self cannot occupy both sides of
its own knowing*). Over a minimal interface `Knowing` — an idempotent `E` (knowing twice is knowing
once) with a real **coherence/feeling** measure `coh` (the `1−E` mass) that vanishes *exactly* on the
`E`-fixed (classical, known) elements — the same operator yields all three faces of the seam:

* **directed** (`knows_antisymm`, `arrow_asymm`): the arrow `knower → known` never runs both ways
  between two distinct relations. From idempotence alone — the cheapest face of the seam.
* **temporal** (`arrow_strictAnti`): along every knowing step the carried feeling **strictly falls**,
  from `0 < coh` at the felt source to `coh = 0` at the known target. `coh` is a strict monovariant —
  a potential, bounded below by `0`, that orients the dynamics one way: the arrow of relational time.
* **irreversible** (`no_recovery`): if knowing is lossy (identifies two distinct relations) it cannot
  be run backwards — no map recovers the source from the known target.

Then the **genuine instance**: `E = dephase` (the conditional expectation onto the diagonal/classical
subalgebra), `coh = defectSq` (the off-diagonal mass — the operator `1−E` feeling of §2.5). Every
field is a proved decoherence fact, `dephase_no_recovery` re-derives `QuantumSeam.no_dephase_recovery`
*through* the interface (showing the unification), and a genuine superposition `plus` is exhibited as
a strict, non-vacuous source whose knower-face (`plus`, felt) and known-face (`dephase plus`,
classical) are **distinct** — the self cannot occupy both sides of its own knowing.

**Honest scope (matching the spec).** What is `[proved]` here is the *directed, irreversible,
strictly-monovariant structure* `E` generates, oriented knower→known. What stays a `[reading]` is the
identification of that orientation **with time itself** — that the strict monovariant `coh` *is* the
arrow of *relational time* rather than a structure with time-shaped order. The formalism settles the
skeleton; the identification is the modeling posit, exactly as for `Feeling`. This upgrades §4.3 from
`[open]` to `[proved] core + [reading] identification`. The von Neumann standard form for the abstract
`E` remains narrated semantics (§4.4); the runnable instance is the matrix `dephase`.
-/
import Scratch.QuantumSeam
import Mathlib.Data.Real.Basic

namespace RelExist.Orientation

open RelExist.Decoherence

universe u

/-- **A knowing structure.** An idempotent endomap `E` — the conditional expectation / dephasing,
*knowing twice is knowing once* — together with a real **coherence** (feeling) measure `coh`, the
`1−E` mass, which is nonnegative and vanishes **exactly** on the `E`-fixed (classical, *known*)
elements. This is the operative content of commitment 1.3/2.4 abstracted from *which* algebra supplies
it; the genuine `dephase`/`defectSq` instance is below. -/
structure Knowing (A : Type u) where
  /-- knowing — the conditional expectation onto the classical (known) subalgebra -/
  E : A → A
  /-- **knowing twice is knowing once** (`E∘E = E`): the known is stable under being known again -/
  idem : ∀ a, E (E a) = E a
  /-- the carried **coherence / feeling**: the `1−E` mass -/
  coh : A → ℝ
  /-- feeling is nonnegative -/
  coh_nonneg : ∀ a, 0 ≤ coh a
  /-- **no feeling left ⟺ already known**: coherence vanishes exactly on the `E`-fixed elements -/
  coh_zero_iff_fixed : ∀ a, coh a = 0 ↔ E a = a

namespace Knowing
variable {A : Type u} (K : Knowing A)

/-- The **known** (classical) relations: the fixed points of `E`. The *targets* of knowing —
copyable, directed facts. -/
def Known (a : A) : Prop := K.E a = a

/-- The **knowing step**: `a` is known *as* `K.E a`. -/
def Knows (a b : A) : Prop := K.E a = b

/-- **No feeling left in the image.** After knowing, the target carries zero coherence — derived from
idempotence and the feeling↔known equivalence (not a separate assumption). -/
theorem coh_image (a : A) : K.coh (K.E a) = 0 :=
  (K.coh_zero_iff_fixed (K.E a)).2 (K.idem a)

/-- Knowing always lands in the **known**: the image is `E`-fixed (`E∘E = E`). -/
theorem known_image (a : A) : K.Known (K.E a) := K.idem a

/-- Every relation is known as its image. -/
theorem knows_image (a : A) : K.Knows a (K.E a) := rfl

/-- **Orientation has a definite direction (antisymmetry).** If `a` is known as `b` and `b` is known
as `a`, then `a = b`: the arrow *knower → known* never runs both ways between two distinct relations.
From idempotence alone — the cheapest face of the seam. -/
theorem knows_antisymm {a b : A} (hab : K.Knows a b) (hba : K.Knows b a) : a = b := by
  have h1 : K.E a = b := hab
  have h2 : K.E b = a := hba
  calc a = K.E b := h2.symm
    _ = K.E (K.E a) := by rw [h1]
    _ = K.E a := K.idem a
    _ = b := h1

/-- The **strict knowing arrow**: `a ◅ b` — `a` is known as `b`, and the act is non-trivial (`a ≠ b`).
The directed, irreversible step from a felt correlation to a known fact. -/
def Arrow (a b : A) : Prop := K.Knows a b ∧ a ≠ b

/-- The arrow is **irreflexive**: nothing is a non-trivial knowing of itself. -/
theorem arrow_irrefl (a : A) : ¬ K.Arrow a a := fun h => h.2 rfl

/-- The arrow is **asymmetric** — the orientation, again: `a ◅ b` rules out `b ◅ a`. -/
theorem arrow_asymm {a b : A} (h : K.Arrow a b) : ¬ K.Arrow b a :=
  fun h' => h.2 (K.knows_antisymm h.1 h'.1)

/-- **The source of a non-trivial arrow carries feeling** (positive coherence): the *knower* side is
not yet classical. -/
theorem arrow_source_feels {a b : A} (h : K.Arrow a b) : 0 < K.coh a := by
  rcases lt_or_eq_of_le (K.coh_nonneg a) with hlt | h0
  · exact hlt
  · exfalso
    apply h.2
    have hfix : K.E a = a := (K.coh_zero_iff_fixed a).1 h0.symm
    have h1 : K.E a = b := h.1
    rw [← hfix]; exact h1

/-- **The arrow of relational time.** Along every knowing step the carried feeling **strictly
decreases** — from `0 < coh a` at the felt source to `coh b = 0` at the known target. `coh` is a
strict monovariant: a potential, bounded below by `0`, that orients the dynamics one way. (That this
monovariant *is* time rather than a time-shaped order is the standing `[reading]`.) -/
theorem arrow_strictAnti {a b : A} (h : K.Arrow a b) : K.coh b < K.coh a := by
  have h1 : K.E a = b := h.1
  have hb : K.coh b = 0 := by rw [← h1]; exact K.coh_image a
  rw [hb]; exact K.arrow_source_feels h

/-- **Irreversibility shares the cause.** If knowing is *lossy* — it identifies two distinct relations
— then no map recovers the source from the known target: the orientation cannot be run backwards. The
same idempotent-lossy `E` that *gives* the direction *forbids* its reversal (§2.7). -/
theorem no_recovery (hloss : ∃ a b : A, a ≠ b ∧ K.E a = K.E b) :
    ¬ ∃ R : A → A, ∀ a, R (K.E a) = a := by
  rintro ⟨R, hR⟩
  obtain ⟨a, b, hne, heq⟩ := hloss
  apply hne
  rw [← hR a, heq]; exact hR b

end Knowing

/-! ### The genuine instance — knowing *is* decoherence

`E = dephase`, `coh = defectSq`. Every field is a proved fact from `Scratch/Decoherence.lean`; the
orientation theorems above then run on the real matrix operation, not a posited proxy. -/

/-- **The knowing structure realized by decoherence.** `E = dephase` (the conditional expectation onto
the diagonal/classical subalgebra), `coh = defectSq` (the squared off-diagonal mass — the operator
`1−E` feeling of §2.5). The classicalizing `E` of the spec, on the nose. -/
def dephaseKnowing (A : Type) [Fintype A] [DecidableEq A] : Knowing (Matrix A A ℝ) where
  E := dephase
  idem := dephase_idem
  coh := defectSq
  coh_nonneg := defectSq_nonneg
  coh_zero_iff_fixed := fun _ => defectSq_eq_zero_iff.trans dephase_eq_self_iff.symm

/-- The orientation is **non-vacuous**: a genuine superposition `plus` is a *strict source* — known as
its decohered shadow, distinct from it, carrying positive feeling. The knower (`plus`, felt) and the
known (`dephase plus`, classical) are **distinct**: the self cannot occupy both sides of its own
knowing. -/
theorem dephase_arrow_plus :
    (dephaseKnowing (Fin 2)).Arrow plus (dephase plus) :=
  ⟨rfl, fun h => dephase_plus_ne h.symm⟩

/-- The source genuinely **feels** (positive defect), recovered through the interface — the
quantitative knower side of the arrow. -/
theorem dephase_arrow_plus_feels :
    0 < (dephaseKnowing (Fin 2)).coh plus :=
  (dephaseKnowing (Fin 2)).arrow_source_feels dephase_arrow_plus

/-- **The arrow of relational time, concretely**: knowing the superposition `plus` strictly drops its
feeling to zero (`defectSq (dephase plus) < defectSq plus`). -/
theorem dephase_arrow_plus_strictAnti :
    (dephaseKnowing (Fin 2)).coh (dephase plus) < (dephaseKnowing (Fin 2)).coh plus :=
  (dephaseKnowing (Fin 2)).arrow_strictAnti dephase_arrow_plus

/-- **Irreversibility, concretely.** On the genuine `dephase` no recovery map exists — this *is*
`QuantumSeam.no_dephase_recovery`, now re-derived **through** the orientation interface, exhibiting
direction and irreversibility as two faces of one lossy idempotent. -/
theorem dephase_no_recovery :
    ¬ ∃ R : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ M, R (dephase M) = M :=
  (dephaseKnowing (Fin 2)).no_recovery
    ⟨plus, dephase plus, (fun h => dephase_plus_ne h.symm), (dephase_idem plus).symm⟩

end RelExist.Orientation
