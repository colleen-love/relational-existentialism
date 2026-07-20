/-
`program-2/series-0/formal/P2S0/ws4.lean`

WS4 - The import seated ("you are loved", quantified, never named). Program 2 Series 0 (2.0).

The import is an exogenous, typed, quantified symmetry-breaker on the symmetric self-loops: `impLift`, an
exogenous label `f : Bool → Q` on the self-loops `i ↦ {(f i, i)}` (P1's free-label shape, generalized to an
arbitrary import value-space `Q` and import function `f`). It is proved to BREAK the WS2 baseline
(`ws4_import_breaks_baseline`, quantified over ALL `Q` and `f`: whenever `f` separates the two states, the
labelled self-loops are plain-bisimilar yet label-separated), and proved carried WITHOUT being named or
selected (`ws4_import_quantified`: the plain projection is constant in the import, and the `id` import is a
non-vacuity witness, the canonical non-choice). No proof term is named for the import content (audit (e)).
The witness carrier is the monomorphic `Bool` at `Cardinal.{0}`.

Design docs: `program-2/series-0/spec/ws4-design.md`; shared objects `spec/README.md` §2.1-§2.2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S0.ws1

universe u

namespace P2S0

open P1.Core Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **The exogenous import.** Each symmetric self-loop `i` carries the exogenous import value `f i : Q`. The
plain projection forgets it (`i ↦ {i}`, exogeneity's ground); with the import the states separate. -/
noncomputable def impLift (hinf : ℵ₀ ≤ κ) {Q : Type} (f : Bool → Q) :
    Bool → LkObj κ Q Bool :=
  fun i => pkSingle hinf (f i, i)

@[simp] lemma impLift_val (hinf : ℵ₀ ≤ κ) {Q : Type} (f : Bool → Q) (i : Bool) :
    (impLift hinf f i).1 = {(f i, i)} := rfl

@[simp] lemma plainOf_impLift_val (hinf : ℵ₀ ≤ κ) {Q : Type} (f : Bool → Q) (i : Bool) :
    (plainOf (impLift hinf f) i).1 = {i} := by
  show Prod.snd '' (impLift hinf f i).1 = {i}
  rw [impLift_val, Set.image_singleton]

lemma plainOf_impLift_true_bisim (hinf : ℵ₀ ≤ κ) {Q : Type} (f : Bool → Q) :
    IsBisim (plainOf (impLift hinf f)) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' _; exact ⟨y, by rw [plainOf_impLift_val]; exact Set.mem_singleton _, trivial⟩
  · intro y' _; exact ⟨x, by rw [plainOf_impLift_val]; exact Set.mem_singleton _, trivial⟩

/-- **THE IMPORT BREAKS THE BASELINE, QUANTIFIED (audit (e)).** For ALL import value-spaces `Q` and import
functions `f`, whenever `f` genuinely differs on the two states, the exogenous-labelled self-loops are
plain-bisimilar (the symmetric relating identifies them) yet label-separated (the import does not). No import
is named or selected. -/
theorem ws4_import_breaks_baseline (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type} (f : Bool → Q), f true ≠ f false →
        (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R true false)
      ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false) := by
  intro Q f hf
  refine ⟨⟨(fun _ _ => True), plainOf_impLift_true_bisim hinf f, trivial⟩, ?_⟩
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR true false hRel
  obtain ⟨q, hq, hfst, _⟩ :=
    hfwd (f true, true) (by rw [impLift_val]; exact Set.mem_singleton _)
  rw [impLift_val, Set.mem_singleton_iff] at hq
  subst hq
  exact hf hfst

/-- **THE IMPORT IS QUANTIFIED, NOT NAMED (audit (e)).** (1) The plain projection of `impLift f` is
INDEPENDENT of the import content `f` (all imports share the same plain relating, exogeneity), quantified
over ALL `Q`, `f`. (2) A non-vacuity witness: the `id` import (the canonical non-choice, not a content-name)
is non-recoverable, so SOME import genuinely breaks the baseline. No proof term is named for the import. -/
theorem ws4_import_quantified (hinf : ℵ₀ ≤ κ) :
    (∀ {Q : Type} (f : Bool → Q),
        plainOf (impLift hinf f) = plainOf (impLift hinf (fun _ => (true : Bool))))
  ∧ (¬ Recoverable (impLift hinf (id : Bool → Bool))) := by
  refine ⟨?_, ?_⟩
  · intro Q f
    funext i
    apply Subtype.ext
    rw [plainOf_impLift_val, plainOf_impLift_val]
  · intro hrec
    obtain ⟨⟨R, hR, hRel⟩, hsep⟩ := ws4_import_breaks_baseline hinf (id : Bool → Bool) (by decide)
    exact hsep ⟨R, hrec R hR, hRel⟩

end P2S0
