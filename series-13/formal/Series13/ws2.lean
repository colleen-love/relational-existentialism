/-
`series-13/formal/Series13/ws2.lean`

WS2 - The mint and the transport theorem. Series 13. Near-certain.

Consumes WS1 (the carrier, the two orders, the `Lab` codomain and its realization `coalg`). Builds the
MINT `mintL insp = ⟨residue insp, insp h₀⟩` (residue-position broadcasts the residue, reference-position
broadcasts `insp h₀`), and proves the TRANSPORT `ws2_mint_lands_in_opening` (for every inspection the minted
label fails `Recoverable`, the engine the diagonal `ws2_residue_distinct`) and the EXOGENEITY
`ws2_mint_exogenous` (the plain projection is constant in the inspection, yet the mint is not, so the plain
relating cannot perform it).

Design doc: `series-13/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series13.ws1

universe u

namespace Series13.WS2

open Series13.WS1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The mint (README §2.7) -/

/-- **The mint.** From an inspection, the labelled coalgebra whose residue-position broadcasts the residue
and whose reference-position broadcasts `insp h₀`. -/
def mintL {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (insp : Insp dest) : Lab dest h₀ :=
  ⟨residue insp, insp h₀⟩

@[simp] lemma mintL_cT {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (insp : Insp dest) :
    (mintL h₀ insp).cT = residue insp := rfl

@[simp] lemma mintL_cF {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (insp : Insp dest) :
    (mintL h₀ insp).cF = insp h₀ := rfl

/-- The `⊤`-relation is a plain-bisimulation of any `coalg b`'s plain projection (`i ↦ {i}`). -/
lemma coalg_plain_true_bisim {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    (b : Lab dest h₀) : IsBisim (plainOf (coalg hinf b)) (fun _ _ => True) := by
  intro x y _
  refine ⟨?_, ?_⟩
  · intro x' hx'
    refine ⟨y, ?_, trivial⟩
    rw [plainOf_coalg_val]; exact Set.mem_singleton y
  · intro y' hy'
    refine ⟨x, ?_, trivial⟩
    rw [plainOf_coalg_val]; exact Set.mem_singleton x

/-! ## The transport theorem -/

/-- **THE TRANSPORT THEOREM.** For every inspection, the minted labelled coalgebra fails `Recoverable`.
Engine: the diagonal. `⊤` is a plain-bisimulation but not a label-bisimulation, because at
`(⟨true⟩, ⟨false⟩)` the residue-position label `residue insp` must match the reference-position label
`insp h₀`, and `ws2_residue_distinct` forbids it. -/
theorem ws2_mint_lands_in_opening {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ)
    (insp : Insp dest) :
    Opening (@Recoverable κ (HoldPred dest) (MCar dest)) (coalg hinf (mintL h₀ insp)) := by
  intro hrec
  have hlab : IsBisimL (coalg hinf (mintL h₀ insp)) (fun _ _ => True) :=
    hrec _ (coalg_plain_true_bisim hinf (mintL h₀ insp))
  obtain ⟨hforward, _⟩ := hlab ⟨true⟩ ⟨false⟩ trivial
  obtain ⟨q, hq, hfst, _⟩ := hforward (residue insp, ⟨true⟩) (by
    rw [coalg_true]; exact Set.mem_singleton _)
  rw [coalg_false, Set.mem_singleton_iff] at hq
  subst hq
  -- hfst : (residue insp, ⟨true⟩).1 = (insp h₀, ⟨false⟩).1, i.e. residue insp = insp h₀
  exact ws2_residue_distinct dest insp h₀ hfst.symm

/-- **Forced-for-all packaging.** -/
theorem ws2_transport_forall {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∀ insp : Insp dest, ¬ Recoverable (coalg hinf (mintL h₀ insp)) :=
  fun insp => ws2_mint_lands_in_opening h₀ hinf insp

/-! ## The exogeneity theorem -/

/-- **THE EXOGENEITY.** Two inspections the plain relating cannot tell apart (their minted coalgebras share
the same plain projection `i ↦ {i}`) receive DIFFERENT mints. So no function of the plain relating alone can
reproduce the mint; it consumes inspective data above the plain layer, and no contradiction with Series 07
threatens. -/
theorem ws2_mint_exogenous {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∃ i₁ i₂ : Insp dest,
        plainOf (coalg hinf (mintL h₀ i₁)) = plainOf (coalg hinf (mintL h₀ i₂))
      ∧ mintL h₀ i₁ ≠ mintL h₀ i₂ := by
  refine ⟨(fun _ _ => True), (fun _ _ => False), ?_, ?_⟩
  · -- plain projections coincide: both are i ↦ {i}
    funext i
    apply Subtype.ext
    rw [plainOf_coalg_val, plainOf_coalg_val]
  · -- the mints differ: residue ⊤i = ⊥ ≠ ⊤ = residue ⊥i (the cT components)
    intro he
    have hcT : residue (fun _ _ : Hold dest => True) = residue (fun _ _ : Hold dest => False) :=
      congrArg Lab.cT he
    have := congrFun hcT h₀
    simp only [residue, diag] at this
    exact absurd this (by simp)

/-- **The sharp corollary.** There is NO function from the plain relating that reproduces the mint. -/
theorem ws2_mint_not_plain_function {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ g : (MCar dest → PkObj κ (MCar dest)) → Lab dest h₀,
        ∀ insp : Insp dest, mintL h₀ insp = g (plainOf (coalg hinf (mintL h₀ insp))) := by
  rintro ⟨g, hg⟩
  obtain ⟨i₁, i₂, hplain, hne⟩ := ws2_mint_exogenous h₀ hinf
  exact hne (by rw [hg i₁, hg i₂, hplain])

end Series13.WS2
