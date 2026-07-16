/-
`series-13/formal/Series13/ws3.lean`

WS3 - The connection (the fit). Series 13.

Consumes WS1 (the two orders) and WS2 (the mint). Builds the ADJOINT `readInsp` (realize the reference-folded
residue-label as a residue), proves the `GaloisConnection` between the WS1 orders (`ws3_galois`, the iff exact
by the fold), exhibits the round trips as closure (`readInsp ∘ mintL`, the identity up to the order) and
interior (`mintL ∘ readInsp`, below the identity) operators, and proves the interior NON-identity on a named
element (`ws3_roundtrip_not_identity`), so the connection is genuinely adjoint, not an isomorphism in disguise.

Design doc: `series-13/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series13.ws2

universe u

namespace Series13.WS3

open Series13.WS1 Series13.WS2 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The adjoint (README §2.7) -/

/-- Realize a content as a residue: `residue (realizeAsResidue c) = c`. -/
def realizeAsResidue {X : Type u} {dest : X → PkObj κ X} (c : HoldPred dest) : Insp dest :=
  fun _ h' => ¬ c h'

lemma residue_realizeAsResidue {X : Type u} {dest : X → PkObj κ X} (c : HoldPred dest) :
    residue (realizeAsResidue c) = c := by
  funext h
  simp only [residue, diag, realizeAsResidue, not_not]

/-- The reference-fold: `gb b h = b.cT h ∧ (h ≠ h₀ ∨ ¬ b.cF h₀)`. Folds the reference-bit at `h₀` into the
residue-label, lossy exactly when `b.cF h₀` holds. -/
def gb {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (b : Lab dest h₀) : HoldPred dest :=
  fun h => b.cT h ∧ (h ≠ h₀ ∨ ¬ b.cF h₀)

/-- **The adjoint** (best approximation): the inspection whose residue is the reference-folded label. -/
def readInsp {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (b : Lab dest h₀) : Insp dest :=
  realizeAsResidue (gb h₀ b)

@[simp] lemma residue_readInsp {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (b : Lab dest h₀) :
    residue (readInsp h₀ b) = gb h₀ b := residue_realizeAsResidue _

/-! ## The Galois connection -/

/-- **THE GALOIS CONNECTION.** `mintL h₀ insp ≤ b ↔ insp ≤ readInsp h₀ b`, both sides equal
`leC (residue insp) (gb h₀ b)`, the reference-fold making the iff exact. -/
theorem ws3_galois {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) :
    GaloisConnection (mintL h₀ : Insp dest → Lab dest h₀) (readInsp h₀) := by
  intro insp b
  -- RHS: insp ≤ readInsp h₀ b  ≡  leC (residue insp) (gb h₀ b)
  have hRHS : (insp ≤ readInsp h₀ b) = leC (residue insp) (gb h₀ b) := by
    show leC (residue insp) (residue (readInsp h₀ b)) = _
    rw [residue_readInsp]
  -- LHS: mintL h₀ insp ≤ b  ≡  leC (residue insp) b.cT ∧ (b.cF h₀ → (insp h₀) h₀)
  constructor
  · rintro ⟨hcT, href⟩
    rw [hRHS]
    intro h hch
    refine ⟨hcT h hch, ?_⟩
    by_cases hh : h = h₀
    · subst hh
      right
      intro hcF
      -- insp h h : from href hcF; but residue insp h = ¬ insp h h, and hch : residue insp h
      exact (hch) (href hcF)
    · exact Or.inl hh
  · intro hle
    rw [hRHS] at hle
    refine ⟨fun h hch => (hle h hch).1, ?_⟩
    intro hcF
    -- goal: (insp h₀) h₀.  by_contra: ¬ insp h₀ h₀ = residue insp h₀ = c h₀, feed to hle
    by_contra hn
    have hc0 : residue insp h₀ := hn
    have := (hle h₀ hc0).2
    rcases this with hne | hnotcF
    · exact hne rfl
    · exact hnotcF hcF

/-- The mint is monotone (from the Galois connection). -/
theorem ws3_mint_monotone {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) :
    Monotone (mintL h₀ : Insp dest → Lab dest h₀) := (ws3_galois h₀).monotone_l

/-- The adjoint is monotone (from the Galois connection). -/
theorem ws3_read_monotone {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) :
    Monotone (readInsp h₀ : Lab dest h₀ → Insp dest) := (ws3_galois h₀).monotone_u

/-! ## The round trips -/

/-- On minted coalgebras the reference-fold is inert: `gb h₀ (mintL h₀ insp) = residue insp`. -/
lemma gb_mintL {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (insp : Insp dest) :
    gb h₀ (mintL h₀ insp) = residue insp := by
  funext h
  simp only [gb, mintL_cT, mintL_cF]
  apply propext
  constructor
  · exact fun hh => hh.1
  · intro hres
    refine ⟨hres, ?_⟩
    by_cases hh : h = h₀
    · subst hh; exact Or.inr hres
    · exact Or.inl hh

/-- **The closure round trip is the identity** (up to the order): `readInsp ∘ mintL` recovers the residue. -/
theorem ws3_roundtrip_closure {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (insp : Insp dest) :
    readInsp h₀ (mintL h₀ insp) ≤ insp ∧ insp ≤ readInsp h₀ (mintL h₀ insp) := by
  have hkey : residue (readInsp h₀ (mintL h₀ insp)) = residue insp := by
    rw [residue_readInsp, gb_mintL]
  refine ⟨?_, ?_⟩
  · show leC (residue (readInsp h₀ (mintL h₀ insp))) (residue insp)
    rw [hkey]; exact leC_refl _
  · show leC (residue insp) (residue (readInsp h₀ (mintL h₀ insp)))
    rw [hkey]; exact leC_refl _

/-- **The interior round trip is below the identity**: `mintL ∘ readInsp ≤ id`. -/
theorem ws3_roundtrip_interior {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (b : Lab dest h₀) :
    mintL h₀ (readInsp h₀ b) ≤ b := (ws3_galois h₀).l_u_le b

/-! ## The non-identity round trip (the fit) -/

/-- The named element: both self-loop labels the constant-true content. Its reference-bit at `h₀` is active. -/
def bRefActive {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) : Lab dest h₀ :=
  ⟨(fun _ => True), (fun _ => True)⟩

/-- **THE NON-IDENTITY ROUND TRIP.** On `bRefActive` the interior is STRICTLY below the identity: the active
reference-bit makes the fold drop `h₀`, so the re-minted residue-label `⊤ ∖ {h₀}` is not `≥ ⊤`. The
connection is a genuine adjunction, not an isomorphism. -/
theorem ws3_roundtrip_not_identity {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) :
    mintL h₀ (readInsp h₀ (bRefActive dest h₀)) ≤ bRefActive dest h₀
  ∧ ¬ (bRefActive dest h₀ ≤ mintL h₀ (readInsp h₀ (bRefActive dest h₀))) := by
  refine ⟨ws3_roundtrip_interior h₀ _, ?_⟩
  rintro ⟨hcT, _⟩
  -- hcT : leC bRefActive.cT (mintL h₀ (readInsp h₀ bRefActive)).cT
  -- (mintL ... ).cT = residue (readInsp h₀ bRefActive) = gb h₀ bRefActive
  have hstep : (mintL h₀ (readInsp h₀ (bRefActive dest h₀))).cT h₀ := hcT h₀ trivial
  rw [mintL_cT, residue_readInsp] at hstep
  -- hstep : gb h₀ bRefActive h₀ = (bRefActive.cT h₀ ∧ (h₀ ≠ h₀ ∨ ¬ bRefActive.cF h₀)); both disjuncts false
  simp only [gb] at hstep
  rcases hstep.2 with h | h
  · exact h rfl
  · exact h trivial

end Series13.WS3
