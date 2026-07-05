/-
Spec 2.4f — Lambek by hand for the corrected functor (2-4-mechanization-c Stage 0, Route A).

Normative source: `series-2/2-4.md` §2 and `2-4-mechanization-c.md` Stage 0 Route A. Continues
`Spec24e.lean`. Specs win. No declaration consults §8.

Route A: the structure map `dest : Ω_R → HC Ω_R` is an isomorphism (Lambek). Built by hand —
`mkC := Cofix.corec (HC.map dest)` — because univariate `QPF.Cofix` provides no `mk`. This retires
the "Lambek in both sorts" claim of 2.4 §2's construction paragraph. FP-C2: the univariate bisim
closes `mkC_dest` without new axioms beyond the file's existing profile.
-/
import Spec24e

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-- `HC` respects composition — the second functor law (companion to `HC_map_id`). -/
theorem HC_map_comp {α β γ : Type} (f : α → β) (g : β → γ) (z : HC α) :
    HC.map g (HC.map f z) = HC.map (g ∘ f) z := by
  show Sym2.map _ (Sym2.map _ z) = Sym2.map _ z
  rw [Sym2.map_map]
  congr 1
  funext w
  rcases w with S | x
  · show Sum.inl _ = Sum.inl _
    congr 1
    apply Subtype.ext
    exact Set.image_image g f S.1
  · rfl

/-- `mkC` — the inverse-to-be of `dest`, built by corecursion (`Cofix.corec (HC.map dest)`), the
Lambek `mk` univariate `QPF.Cofix` does not ship. -/
noncomputable def mkC (x : HC ΩR) : ΩR :=
  QPF.Cofix.corec (HC.map (QPF.Cofix.dest (F := HC))) x

/-- The one-step unfolding of `mkC` (isolating the `corec`): `dest (mkC y) = mkC <$> (dest <$> y)`.
Used by both inverse laws. -/
theorem dest_mkC_eq (y : HC ΩR) :
    QPF.Cofix.dest (mkC y) = mkC <$> (QPF.Cofix.dest (F := HC) <$> y) := by
  show QPF.Cofix.dest (QPF.Cofix.corec (HC.map (QPF.Cofix.dest (F := HC))) y) = _
  rw [QPF.Cofix.dest_corec]
  rfl

/-- FP-C2 — `mkC` is a LEFT inverse of `dest`: `mkC (dest t) = t`. The coinductive core, via the
univariate bisimulation principle. Closes without new axioms — the mathlib gap was only the missing
`mk`, not a deeper obstruction. -/
theorem mkC_dest (t : ΩR) : mkC (QPF.Cofix.dest t) = t := by
  refine QPF.Cofix.bisim (fun a b => a = mkC (QPF.Cofix.dest b)) ?_ _ t rfl
  rintro a b rfl
  rw [QPF.liftr_iff]
  have habs : QPF.abs (QPF.repr (QPF.Cofix.dest b)) = QPF.Cofix.dest b := QPF.abs_repr _
  refine ⟨(QPF.repr (QPF.Cofix.dest b)).1,
          fun i => mkC (QPF.Cofix.dest ((QPF.repr (QPF.Cofix.dest b)).2 i)),
          (QPF.repr (QPF.Cofix.dest b)).2, ?_, ?_, fun _ => rfl⟩
  · -- dest (mkC (dest b)) = abs ⟨shape, mkC ∘ dest ∘ g⟩
    rw [dest_mkC_eq]
    have e1 : QPF.Cofix.dest (F := HC) <$> QPF.Cofix.dest b
        = QPF.abs (QPF.Cofix.dest (F := HC) <$> QPF.repr (QPF.Cofix.dest b)) := by
      conv_lhs => rw [← habs]
      exact (QPF.abs_map (F := HC) _ _).symm
    rw [e1,
      show mkC <$> QPF.abs (QPF.Cofix.dest (F := HC) <$> QPF.repr (QPF.Cofix.dest b))
        = QPF.abs (mkC <$> (QPF.Cofix.dest (F := HC) <$> QPF.repr (QPF.Cofix.dest b)))
        from (QPF.abs_map (F := HC) _ _).symm]
    rfl
  · -- dest b = abs ⟨shape, g⟩
    exact habs.symm

/-- `mkC` is a RIGHT inverse of `dest`: `dest (mkC x) = x`. Derived from `mkC_dest` via
`dest_mkC_eq` and functor composition (`HC_map_comp`, `HC_map_id`). -/
theorem dest_mkC (x : HC ΩR) : QPF.Cofix.dest (mkC x) = x := by
  rw [dest_mkC_eq]
  show HC.map mkC (HC.map (QPF.Cofix.dest (F := HC)) x) = x
  rw [HC_map_comp]
  have hcomp : mkC ∘ QPF.Cofix.dest (F := HC) = id := funext mkC_dest
  rw [hcomp, HC_map_id, id_eq]

/-- Lambek, mechanized for the corrected functor: `dest : Ω_R ≃ HC Ω_R = Sym2(Ω_O ⊕ Ω_R)` is the
structure isomorphism (2.4 §2). Retires the "Lambek in both sorts" claim of the construction
paragraph — the object-sort iso `Ω_O = P⁺f(Ω_R)` is definitional (`ΩO := PfNe ΩR`); this is the
relation-sort iso, the one that needed proof. -/
noncomputable def destEquivC : ΩR ≃ HC ΩR where
  toFun := QPF.Cofix.dest (F := HC)
  invFun := mkC
  left_inv := mkC_dest
  right_inv := dest_mkC

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms mkC_dest
#print axioms dest_mkC
#print axioms destEquivC
end AxiomAudit
