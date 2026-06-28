/-
# `Rel` is a *coherent* traced SMC — the coherence layer, validated non-trivially

`Scratch/Rel.lean` makes `Rel` (sets & relations) a `TracedSMC`. Here we promote it to a
`CoherentTracedSMC`: the eight symmetric-monoidal coherence laws (associator/unitor
naturality, pentagon, triangle, braiding naturality, symmetry, hexagon) all hold, each by the
same `simp`+`aesop` discharge as the JSV axioms. So the coherence refinement is validated in a
genuine **multi-object** model, not only the one-object scalar one.
-/
import Aesop
import RelExist.Coherence
import Scratch.Rel

namespace RelExist.RelModel

open RelExist.Traced

set_option maxRecDepth 8000 in
/-- **`Rel` is a coherent traced symmetric monoidal category** — the full coherence layer,
validated in a genuine multi-object model. -/
def relCoherentTracedSMC : CoherentTracedSMC.{u+1, u} :=
  { toTracedSMC := relTracedSMC
    assoc_nat := by
      intro X X' Y Y' Z Z' f g h; funext p q
      simp only [relTracedSMC, rcomp, rtensH, raHom, rid]; aesop
    lu_nat := by
      intro X Y f; funext p q
      simp only [relTracedSMC, rcomp, rtensH, rluHom, rid]; aesop
    ru_nat := by
      intro X Y f; funext p q
      simp only [relTracedSMC, rcomp, rtensH, rruHom, rid]; aesop
    pentagon := by
      intro W X Y Z; funext p q
      obtain ⟨⟨⟨pw, px⟩, py⟩, pz⟩ := p
      obtain ⟨qw, qx, qy, qz⟩ := q
      simp only [relTracedSMC, rcomp, rtensH, raHom, rid]
      aesop (config := { maxRuleApplications := 4000 })
    triangle := by
      intro X Y; funext p q
      simp only [relTracedSMC, rcomp, rtensH, raHom, rluHom, rruHom, rid]; aesop
    braid_nat := by
      intro X X' Y Y' f g; funext p q
      simp only [relTracedSMC, rcomp, rtensH, rbraid, rid]; aesop
    braid_symm := by
      intro X Y; funext p q
      simp only [relTracedSMC, rcomp, rbraid, rid]; aesop
    hexagon := by
      intro X Y Z; funext p q
      obtain ⟨⟨px, py⟩, pz⟩ := p
      obtain ⟨qy, qz, qx⟩ := q
      simp only [relTracedSMC, rcomp, rtensH, raHom, rbraid, rid]
      aesop (config := { maxRuleApplications := 4000 }) }

end RelExist.RelModel
