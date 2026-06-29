/-
# `paper-2/` — the modular self-relation paper (thin layer, handoff XXI)

Paper two is now a **thin version-pinned layer**: it **imports** the modular slice from the stable
`theory/` (clean `Theory.*` names) rather than forking it. The proof-DAG reorg (handoff XXI) un-forked the
six byte-identical `Paper2.*` copies — they were confirmed identical to `theory/`'s, so unifying them shifts
no meaning — and paper two reads off the canonical `T.x` nodes:

`Theory.{ModularFlow, RotatingSpectrum, BandCoincidence, BandFromAxioms, OneGenerator, Einselection}` — the
modular reading of A1, the conserved band, the equilibrium one generator, and the einselection principle +
presence. Paper two's headline theorems (`presence_conserved`, `pythagorean`,
`arrow_is_loss_not_relocation`, `combinedFlow_add`, `stationary_eq_diagonal_real`) now live at their
canonical `Theory.*` addresses; the manuscript cites them there.

Paper one's seam→arrow result is **cited in prose** in the manuscript, never imported. The pinned `theory/`
commit is recorded in [`../spec/AXIOM-PROVENANCE.md`](../spec/AXIOM-PROVENANCE.md).
-/
import Theory.ModularFlow
import Theory.RotatingSpectrum
import Theory.BandCoincidence
import Theory.BandFromAxioms
import Theory.OneGenerator
import Theory.Einselection
