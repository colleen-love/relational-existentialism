/-
# `paper-2/` — the modular self-relation paper (handoff XXII)

Paper two **imports** the shared `T.x` it uses from the stable `theory/` and proves its **own** `P2.x`:

- **Imported (`T.x`, from `theory/`):** `Theory.ModularFlow` (the modular reading of A1) and the band layer
  `Theory.{RotatingSpectrum, BandCoincidence, BandFromAxioms}` (genuinely double-imported with paper one).
- **Its own (`P2.x`):** `Paper2.OneGenerator` = **P2.1** (the equilibrium one-generator capstone,
  `combinedFlow_add`) and `Paper2.Einselection` = **P2.2** (einselection + presence — paper two's headline:
  `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`). Handoff XXII returned these from
  `theory/` to paper two: only paper two imports them, so by the promotion rule (`T.x` iff ≥2 papers import)
  they are `P2.x`. They import the band/`ModularFlow` from `theory/`.

Paper one's seam→arrow result is a **prose citation** in the manuscript, never imported. The pinned `theory/`
commit is recorded in [`../spec/AXIOM-PROVENANCE.md`](../spec/AXIOM-PROVENANCE.md).
-/
import Theory.ModularFlow
import Theory.RotatingSpectrum
import Theory.BandCoincidence
import Theory.BandFromAxioms
import Paper2.OneGenerator
import Paper2.Einselection
