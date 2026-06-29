/-
# `paper-3/` — the modular self-relation paper

Paper three **imports** the shared `T0.x` it uses from the stable `theory/` and proves its **own** `T3.x`:

- **Imported (`T0.x`, from `theory/`):** `Theory.ModularFlow` (the modular reading of A1) and the band layer
  `Theory.{RotatingSpectrum, BandCoincidence, BandFromAxioms}` (genuinely double-imported with paper two).
- **Its own (`T3.x`):** `Paper3.OneGenerator` = **T3.01** (the equilibrium one-generator capstone,
  `combinedFlow_add`) and `Paper3.Einselection` = **T3.02** (einselection + presence — paper three's headline:
  `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`). These are paper-three-only nodes: only
  paper three imports them, so by the promotion rule (`T0.x` iff ≥2 papers import) they stay `T3.x`. They
  import the band/`ModularFlow` from `theory/`.

Paper two's seam→arrow result is a **prose citation** in the manuscript, never imported. The pinned `theory/`
commit is recorded in [`../spec/04-provenance.md`](../spec/04-provenance.md).
-/
import Theory.ModularFlow
import Theory.RotatingSpectrum
import Theory.BandCoincidence
import Theory.BandFromAxioms
import Paper3.OneGenerator
import Paper3.Einselection
