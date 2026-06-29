/-
# `theory/` — the stable shared layer (handoff XIII → XXI → XXII)

The canonical axioms + the `T0.x` theorems the papers import: the modular reading of A1
(`Theory.ModularFlow`, axiom-supporting), the generative A3 (`Theory.MutualCoupling`), A2-priority
(`Theory.Priority`), the band layer double-imported by paper two and paper three (`Theory.We`,
`Theory.RotatingSpectrum`, `Theory.BandCoincidence`, `Theory.BandFromAxioms`), and the canonical axiomatization
(`Theory.Axioms`). Imports only `theory/` + `foundation/`; references no paper.

**Handoff XXII** returned the modular paper's capstones to its own root (now `paper-3/`): the one-generator
assembly (`OneGenerator`) and einselection/presence (`Einselection`) are imported only by paper three, so by
the promotion rule they are `T3.x`, not `T0.x`. The canonical axioms' modular reading was re-grounded on
`Theory.ModularFlow` alone (the spectral structure), so `theory/` no longer depends on that assembly.
-/
import Theory.ModularFlow
import Theory.MutualCoupling
import Theory.Priority
import Theory.Axioms
