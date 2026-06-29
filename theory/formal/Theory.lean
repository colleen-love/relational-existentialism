/-
# `theory/` — the stable shared layer (handoff XIII → XXI → XXII)

The canonical axioms + the `T.x` theorems the papers import: the modular reading of A1
(`Theory.ModularFlow`, axiom-supporting), the generative A3 (`Theory.MutualCoupling`), A2-priority
(`Theory.Priority`), the band layer double-imported by paper one and paper two (`Theory.We`,
`Theory.RotatingSpectrum`, `Theory.BandCoincidence`, `Theory.BandFromAxioms`), and the canonical axiomatization
(`Theory.Axioms`). Imports only `theory/` + `foundation/`; references no paper.

**Handoff XXII** returned paper two's capstones to `paper-2/`: the one-generator assembly (`OneGenerator`) and
einselection/presence (`Einselection`) are imported only by paper two, so by the promotion rule they are
`P2.x`, not `T.x`. The canonical axioms' modular reading was re-grounded on `Theory.ModularFlow` alone (the
spectral structure), so `theory/` no longer depends on paper two's assembly.
-/
import Theory.ModularFlow
import Theory.MutualCoupling
import Theory.Priority
import Theory.Axioms
