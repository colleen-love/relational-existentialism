# theory — fork provenance

`theory/` is the living, theory-specific frontier. It imports only `theory/` + `foundation/` (closure gate),
references no paper, and is the only root that moves freely.

- **New here (no fork):** `Theory.ModularFlow` (modular A1), `Theory.MutualCoupling` (generative A3),
  `Theory.Priority` (A2-priority / no-bare-carrier), `Theory.OneGenerator` (handoff XV — the open-system
  capstone: assembles the GKLS generator `𝓛 = -i[(1/β)K,·] + 𝒟` from the modular `K` (state) and paper one's
  dissipator `𝒟` (arrow), and proves they are **one generator at equilibrium** via the KMS bridge and the
  preferred-basis Schur-commutation; consumes `Theory.ModularFlow` and `Theory.RotatingSpectrum`),
  `Theory.Einselection` (handoff XVI — *derives* spec XV's basis alignment from stationarity
  `𝒟(ρ) = 0` ("the clock-state is the rest-state"), identifies the einselected conserved band `Peri = fixed ⊕
  rotating`, and defines **presence** as its HS weight: conserved and Pythagorean-split into knowing ⊕ energy,
  but with the arrow shown to be *loss, not relocation* — a precisely-located negative for paper three;
  consumes `Theory.OneGenerator` and `Theory.BandFromAxioms`). These are already *not* paper one.
- **Forked from `paper-1/` on demand at `fe935a6`** (genuine second consumer = the frontier modules above):
  `Theory.We` (for `Priority`), and `Theory.{RotatingSpectrum,BandCoincidence,BandFromAxioms}` (for
  `MutualCoupling`). Frozen copies of paper-1's `Scratch.{We,RotatingSpectrum,BandCoincidence,BandFromAxioms}`,
  byte-identical at the fork hash except their import lines (re-pointed to `Theory.*`). **Intended identical**
  to paper-1's copies until a `theory` axiom reading deliberately diverges them.
- **Imported (not forked):** `foundation/` (`Foundation.Traced`).

**Lazy-hoist rule:** the canonical home of a shared module is wherever it currently lives; hoisting to
`theory/` happens *per-lemma, at first second-consumer*, not eagerly. The other ~14 paper-one modules have
no `theory` consumer and remain paper-1-only — not duplicated here.
