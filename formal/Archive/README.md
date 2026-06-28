# Archive — quarantined development (not built)

These Lean modules were part of the development but are **not** in the transitive import-closure of
**paper one**'s headline theorems (see [`../../docs/spec/paper-one.md`](../../docs/spec/paper-one.md)).
Per the reorganization rule — *keep the import-closure of the headline; archive the complement* — they
were moved here mechanically, by the import graph, not by hand.

They are **quarantined**: the active libraries (`RelExist`, `Scratch`) no longer import them, so
`lake build` does not compile them. They are **kept, not deleted** — each is the seed of a later paper.
(Module paths under `Archive/` no longer match a library root, and some internal `import` lines now
dangle; reviving a module means moving it back and restoring its imports.)

Organized by the paper they belong to:

- **Paper two — cosmos & the conservation law.** `Scratch/Genesis`, `Scratch/CosmicTime`,
  `Scratch/DistributedSelf`, `Scratch/WeaveGfp`, `Scratch/Learning`, `Scratch/Conservation`,
  `Scratch/Forgetting`, `Scratch/SeamPermanence`, and the two-term / `undifferentiated` framing that
  `Scratch/BandCoincidence` proves but paper one does not headline.
- **Paper three — sparsity.** `RelExist/Sparsity`, `RelExist/Loop`, `Scratch/Sparsity*`,
  `Scratch/Convergence`, `Scratch/Stabilization`, `Scratch/SpectralMultiplicity`,
  `Scratch/SpectralDecay`, `Scratch/PerronFrobenius`, `Scratch/Peripheral*`.
- **Functorial semantics (Layer 4).** `RelExist/Firewall`, `RelExist/Free`, `RelExist/Coherence`,
  `RelExist/FreeCoherent`, `Scratch/Biology`, `Scratch/Chemistry`, `Scratch/Classical`,
  `Scratch/Domain*`, `Scratch/Int*`, `Scratch/Rel*`, `Scratch/MatrixCoherence`, `Scratch/Feedback`.
- **Route-1 reflexive-object / GoI scaffolding** (03.5 already marks route 1 not load-bearing).
  `RelExist/ReflexiveSeam`, `RelExist/ReflexiveModel`, `Scratch/GraphModel`, `Scratch/SelfApplication`,
  `Scratch/Compact`, `Scratch/ConwayTrace`, `Scratch/ReflexiveCompact`.
- **Other branches not in the headline closure.** `RelExist/Fox`, `Scratch/Attention`,
  `Scratch/Identity`, `Scratch/Knowing`, `Scratch/Marginal`, `Scratch/Distribution`,
  `Scratch/RelationalAppearance`, `Scratch/RelationalMarginal`, `Scratch/Registration`,
  `Scratch/Causation`, `Scratch/Feeling`, `Scratch/NoCloning`, `Scratch/Recurrence`,
  `Scratch/MeanErgodic` (Conjecture R, the general arrow⇒knowing converse — an open frontier),
  `Scratch/Space` (the metric half), `Scratch/TimeArrow`, `Scratch/SeamComonoid`,
  `Scratch/QuantumSeamTrace`, `Scratch/ValuationBoundary`, `Scratch/FoxTheorem`.

A notable finding of the reorg: **`Scratch/Attention.lean`** (the gfp formalization of A3's self,
`sustainedField = νΦ`) is *not* in the headline closure. Paper one's headline takes A1–A3 as the
abstract baseline hypotheses of `Scratch/BandFromAxioms` (`Contractive`, nondegeneracy), not via the
gfp model — so the gfp self belongs to the cosmos development, not the headline chain.
