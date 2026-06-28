-- Relational Existentialism — formal core (dependency-free root module).
--
-- This core is deliberately mathlib-free: it builds and checks in seconds. It carries the
-- order-theoretic / categorical spine of paper one's headline (see docs/spec/paper-one.md):
--
--   * RelExist.Mirror     — 3.3 (σ-side): Lawvere's theorem, the mirror that can't close.
--   * RelExist.Relating   — the relational typology; the self-inclusive block is unmodelable.
--   * RelExist.Seam       — the seam: a self cannot completely trace what includes it (0 ax).
--   * RelExist.SeamBridge — the bridge tying the seam to the decohering remainder.
--   * RelExist.Traced     — the traced symmetric monoidal category typeclass (A1's arena).
--
-- The rest of the former core (Sparsity/Loop — paper three; Fox/Reflexive*/Firewall/Free/
-- Coherence/FreeCoherent — the functorial-semantics and free-Cl(𝕋) scaffolding) has been moved
-- to Archive/RelExist/ (quarantined, not built). The keep set is the computed import closure of
-- paper one's anchors, not a hand-picked list.
import RelExist.Mirror
import RelExist.Relating
import RelExist.Seam
import RelExist.SeamBridge
import Foundation.Traced
