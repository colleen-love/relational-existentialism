/-
`program-2/series-8/formal/P2S8/ws2.lean`

WS2 - Local coherence (the edge). Program 2 Series 8 (2.8).

The reconciliation `recon` (defined in `ws1`) is the model-derived translation of the value torsor by the directed
increment `incr`. WS2 proves LOCAL (pairwise) COHERENCE PERVASIVE (`ws2_pairwise_coherent`): for EVERY attention and
EVERY pair the reconciliation is a consistent isomorphism (composed with the reverse edge it is the identity),
because `incr` is antisymmetric definitionally. It is NON-VACUOUS (`ws2_reconciliation_nontrivial`: the ring
reconciliation is not the identity). A bridge (`ws2_bridge_converges`) exhibits the per-edge datum as exactly Series
2.3's `Converges₂` on the valuation `⟨valu att, recon att⟩` — the local coherence Series 2.3 studied on a single
edge, here pervasive across the network and exceeded by the holonomy (WS3/WS4).

Design docs: `program-2/series-8/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8.ws1

universe u

namespace P2S8

set_option linter.unusedVariables false

/-! ## Pairwise coherence, pervasive -/

/-- **EVERY PAIR RECONCILES, CONSISTENTLY, PERVASIVELY (WS2).** For all attentions, all selves, all values, the
reconciliation composed with the reverse edge is the identity: `incr` is antisymmetric (the two indicator terms
cancel), so `recon (y,x) ∘ recon (x,y) = id`. Local coherence is real across the whole population, not a scarce
accident (audit d). -/
theorem ws2_pairwise_coherent (att : S → Finset S) (x y : S) (v : ℤ) :
    recon att y x (recon att x y v) = v := by
  simp only [recon, incr]; ring

/-- **THE RECONCILIATION IS NON-VACUOUS.** On the ring, `recon p0 p1` is not the identity map (it shifts `0` to
`1`): a genuine transition, so coherence is not the trivial `recon = id`. -/
theorem ws2_reconciliation_nontrivial : recon attTri p0 p1 0 ≠ 0 := by decide

/-! ## Bridge to Series 2.3's single-edge coherence datum (the transitive API, used locally) -/

/-- The per-self valuation packaged as a Series 2.3 `Valuation`: the good `valu att` with the reconciliation
`recon att` as its raising. The object Series 2.3 studied on a single edge. -/
def valPop (att : S → Finset S) : P2S3.Valuation S ℤ := ⟨valu att, fun x y => recon att x y⟩

/-- **THE EDGE DATUM IS SERIES 2.3'S `Converges₂` (the local coherence, per edge).** `Converges₂ (valPop att) x y`
holds iff the good at `x`, reconciled toward `y`, agrees with the good at `y` — the single-edge coherence Series 2.3
forged, here read off the directed attention and pervasive across the network. -/
theorem ws2_bridge_converges (att : S → Finset S) (x y : S) :
    P2S3.Converges₂ (valPop att) x y ↔ valu att x + incr att x y = valu att y := Iff.rfl

end P2S8
