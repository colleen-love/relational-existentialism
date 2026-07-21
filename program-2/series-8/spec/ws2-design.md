# WS2 design — local coherence (the edge) (2.8)

**DEFINE the pairwise RECONCILIATION: the model-derived translation of the value torsor by the directed-attention increment. Prove LOCAL (pairwise) COHERENCE holds across the population — every pair reconciles, the reconciliation a consistent isomorphism (round-trips to the identity), PERVASIVELY and for EVERY attention. This makes the frustration surprising: it is precisely because every pair reconciles that the failure to glue is a genuine many-body phenomenon and not a local disagreement (audit d).**

## 1. Objects (shared, `spec/README.md` §2)

```
def recon (att : S → Finset S) (x y : S) : ℤ → ℤ := fun v => v + incr att x y
```

The reconciliation from `x` to `y` transports a value across their edge by `incr att x y`, the signed directed-attention increment (`P2S3`'s per-edge raising, now read off the model). It is the LOCAL datum Series 2.3 studied as `Converges₂`; the network holonomy (WS3) is what two-selves-coherence cannot see.

## 2. Payoffs

```
-- EVERY PAIR RECONCILES, CONSISTENTLY, PERVASIVELY (WS2). For all attentions, all selves, all values:
theorem ws2_pairwise_coherent (att : S → Finset S) (x y : S) (v : ℤ) :
    recon att y x (recon att x y v) = v

-- THE RECONCILIATION IS NON-VACUOUS (not the identity map on the ring): a genuine transition exists.
theorem ws2_reconciliation_nontrivial :
    recon attTri p0 p1 0 ≠ 0

-- SUPPORTING BRIDGE: the per-edge datum IS Series 2.3's Converges₂ on the valuation ⟨valu att, recon att⟩.
def valPop (att : S → Finset S) : P2S3.Valuation S ℤ := ⟨valu att, fun x y => recon att x y⟩
theorem ws2_bridge_converges (att : S → Finset S) (x y : S) :
    P2S3.Converges₂ (valPop att) x y ↔ valu att x + incr att x y = valu att y   -- Iff.rfl
```

`ws2_pairwise_coherent`: `recon att y x (recon att x y v) = (v + incr att x y) + incr att y x = v + (incr att x y + incr att y x) = v`, since `incr att x y + incr att y x = 0` definitionally (two `if`s cancel; `ring` after `simp only [recon, incr]`). Holds for ALL `att`, `x`, `y`, `v` — coherence is pervasive, not a scarce accident. `ws2_reconciliation_nontrivial`: `recon attTri p0 p1 0 = 0 + incr attTri p0 p1 = 1 ≠ 0` (`decide`). `ws2_bridge_converges`: `Converges₂` unfolds definitionally to `valu att x + incr att x y = valu att y` (`Iff.rfl`).

## 3. Triage

- **Pervasive (audit d).** `ws2_pairwise_coherent` is `∀`-quantified over `att`, `x`, `y`, `v`: local coherence is real across the whole population, so the WS4 frustration is surprising, not vacuous.
- **Local only, forces no global.** The lemma references NO global assignment: it says only that each edge carries a consistent transition (its own inverse on the reverse edge). Whether these transitions admit a simultaneous global section is the WS4 question, invisible here — so WS2 does not smuggle in gluing.
- **Non-vacuous.** `ws2_reconciliation_nontrivial` rules out the degenerate reading where `recon` is always `id`.
- **Model-derived.** `recon` reads off `incr` (a function of `att`); no free parameter.
- **Strip test.** Delete "reconciliation"/"coherence": "translation by the signed increment round-trips to the identity across every edge, and is not the identity on the ring." A bare fact about `incr`.
- **Bridge to 2.3.** `ws2_bridge_converges` exhibits the per-edge datum as exactly `P2S3.Converges₂` — the single-edge coherence Series 2.3 forged, here read off the directed attention. Supporting, not load-bearing on the verdict.
- **Names (audit e).** `recon`, `valPop`, `ws2_*` embed no forbidden content-word.
