# Series 2.8 (The Common Good) — technical summary

**Status: BUILT and reviewed. Verdict FRUSTRATED, computed. The full development is `program-2/series-8/formal/P2S8/` (`ws1`–`ws5`, `P2S8`, `AxiomCheck`); it compiles sorry-free, axiom-clean (standard three), gate-green, names-grep clean. Imports `P2S7` only; `P2S6 / … / P2S0 / P1` transitive.**

## 1. What is built

The value space is the torsor `ℤ`. The population is `S := Fin 3` (`p0` the self, `p1`/`p2` two lateral peers), carried by two directed attentions: the directed 3-ring `attTri` (`p0→p1→p2→p0`) and the mutual star `attStar` (`p0↔p1`, `p0↔p2`). One model quantity underlies everything:

```
incr att x y : ℤ := (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)
```

the signed directed-attention increment — a function of the attention `att` alone (`= P2S0.knows`). From it:

- **The good** `valu att := incr att p0 ·` (WS1): the self-relative valuation, read from the self `p0`'s frame.
- **The reconciliation** `recon att x y v := v + incr att x y` (WS2): the model-derived translation of the torsor.
- **The holonomy** `hol att x y z := incr att x y + incr att y z + incr att z x` (WS3/WS4): the net translation of the composed reconciliation around a triangle.
- **A global section** `IsSection att s := ∀ x y, y ∈ att x → s y = s x + incr att x y` (WS4): a global good.

## 2. The theorems

| Theorem | Content |
|---|---|
| `ws1_nontrivial` | `valu attTri p1 ≠ valu attTri p2` (non-constant) ∧ `incr attTri p0 p2 ≠ incr attTri p1 p2` (perspectival: `p2` valued `-1` from `p0`, `+1` from `p1`) |
| `ws2_pairwise_coherent` | `∀ att x y v, recon att y x (recon att x y v) = v` — the reconciliation round-trips to `id` on every edge, pervasively (antisymmetry of `incr` is definitional) |
| `ws2_reconciliation_nontrivial` | `recon attTri p0 p1 0 ≠ 0` — a genuine (non-identity) transition |
| `ws2_bridge_converges` | `P2S3.Converges₂ (valPop att) x y ↔ valu att x + incr att x y = valu att y` — the edge datum IS Series 2.3's `Converges₂` (`Iff.rfl`) |
| `ws3_two_body_trivial` | `∀ att x y, incr att x y + incr att y x = 0 ∧ hol att x y x = 0 ∧ hol att x x y = 0` — the holonomy vanishes for two selves |
| `ws3_holonomy_model_derived` | `incr` is the signed `knows` difference; symmetric `att` ⇒ `hol ≡ 0`; `attTri` is genuinely directed |
| `ws4_frustrated_reachable` | `hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s, IsSection attTri s` — the ring frustrates: no global good |
| `ws4_gluable_reachable` | `hol attStar p0 p1 p2 = 0 ∧ ∃ s, IsSection attStar s ∧ s p0 = valu attStar p0` — the star glues |
| `ws5_verdict_eq` | `verdict true true true true true true = Outcome.frustrated` (`rfl`) |
| `ws5_verdict_discriminates` | the six-input verdict reaches all six outcomes |
| `ws5_flags_justified` | the six deciding flags are the WS1–WS4 facts |
| `ws5_audit_no_global` / `_fork_genuine` / `_many_body` / `_coherence_pervasive` / `_names_not_terms` | audit (a)–(e) |

## 3. The mathematics

The construction is the discrete flat-connection / group-cohomology H¹ obstruction, realised on the directed attention. The 1-cochain `incr ∈ C¹(graph, ℤ)` is antisymmetric by construction (`incr x y + incr y x = 0`, two indicator terms cancel), so it is a well-defined edge datum and every reconciliation `recon x y = (+ incr x y)` is a consistent isomorphism with inverse the reverse edge — pairwise coherence, pervasive and unconditional (WS2, audit d).

A global section (global good) is an `s : S → ℤ` with `s y - s x = incr att x y` on every edge — i.e. `incr` is a coboundary `s`. Around a cycle this forces the holonomy `hol = 0`. So **a global good exists iff the holonomy vanishes.** The holonomy is genuinely many-body: for any two selves it is `incr x y + incr y x = 0` (WS3, audit c — not Series 2.3's single edge), and it is carried entirely by the DIRECTEDNESS — symmetrise `att` and every `incr` is `0`, so `hol ≡ 0` (WS3, the model-derived certificate; a bolted-on gadget would be indifferent to `att`'s symmetry — the 2.7 T1-S1 trap foreclosed).

The fork is reached on two carriers built from the same `incr`/`hol`:
- **`attTri`** (the directed ring): `incr = +1` on each of `p0→p1`, `p1→p2`, `p2→p0`, so `hol = 3 ≠ 0`. Any section would force `s p0 = s p0 + 3`, i.e. `0 = 3` — no global good. **FRUSTRATED.**
- **`attStar`** (the mutual star): every present edge is mutual or absent, so every `incr = 0`, `hol = 0`, and the constant `s = 0` is a section restricting to `valu attStar p0 = 0`. **GLUABLE.**

Neither side is a fiat: `hol` does not branch on the carrier; frustration and gluing are facts about which directed attention is present. The verdict computes `frustrated` because BOTH sides are reachable — local coherence is compatible with non-gluing, so it does not FORCE a global good.

## 4. The costume gate, doubled, and the T1-S1 lesson

- **Not a single edge (Series 2.3).** The obstruction vanishes for two selves (`ws3_two_body_trivial`); it is alive only for the 3-cycle.
- **Not import-ness (Series 07).** No definition, statement, or proof mentions `Recoverable` / `plainOf` / `AttentionDistinguishes`. The engine is the directed-cycle sum, not `¬ Recoverable`.
- **Model-derived, not bolted on (the 2.7 T1-S1 lesson).** `incr` reads only `∈ att`; the good, the reconciliation, and the holonomy all read off the SAME `incr`. Symmetrising `att` kills the holonomy identically — the obstruction lives in the built directed attention, not in a `Finset.card`/`insert` counter or a free permutation beside it.

## 5. Axioms and closure

`AxiomCheck.lean` records, per payoff, dependence only on `propext` / `Classical.choice` / `Quot.sound` (several fewer; the verdict theorems on none). `scripts/gate.sh` confirms the imports resolve to `P2S7` / `P2S8.*` / Mathlib only. The names-not-terms grep over `formal/` is clean: no proof term is named `good` / `common` / `value` / `justice` / `consensus` / `ethics` / `self` / `import` / `god` / `love` / `compass`; the good's definition is `valu`.

## 6. Verdict

**FRUSTRATED.** A non-trivial, self-relative, perspectival good (WS1); local pairwise coherence real and pervasive (WS2); the obstruction a genuine many-body cocycle, model-derived, neither a single edge nor import-ness (WS3); and both a frustrated world (no global good) and a gluable world reachable, neither by fiat (WS4). The verdict is computed, not hand-set (WS5). Local coherence does not force a global good — the value analog of Series 2.7's global failure. The pre-registered GLUABLE, SHAPE-DRAWN, PAIRWISE-ONLY, and DISCONNECTED were not reached; each was live in the verdict function and foreclosed by proof, not by construction.
