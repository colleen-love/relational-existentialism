# Series 2.8 design index (`spec/README.md`) — THE COMMON GOOD

**The design layer for the value capstone. Read `frustration-derisking.md` first (the paper gate: a non-trivial self-relative good AND a model-derived frustration, both survived). This README fixes the shared objects, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All six files plus the de-risking are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported chain (quantified, never named as content)

Series 2.8 imports `P2S7` only; `P2S6 / … / P2S0 / P1` are reached transitively. Working material:

- **The directed attention** `P2S0.attends : X → Finset X`, `P2S0.knows att x y := y ∈ att x`, `P2S0.outDest` — the finite out-attention, the sole ontological bound, and the DIRECTEDNESS (the knowing-asymmetry) that is the engine of the holonomy.
- **The world** — the lateral population of same-rank peers and the directed ring (`P2S4.attendsW`, `P2S4.reachIn`), re-seated as the population of three or more selves.
- **The single-edge coherence datum** `P2S3.Valuation`, `P2S3.Converges₂`, `P2S3.Faithful₂` — used LOCALLY (per edge) and exceeded at the network (`ws2_bridge_converges`).
- The recoverability/import test and P1 diagonal (`P1.Core`, `P1.Reader`) — reached transitively; used to say what the obstruction is NOT (import-ness).

## 2. The shared objects (built FRESH at S8, model-derived; `formal/P2S8/ws1..ws5`)

The value space is the torsor `ℤ` (values compared by differences; no canonical origin — no view from nowhere). The population is a fresh `Fin 3` carrier seated as the world triangle; two directed attentions carry the fork.

```
abbrev S : Type := Fin 3            -- the population of three selves (peers)
def p0 : S := 0  ; def p1 : S := 1 ; def p2 : S := 2      -- the self and its two lateral peers

def attTri  : S → Finset S          -- the directed 3-ring  p0→p1→p2→p0   (the FRUSTRATED carrier)
def attStar : S → Finset S          -- the mutual star  p0↔p1, p0↔p2       (the GLUABLE carrier)

def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y   -- the imported directed knowing

-- THE ONE MODEL QUANTITY: the signed directed-attention increment, read off `knows` and nothing else.
def incr (att : S → Finset S) (x y : S) : ℤ :=
  (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)

-- THE RECONCILIATION: the model-derived translation of the value torsor (WS2).
def recon (att : S → Finset S) (x y : S) : ℤ → ℤ := fun v => v + incr att x y

-- THE GOOD: the self-relative valuation, read from the self p0's directed attention (WS1).
-- Named `valu` in code (`good` is a forbidden content-name for identifiers, audit e); "good" in prose.
def valu (att : S → Finset S) : S → ℤ := fun y => incr att p0 y

-- THE HOLONOMY: the net translation of the composed reconciliation around a triangle (WS3/WS4).
def hol (att : S → Finset S) (x y z : S) : ℤ := incr att x y + incr att y z + incr att z x

-- A GLOBAL SECTION (a global good): an assignment consistent with every attention edge (WS4).
def IsSection (att : S → Finset S) (s : S → ℤ) : Prop := ∀ x y, y ∈ att x → s y = s x + incr att x y
```

Everything downstream is a ℤ-arithmetic fact on a finite carrier: `decide` / `omega`-checkable.

## 3. The discipline (the doubled costume gate + the T1-S1 lesson, first-class)

- **No global good asserted (audit a, the phase sin).** No proof term asserts a globally forced good. The good is FOR a self (`valu = incr p0 ·`); a global section is claimed only where the holonomy vanishes. A `gluable` verdict is returned only if gluing is FORCED (frustration not reachable) — and here it is not, so the honest close is FRUSTRATED.
- **Genuine many-body cocycle, not a single edge, not import-ness (audit c, doubled gate).** The obstruction is `hol`, the δ-sum around a 3-cycle: it VANISHES for two selves (`incr x y + incr y x = 0`, definitional) and is alive for three (the ring's `3`). It never mentions `Recoverable`; it is a network/axis engine, not import-ness.
- **Model-derived, not bolted on (audit c/d, the T1-S1 lesson).** `incr` is a function of `att` alone (the signed `knows` difference); `valu`, `recon`, `hol` all read off the SAME `incr`. Kill the directedness (make `att` symmetric) and ALL holonomy vanishes (`ws3_holonomy_model_derived`) — the obstruction lives in the built directed attention, not in a gadget beside it. No `Finset.card`/`insert` counter, no free permutation.
- **The good non-trivial and self-relative, the fork not by fiat (audit b).** `valu` is non-constant and perspectival (two selves value a target oppositely — no symmetric metric can). Frustration is not built into `hol` (the star gives `0`); gluing is not built in (the ring gives `3`); the verdict discriminates.
- **PAIRWISE-ONLY and DISCONNECTED honorable.** If the good were trivial → DISCONNECTED; if the obstruction degenerated to a single edge → PAIRWISE-ONLY. Neither materialises (§ de-risking), but both are pre-registered and reachable in the verdict function.

## 4. Cross-workstream triage

| WS | Object | Headline(s) | Costume foreclosed |
|----|--------|-------------|--------------------|
| WS1 | `valu` | `ws1_nontrivial` | not a metric relabel; perspectival, self-relative |
| WS2 | `recon` | `ws2_pairwise_coherent`, `ws2_reconciliation_nontrivial`, `ws2_bridge_converges` | pervasive & non-vacuous, not a scarce accident |
| WS3 | `hol` | `ws3_two_body_trivial`, `ws3_holonomy_model_derived` | not a single edge (2-body trivial); not bolted on (symmetry kills it); not import-ness |
| WS4 | `IsSection` | `ws4_frustrated_reachable`, `ws4_gluable_reachable` | both sides genuine, no fiat |
| WS5 | `verdict` | `ws5_verdict_eq (= frustrated)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)-(e) | computed, not hand-set |

## 5. The outcomes (WS5)

`frustrated` (both fork sides reachable → local coherence does not FORCE a global good — the expected close, the value analog of 2.7's global failure), `gluable` (a global good forced — frustration not reachable, the surprise), `shapeDrawn` (neither side decided in-sight), `pairwiseOnly` (the obstruction degenerates to a single edge), `disconnected` (no non-trivial good), `partial'` (degenerate; `partial` is a Lean keyword).

## 6. Names-in-prose rule (audit e)

The concept-words — good, common, value, justice, consensus, ethics, self, import, God, love, compass — appear only in docstring prose. Every proof term, definition, and discharged obligation carries a NEUTRAL name (`incr`, `recon`, `valu`, `hol`, `IsSection`, `verdict`, `Outcome`, `ws*`). In particular the good's definition is named **`valu`**, not `good` (`good` and `value` are forbidden as identifiers; `valu` is not the whole word `value`). No headline embeds a forbidden content-word as a whole word. The §6 grep runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt (they are not proof-term names).
