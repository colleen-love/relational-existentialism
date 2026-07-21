# Series 2.9 design index (`spec/README.md`) — THE CONE

**The design layer for the first recovery test of Phase 3 (one of two tier-1 probes). Read `rate-derisking.md` first (the paper gate: a finite rate earned from attention, a non-trivial cone, the rate genuine content not the bare order — all survived). This README fixes the shared objects, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All six files plus the de-risking are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported chain (quantified, never named as content)

Series 2.9 imports `P2S8` only; `P2S7 / … / P2S0 / P1` are reached transitively. Working material:

- **The finite attention** `P2S0.attends : X → Finset X`, `P2S0.knows att x y := y ∈ att x`, proved strictly finite (`P2S0.ws1_bound_is_finite_attention`). The finite `Finset` IS the attention budget; the rate is read off it.
- **The tick and its depth** — `P2S1.reifyT` (a finite pattern reified to one relatum: breadth → depth), `P2S1.causal` / `rankT` (one tick = one unit of depth).
- **The lateral metric and the two DISTINCT axes** — `P2S4.stepsFrom` / `P2S4.latW` (breadth as lateral distance), `P2S4.rankW` (depth), DISTINCT (`P2S4.ws2_axes_independent`); `P2S4.reachIn` the length-indexed reach.
- **The causal order** — `P2S5.causalDep` and its transitive closure — the order this series rate-limits and exceeds.

## 2. The shared objects (built FRESH at S9, model-derived off the attention; `formal/P2S9/ws1..ws5`)

The carrier is a fresh `Fin 5` LINE seated as the lateral world; a fixed lateral metric carries breadth; the rate is a `Finset.sup` over the attention; the cone is the rate-bounded ball; three attentions carry the fork.

```
abbrev S : Type := Fin 5                              -- a lateral line of five peers (2.4's world, re-seated)
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2 ; def p3 : S := 3 ; def p4 : S := 4

def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y   -- the imported directed knowing

-- THE LATERAL METRIC (2.4's breadth-distance, re-seated): a fixed spatial background, attention-independent.
def dist (x y : S) : ℕ := Nat.dist x.val y.val

-- THE PER-TICK REACH: the greatest lateral distance to an attended relatum, read off `att` (breadth per tick).
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)

-- THE RATE c: the carrier's maximal per-tick reach, a function of the finite attention alone (EARNED, not postulated).
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)

-- THE CONE: the events within rate×depth of the source in the lateral metric. Named `ball` (audit e); "cone" in prose.
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)

-- THE CAUSAL ORDER (2.5, re-seated): decidable bounded reachability, the order the cone must exceed.
def reachWithin (att : S → Finset S) : ℕ → S → S → Bool
  | 0,     x, y => x == y
  | (n+1), x, y => (x == y) || (att x).any (fun z => reachWithin att n z y)
def reaches (att : S → Finset S) (x y : S) : Bool := reachWithin att (Fintype.card S) x y

def attSlow : S → Finset S           -- forward neighbor  (rate 1)  — the CONE carrier
def attFast : S → Finset S           -- forward two       (rate 2)  — the costume pair (SAME order as attSlow)
def attAll  : S → Finset S           -- attend everyone   (rate 4)  — the NO-CONE carrier (instantaneous)
```

Everything downstream is a ℕ / Finset arithmetic fact on a finite carrier: `decide` / `omega` / `Finset.le_sup`-checkable.

## 3. The discipline (the no-smuggling gate + the costume gate, first-class)

- **The rate is EARNED, not smuggled (audit a, the phase sin).** `rate = univ.sup (span att)` is a `Finset.sup` over the finite attention — no numeral `c` added. It is a function of `att` (rfl), FINITE because the `Finset` is (the P2S0 bound, one level down at ℕ), and STRICTLY MONOTONE in the attention (`rate attSlow = 1 < 2 = rate attFast < 4 = rate attAll`). A postulated `c` would be indifferent to `att`; this rate tracks it. Delete every numeral: the rate is still `univ.sup (span att)`.
- **The cone is a RATE, not the bare order (audit c, the costume gate).** `attSlow` and `attFast` have the SAME causal order (`reaches attSlow = reaches attFast`) but different rate and so DIFFERENT cones. The cone carries `rate × depth`, content 2.5's order does not have; a cone that stripped to `{y | reaches att x y}` would be identical on the two carriers, and is rejected.
- **The cone is NON-TRIVIAL (audit d).** On `attSlow`, `p4` is strictly outside the depth-1 cone — a genuine finite speed. A cone that is the whole world (`attAll`) is the NO-CONE pole, not a cone.
- **The metric is a fixed spatial background.** `dist` is `Nat.dist` on the line, symmetric and attention-independent (2.4's breadth axis), so `rate × depth` is not circular: space (2.4) and the conversion rate (2.1) are kept distinct, honoring 2.4's two-axes result.
- **NO-CONE and the degenerate outcomes honorable.** If the rate were unbounded → NO-CONE; if the cone collapsed to the order → the disconnected/degenerate outcomes. NO-CONE is genuinely reachable (`attAll`, instantaneous reification), pre-registered, reported in full.

## 4. Cross-workstream triage

| WS | Object | Headline(s) | Costume / smuggle foreclosed |
|----|--------|-------------|--------------------|
| WS1 (ground) | `rate`, `span` | `ws1_rate_bounded`, `ws1_rate_earned_from_knows`, `ws1_rate_monotone`, `ws1_rate_tracks_attention` | bounded by attention, finite, tracks `att` — not a postulated `c` |
| WS2 | `ball` | `ws2_cone`, `ws2_cone_nontrivial` | the rate-bounded set; some event strictly outside |
| WS3 (anti-costume) | `rate` vs `reaches` | `ws3_rate_is_content`, `ws3_earned_from_attention` | same order, different rate, different cone; rate a function of `att` |
| WS4 (the knot) | `ball` | `ws4_cone_reachable`, `ws4_nocone_reachable` | both sides genuine, no fiat |
| WS5 | `verdict` | `ws5_verdict_eq (= cone)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)-(e) | computed, not hand-set |

## 5. The outcomes (WS5)

`cone` (the rate bounded and earned, the cone non-trivial and rate-content, both fork sides reachable — the expected close, relativity's cone recovered), `nocone` (the rate unbounded or the cone trivial — the world non-relativistic, the NOT-RECOVERED specification), `shapeDrawn` (the fork drawn, one side only in sight), `disconnected` (the cone collapses to the bare order — no genuine rate-content survives), `partial'` (degenerate; the rate not earned, an obligation degenerate; `partial` is a Lean keyword).

## 6. Names-in-prose rule (audit e)

The concept-words — light, cone, speed, relativity, spacetime, self, import, God, compass — appear only in docstring prose. Every proof term, definition, and discharged obligation carries a NEUTRAL name (`dist`, `span`, `rate`, `ball`, `reaches`, `reachWithin`, `verdict`, `Outcome`, `ws*`). In particular the cone's definition is named **`ball`**, not `cone` (`def cone` matches the §6 grep `\bcone\b`; `ball` does not). The theorem names `ws2_cone`, `ws4_cone_reachable`, `ws4_nocone_reachable` (the charter's target names) are underscore-wrapped, so the `\b…\b` grep does not match them (verified). No headline embeds a forbidden content-word as a whole word. The §6 grep runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt.
