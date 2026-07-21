# Series 2.9 (The Cone) — technical summary

**Status: BUILT and reviewed. Verdict CONE, computed. The full development is `program-2/series-9/formal/P2S9/` (`ws1`–`ws5`, `P2S9`, `AxiomCheck`); it compiles sorry-free, axiom-clean (standard three), gate-green, names-grep clean. Imports `P2S8` only; `P2S7 / … / P2S0 / P1` transitive. Blind Phase C (design) and Phase F (code) each returned 0 SERIOUS.**

## 1. What is built

The carrier is `S := Fin 5`, a line of five peers (`p0`…`p4`, the 2.4 lateral world re-seated). A fixed lateral metric carries breadth; the rate is a `Finset.sup` over the finite attention; the cone is the rate-bounded ball; three attentions carry the fork.

```
def dist (x y : S) : ℕ := Nat.dist x.val y.val                            -- the lateral metric (breadth, attention-independent)
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)   -- the per-tick reach
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)     -- the speed c, read off the attention
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)               -- the cone
def reaches (att : S → Finset S) (x y : S) : Bool := ...                   -- decidable bounded reachability (the causal order)
def attSlow / attFast / attAll : S → Finset S                             -- forward-1 (rate 1) / forward-2 (rate 2) / attend-all (rate 4)
```

`rate` is a function of the attention `att` alone (a `Finset.sup`, no postulated numeral), tying it to `P2S0.knows` via `knows att x y := P2S0.knows att x y = (y ∈ att x)`.

## 2. The theorems

| Theorem | Content |
|---|---|
| `ws1_rate_bounded` | `∀ att x y, y ∈ att x → dist x y ≤ rate att` — the per-tick reach cannot outrun the rate (`Finset.le_sup` twice) |
| `ws1_rate_earned_from_knows` | `knows att x y → dist x y ≤ rate att` — the bound is over exactly the P2S0-attended relata |
| `ws1_rate_monotone` | `(∀ x, a x ⊆ b x) → rate a ≤ rate b` — the rate tracks the attention |
| `ws1_rate_tracks_attention` | `rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4` — strictly monotone, not a fixed cap |
| `ws2_cone` | `y ∈ ball att x depth ↔ dist x y ≤ rate att * depth` — the cone is the rate-bounded set |
| `ws2_cone_nontrivial` | `p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1` — some inside, some strictly outside |
| `ws3_rate_is_content` | `(∀ x y, reaches attSlow x y = reaches attFast x y) ∧ rate attSlow ≠ rate attFast ∧ ball attSlow p0 1 ≠ ball attFast p0 1` — same order, different rate, different cone |
| `ws3_earned_from_attention` | `rate = univ.sup (span att)` (def) ∧ monotone in `att` — a function of the finite attention, not a postulated c |
| `ws4_cone_reachable` | `rate attSlow = 1 ∧ ∃ y, y ∉ ball attSlow p0 1` — a finite rate, a non-trivial cone (CONE) |
| `ws4_nocone_reachable` | `∀ y, y ∈ ball attAll p0 1` — total attention reifies instantaneously (NO-CONE) |
| `ws4_nocone_trivial` | `ball attAll p0 1 = Finset.univ` — the NO-CONE cone is the whole world |
| `ws5_verdict_eq` | `verdict true true true true true true = Outcome.coneOut` (`rfl`) |
| `ws5_verdict_discriminates` | the six-input verdict reaches all five outcomes |
| `ws5_flags_justified` | the six deciding flags are the WS1–WS4 facts |
| `ws5_audit_rate_earned` / `_fork_genuine` / `_rate_not_order` / `_cone_nontrivial` / `_names_not_terms` | audit (a)–(e) |

## 3. The mathematics

The construction realises a discrete causal cone as a metric ball whose radius is a rate times a depth, with the rate EARNED from the finite attention rather than postulated. The lateral metric `dist = Nat.dist` on the line is a fixed spatial background (2.4's breadth axis, symmetric and attention-independent). The rate is the two nested suprema `rate att = ⨆_x ⨆_{y ∈ att x} dist x y` — the greatest lateral reach of any one tick — a `Finset.sup` over the finite attention, hence finite (the P2S0 finiteness bound, one level down at `ℕ`) and monotone in `att` (`Finset.sup_mono`). The bound `ws1_rate_bounded` is `dist x y ≤ span att x ≤ rate att` by `Finset.le_sup` at the neighbourhood level and again at the world level.

The cone `ball att x depth = {y | dist x y ≤ rate att * depth}` is the rate-bounded reachable set (`ws2_cone`, by `Finset.mem_filter`). Its content beyond the causal order is the costume gate: `reaches` (bounded directed reachability, the transitive closure re-seated as a decidable Finset closure) is IDENTICAL on `attSlow` and `attFast` — both give the forward order `x ⤳ y ↔ x ≤ y` — while their rates (1 vs 2) and hence their depth-1 cones ({p0,p1} vs {p0,p1,p2}) DIFFER. So the cone is not recoverable from the order: `ws3_rate_is_content`.

The fork is reached on two carriers built from the same `rate`/`ball`/`dist`:
- **`attSlow`** (forward neighbour, rate 1): `ball attSlow p0 1 = {p0,p1}`, and `p4` (distance 4) is strictly outside — a genuine finite speed. **CONE.**
- **`attAll`** (attend everyone, rate 4 = the diameter): `ball attAll p0 1 = univ` — every event inside at depth 1, no elsewhere, instantaneous reification. **NO-CONE.**

Neither side is a fiat: `ball` does not branch on the carrier; CONE and NO-CONE are facts about which attention is present. The verdict computes `coneOut` because the rate is bounded (WS1) and earned (WS3), the cone is non-trivial (WS2) and rate-content (WS3), and both the CONE and NO-CONE sides are reachable (WS4), the NO-CONE side witnessing that the fork is not by fiat.

## 4. The no-smuggling gate and the costume gate

- **Earned, not smuggled (audit a, the phase sin).** `rate` is `univ.sup (span att)` — no numeric `c` added, no fixed cap independent of `att`. It is monotone in `att` and takes 1/2/4 as the attention widens. A postulated speed would be indifferent to the attention; this rate is a strictly monotone function of it. The blind Phase F reviewer confirmed no constant is baked into `rate` or `ball`.
- **A rate, not the bare order (audit c, the costume gate).** `attSlow` and `attFast` share the causal order (`reaches attSlow = reaches attFast`) but not the cone. A "cone" that stripped to `{y | reaches att x y}` would be equal on the two carriers; ours is not, so it carries genuine rate-content.
- **The metric is not the dynamics.** `dist` is a fixed spatial background, independent of `att`, so `rate × depth` is not circular; space (2.4) and the conversion rate (2.1) are kept distinct, honouring 2.4's two-axes result.

## 5. Axioms and closure

`AxiomCheck.lean` records, per payoff, dependence only on `propext` / `Classical.choice` / `Quot.sound` (several on none: the `verdict`/`rfl` facts). No `native_decide`, no added axiom. `scripts/gate.sh` confirms the imports resolve to `P2S8` / `P2S9.*` / Mathlib only (`P2S7 / … / P2S0 / P1` transitive). The names-not-terms grep over `formal/` is clean: no proof term is named `light` / `cone` / `speed` / `relativity` / `spacetime` / `self` / `import` / `god` / `compass`; the cone's definition is `ball`, the outcome constructors are `coneOut` / `noconeOut`, and the theorem names `ws2_cone` / `ws4_cone_reachable` / `ws4_nocone_reachable` are underscore-wrapped (the `\b…\b` grep does not match them).

## 6. Verdict

**CONE.** A bounded rate earned from finite attention (WS1); the cone the rate-bounded set and non-trivial, something strictly outside (WS2); the cone genuine rate-content, not Series 2.5's order — same order, different rate, different cone (WS3); and both a finite-speed world (a non-trivial cone) and an instantaneous world (a trivial cone) reachable, neither by fiat (WS4). The verdict is computed, not hand-set (WS5). Finite attention is a maximal rate of becoming, and relativity's light cone is the shadow of a bounded capacity to attend. The pre-registered NO-CONE, SHAPE-DRAWN, DISCONNECTED, and PARTIAL were not reached; each was live in the verdict function and foreclosed by proof, not by construction. The Lorentz mixing of the two axes (a boost trading breadth for depth at rate `c`) is a forward-note, not this series' target; 2.9 establishes the cone only.
