# Relational Existentialism — Series 3: Technical Status Summary

*A machine-checked constitution of a groundless, relation-first ontology, and what its formalization revealed.*

## 1. What was built

The program set out to answer one question (charter §4): **can the ungrounded constitution — objects that are nothing over and above their relations, relations that are themselves objects, a fabric with no atom, no all-encompassing "everything," and no collapse to a point — be given a rigorous mathematical constitution using non-well-founded set theory, coalgebra, and bialgebra?**

The answer, as of Series 3 with the axiom check passing, is **yes for a bounded reconstruction of the specification, with two of the seven success criteria satisfied as sharp impossibility theorems and the remaining dynamical obligation discharged for the exhibited replicator-mutator dynamics (linear *and* frequency-dependent exponential) on explicit convergence bands, leaving only the universal-regime blanket as a characterized band rather than a proof.**

The object built is the **terminal coalgebra of the κ-bounded powerset functor `P_κ`**, realized as a set via a quotient-of-polynomial-functor / `Cofix` construction. It is *not* the object the charter's §3.1 literally names (the class-sized final coalgebra of the full powerset functor / Aczel hyperuniverse); that object provably has no set-sized realization (Lambek + Cantor), and §3.9 sides openly with the bounded reading that §3.6 already endorsed. The canonical inhabitant `Ω = {Ω}` is recovered *inside* the bounded carrier.

## 2. Verification status

- **`sorry`-free:** no proof-position `sorry` anywhere in the ~3,100 lines of Lean across `ws1`–`ws8`. (All textual matches are in doc comments.)
- **No custom axioms:** no `axiom` declarations, no `admit`, `native_decide`, `sorryAx`, or `opaque` escape hatches. Every headline theorem rests only on Mathlib's standard three: `propext`, `Classical.choice`, `Quot.sound`. The `Łₙ` quantitative witness is even choice-free (`[propext, Quot.sound]`).
- **In-build verification:** `AxiomCheck.lean` imports the whole development and runs `#print axioms` on one representative top-level deliverable per workstream; it is a root of the `Series3` lean_lib, so `lake build` compiles it and emits the axiom record. **Confirmed passing on the author's build** (Lean 4 v4.15.0, Mathlib v4.15.0). The reproducibility claim in any publication should cite the specific commit hash and a clean-build log.

## 3. Status against the seven success criteria (charter §7)

| Criterion | Status | Mechanism |
|---|---|---|
| (i) no atoms | Discharged | atomlessness is automatic for a terminal coalgebra (`νF ≅ F(νF)` never bottoms out) |
| (ii) identity = relational unfolding up to bisimulation | Discharged | terminality gives bisimulation = identity (`ws2`) |
| (iii) reified relations as further elements | Discharged | single-sorted coalgebra; successors are themselves states |
| (iv) bidirectional constitution via coherent bialgebra | Discharged (bounded carrier) | strict law **impossible** (positive finding); weak Egli–Milner law canonical (`∃!`) and weak-pullback-preserving |
| (v) finite attention / incomplete self-knowledge | Split: incompleteness Impossibility-proved and `(F,κ)`-robust; plurality floor Discharged; convergence Discharged for exhibited linear & exponential replicators on explicit μ-bands | Lawvere diagonal for incompleteness; Banach spine for convergence |
| (vi) no substantive terminal standpoint | Discharged | `ws6_no_global_observer` (negative) + `ws6_substantive_standpoints` (positive) |
| (vii) non-degeneracy / no collapse | Structural half Discharged; dynamical half Discharged for both the linear and the exponential (frequency-dependent) replicator-mutator on explicit bands; only the universal-regime blanket left as a characterized band | richness floor + μ-floor + Lipschitz/Banach |

Two of these — the strict-distributive-law impossibility (iv) and the incomplete-self-knowledge result (v) — are **sharp negative theorems that count as success per §5**. They are not shortfalls; they are the philosophically interesting content.

## 4. The three fractures

Three commitments did not survive formalization in their literal form. Each broke along a different fault line, and the pattern is the central finding.

### 4.1 Commitment 4 (bidirectional constitution): strictness is incompatible with self-application

The Turi–Plotkin bialgebra picture wants a distributive law `λ : TF ⇒ FT` cohering composition (`T`) and observation (`F`). Because Commitment 2 makes relations *objects* — one sort, not two — both operations act on `P_κ`, and the required law is `P_κ` over itself. **`ws3_no_distributive_law` proves `IsEmpty (DistLaw κ)`** via a full port of the Klin–Salamanca `Bool × Bool` four-set diagonal: the unit laws + naturality pin `λ` so tightly that a two-fibre element must be simultaneously constant and non-constant in the fibre maps `fst`/`snd`/`xor`, where `fst = snd ⊕ xor`. Contradiction.

The content of (iv) survives via the **weak (Egli–Milner) law** `dest (alg t) = ⋃_{x ∈ t} dest x`, now proved **canonical** (`ws3_weak_law_canonical`, `∃!`) and **weak-pullback-preserving** (`wq_preserves_weak_pullback`, WS8-A). The finding: **relation-composition is inherently non-strict.** Strictness demands compose-then-observe equal observe-then-compose on the nose; but composing relations-as-objects produces an object whose observation is a *union* of the parts', and union's idempotent, order-forgetting character cannot respect strict coherence.

### 4.2 Commitment 3 (no poles, no outside): a portmanteau of three claims in three settings

"No poles, no outside" was never one commitment. Its three faces have different mechanisms and different fates:

- **No maximal everything.** Intended as a Cantor-wall argument about unbounded totality (`νF ≅ F(νF)` impossible by cardinality). But bounding to `P_κ` — required for existence — defeats that argument. The surviving proof (`ws6_no_maximal`) holds **by κ-fiat**: maximality would force the `< κ` support to be the whole carrier. True, but for a much weaker reason (a chosen size cap) than the philosophy wanted (structure too big to totalize).
- **No view from nowhere.** The first WS6 formalization found `PositionFree` holds **vacuously** on the terminal carrier (`endo_eq_id`: the terminal object admits only the identity self-map, so "no privileged position" is trivially true and contentless). Real content required WS8-E: a negative half (`ws6_no_global_observer` — no observer's `< κ` successor set surjects onto the carrier) and a positive half (`ws6_substantive_standpoints` — distinct bases give distinct positioned views).
- **Zero-object / pole-coincidence.** A category with a zero object (initial "void" = terminal "whole") is **not** `Set`/`Cofix`, where the bounded coalgebra lives. `ws6_no_faithful_zero_host` is open and almost certainly false as a blanket; the poles-coincidence object and the groundless carrier appear to be **different objects in different categories**, and "one object realizes both" is an unproven, probably unprovable, bridge. `ws6_poles_split` records the scoped impossibility of a faithful carrier-embedding landing entirely in zero objects.

Commitment 3 fractured because it packed a **cardinality** claim, an **indexical-standpoint** claim, and a **category-theoretic self-duality** claim into one "refusal of a distinguished endpoint." The prose unified them; the mathematics shows three absences with three proofs and three fates.

### 4.3 Commitment 6 (no singularity): parasitic, and partly reducible

Under formalization Commitment 6 turned out not to be independent structure but a bundle of side-conditions on parameter choice:

- **Standpoint collapse** *is* Commitment 3's no-view-from-nowhere, restated — no separate theorem.
- **Structural collapse** is barred by a richness floor. The charter's natural strong form, `GeneralBranching` (branching ≥ 2 at *every* state), was proved **false** (`ws7_general_branching_false`: the empty carrier-state has out-degree 0). The honest surviving floor is the `alg`-relative `ws7_iv_branching`.
- **Dynamical collapse** is the μ-floor — genuinely separable, but a constraint on the *dynamics bolted on*, not a property of the object. Now closed for the exhibited dynamics: attention provably converges to a unique fixed point on explicit μ-bands for both the linear and the exponential replicator (§6), so the honest dynamical status is `partial_band`, not `deferred`.

Commitment 6 fractured because it was **fencing off degeneracy**, not adding structure; one clause reduces to (3), one is impossible in its stated form and survives only relativized, and one concerns an add-on.

### 4.4 The unifying diagnosis

The three commitments that fractured (3, 4, 6) are exactly the three that make **global** claims about the totality — global coherence of composition, global claims about endpoints/outside, global non-degeneracy. The recurring cause of fracture is that **the bounding move that lets the object exist (Commitment 5's boundedness) systematically defeats the global claims**: it turns the Cantor wall into a fiat, makes the standpoint claim vacuous until repaired, makes universal branching impossible.

The **local** commitments — Commitment 2 (relations are objects) and the incompleteness half of Commitment 5 — survived intact, because they do not reach for the totality. Indeed, Commitment 2 *is* the type signature of the construction, and the incompleteness half of 5 is **the same modesty (boundedness) that makes the carrier exist at all**: the full powerset functor has no set-sized final coalgebra, the bounded one does, and finiteness of attention is precisely the non-surjectivity (Lawvere) that both tames "everything" into a set and forbids complete self-knowledge.

**Thesis (supported by the Lean structure):** *You cannot have both a set-sized (hence bounded) groundless object and the full strength of the global no-totality / no-endpoint / no-collapse-everywhere claims. The bound buys existence and weakens every commitment that quantifies over the whole.* This is itself a structural-realist result about the price of existence — the resistance is metaphysically informative, exactly as charter §9 bet.

## 5. The Goldilocks band

An admissible `(F, κ, μ, #Q)` tuple requires the conjunction:

**Structural** (`ws7_static_band`): at least two distinct states (`RichnessWitness`; the universal `GeneralBranching` is false, floor is `alg`-relative); no maximal state (`ws6_no_maximal`, by κ-fiat); weak-pullback preservation (`PkPreservesWeakPullback`).

**Cardinal:** `κ` infinite and **regular** (consumed in Banach/`hcard`); `κ ≤ mk (νP_κ).X`; shape-count coupling `#Q ≤ κ` (vacuous at the finite `Łₙ` via `luk_card_le`, binding for an unbounded quantale).

**Dynamical:** plurality floor `0 < μ` (load-bearing; `μ = 0` reintroduces collapse); contraction window — for the linear replicator, `2(1−μ) < μ·u_min` (μ near 1).

The band is proved **inhabited at one concrete tuple** `(P_κ, κ₀, μ, Łₙ)` with `n ≥ 2` (`ws7_retro_validate`), confirming the WS2 characterization, no-maximal, the WS6 split, and the WS4 graded coherence hold simultaneously there. This is "locate the band" on the *locate* side: one witnessed point, not a characterization of the full admissible region.

## 6. The attention dynamics (criterion vii, dynamical half)

- **Linear / frequency-independent replicator** `R(w)_r = w_r c_r / ∑ w_s c_s`: Lipschitz on the μ-floor with **explicit** constant `2/(μ·u_min)` (`linReplicatorLipschitz`), contracting on the band `2(1−μ) < μ·u_min`; unique fixed point via the Banach spine (`ws8_replicator_converges`), no bare hypothesis. Design correction surfaced honestly: the floor region is unbounded above, so the design's `w ≤ 1` / `C·δ⁻²` is unavailable; the honest constant is first-power `δ`, from scale-covariance.
- **Exponential / frequency-dependent replicator** `R(w)_r = w_r exp(f_r w) / Z(w)`: the target of §3.6, now **Discharged** (`ws8_exp_replicator_converges`, `ws8_exp_replicator_converges_band`). Fitness-dependence breaks scale-covariance, so on the *unbounded* floor region **no uniform Lipschitz constant exists** (the cross term is genuinely O(d²)) — meaning the exp map provably *cannot* inhabit `ws7.SelectionLipschitz`. The fix is not an upstream change but firing Banach **directly** on the floored simplex: on the *bounded* simplex-floor (where the dynamics actually lives, since `mutT` maps `FlooredSimplex` to itself) `expR_coord_lipschitz` proves Lipschitzness with the **explicit** constant `L = e^{2B}(1+L_f) + |S|·e^{4B}(1+L_f)`. Note this is *better* than the earlier estimate: there is **no `1/δ` term**, because `∑w = 1` bounds the normalizer below by `e^{−B}` directly rather than through the floor `δ`. Convergence to a unique fixed point follows on the band `(1−μ)·L < 1`, i.e. `μ > μ⋆_exp := 1 − 1/L` (`exp_band_iff`, a sharp threshold).

So the dynamical half of (vii) is now **closed for both** exhibited replicator families on explicit μ-bands — no bare hypothesis, no upstream lever pending. The honest status label is `partial_band` (`ws8_noncollapse_partial_band`), and deliberately **not** `impossible`: the floored simplex is compact and convex and `mutT` continuous, so Brouwer gives a fixed point for *every* `μ ∈ [0,1]` — the band governs uniqueness/convergence, not existence. What remains genuinely open is only (a) the *universal-regime* reading (convergence for all `μ` / all fitness as a blanket, which is characterized as a band, not proved as one), and (b) faithfulness to a continuous-time replicator ODE (out of reach sorry-free at present — a Mathlib flow/Picard–Lindelöf gap, recorded as a modelling obligation, not a hole).

## 7. Outstanding items

1. **Publication reproducibility.** Cite commit hash + clean-build log for the axiom-check claim; do not assert sorry-free/axiom-free without the pinned build.
2. **Universal-regime convergence.** Convergence is proved on explicit bands for both the linear and exponential replicators; the *blanket* reading (all `μ`, all fitness) stays a characterized band rather than a theorem — this is a genuine feature of the mathematics (contraction genuinely fails below `μ⋆`), not a missing proof.
3. **Continuous-time faithfulness.** Relating the discrete `mutT` to a continuous replicator ODE (that the fixed point is the ODE's equilibrium) is out of reach sorry-free at Mathlib v4.15.0 — a flow/Picard–Lindelöf packaging gap. Recorded as a modelling obligation, not a Lean hole.
4. **Interpretive gap (charter §8).** Untouched by any formalization: whether the object *is* the ROSR world or a faithful model of it. A philosophical question to frame, not overclaim settling.
5. **Graded transport (step-16).** The WS4-local residual — canonicity transport through `W_Q` — remains open.

*(Superseded since first draft: exp-replicator convergence — now discharged directly on the floored simplex, §6; and charter Revision F — now written, folding in the verified axiom-check state and the exp-fitness convergence.)*

## 8. What can be claimed

*We construct a set-sized mathematical object — the terminal coalgebra of the κ-bounded powerset functor — and prove in Lean 4, sorry-free and with no axioms beyond Mathlib's standard three, that it satisfies criteria (i)–(vi) of the ungrounded-constitution specification and the structural half of (vii), with the dynamical half established for both the linear and the frequency-dependent (exponential) replicator-mutator on explicit convergence bands. Two of the satisfactions are sharp impossibility theorems (no strict distributive law; no complete self-knowledge). The literal §3.1 carrier is proved non-existent as a set; the bounded reconstruction §3.6/§3.9 endorse is what is built.*

The most novel claim available is arguably not the existence result but the **interdependence result** of §4: the six commitments are not independent, the two local ones do the constructive work and yield atomlessness and non-degeneracy nearly for free, and the three global ones are precisely where the existence-forcing bound extracts its price.
