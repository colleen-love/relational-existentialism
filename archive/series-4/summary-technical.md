# Relational Existentialism — Series 4: Technical Status Summary

*A machine-checked study of restriction-quality — quality drawn from inside the relata — and a precise map of what it can and cannot do.*

## 1. What was built

Series 4 asks (charter §4): **can a groundless relational world — no atoms, plural, no all-encompassing top, no view from nowhere, incomplete self-knowledge, non-degenerate — be constituted so that the *quality* distinguishing its objects is a *restriction* of the relata themselves (the part each turns toward another), rather than a value imported from an external algebra; and does making quality internal make the world's finite bound *endogenous* (grain, not wall) rather than imposed?**

The answer, machine-checked and folded through two rounds of adversarial review, is: **internal quality genuinely delivers plurality-without-atoms and leak-free composition, but it provably cannot make the world bound or position itself on this carrier.** The elegant "grain, not wall" thesis is *not* achieved; the sharp localization of where restriction-quality works and where it is decoration is the result.

The objects built are two self-contained terminal coalgebras, both realized as sets via a quotient-of-polynomial-functor / `Cofix` construction:

- the **plain carrier** `νPk` = terminal coalgebra of the κ-bounded powerset functor `P_κ` (a state is its `< κ`-set of successors); the derived **face** `x↾(x,y)` is the part of `x` reachable through its edge to `y`, defined from the successor relation alone (design candidate **R2**);
- the **labelled (faced) carrier** `νLk` = terminal coalgebra of `X ↦ P_κ (Q × X)`, where each successor edge carries a quality label `q : Q` as genuine functor data (the **R3** escalation), used exactly where the R2 derived face proves too weak (plurality).

Series 4 is **completely self-contained**: the carrier machinery reused from the archived Series 3 development is transcribed into `series-4/formal/`, and nothing is imported from `archive/`.

## 2. Verification status

- **`sorry`-free:** no proof-position `sorry`, `admit`, `native_decide`, `sorryAx`, or `opaque` anywhere in `ws1`–`ws7`. (Textual matches are in doc comments only.)
- **No custom axioms:** no `axiom` declarations. Every headline theorem rests only on Mathlib's standard three — `propext`, `Classical.choice`, `Quot.sound` — or on none.
- **In-build verification, machine-run:** `AxiomCheck.lean` imports the whole build (`Series4.lean`) and runs `#print axioms` on **41 headline theorems** across WS1–WS7. The captured run is committed at [`spec/axiom-check-log.md`](./spec/axiom-check-log.md) against **Lean 4 v4.15.0 / Mathlib v4.15.0**. A publication should cite the specific commit hash and a clean-build log.
- **Closure:** `scripts/gate.sh` confirms the `series-4/formal/` imports resolve only to Series 4's own roots plus Mathlib — no cross-series leakage.

## 3. Status against the success criteria (charter §8)

| Criterion | Status | Mechanism / honest note |
|---|---|---|
| (i) no atoms | **Impossibility (global) + local positive.** Global atomlessness collapses the world (`ws5_global_groundless_collapses`, from `ws2_collapse`); atomless-and-plural is realized *locally* on the labelled carrier. | plain-carrier collapse `ws2_collapse` (bisimulation = identity forces any two hereditarily-nonempty states equal); the faced counterpart is *false* — `ws3_plurality_core` gives distinct non-atomic loops distinguished by face |
| (ii) plurality (held by faces, not leaves) | **Healed.** | `ws3_loopface_ne` / `ws3_plurality_core`; the coincidence `ws3_same_succ_diff_face` — collapse on `νPk`, split on `νLk`, same bare successor shape |
| (iii) sameness is identity | **Discharged.** | terminality gives bisimulation = identity (`bisim_eq`); the R2 face changes no functor, so weak-pullback preservation is inherited (`ws1_weak_pullback_inherited`), not re-proved |
| (iv) no top / no observer *by the self-cost of facing* | **Relocated (cardinal wall); the "by faces" clause NOT delivered.** | `ws4_no_top_cardinal` (real, unconditional) is a bound on successor *count* (`#(str x) < κ ≤ #carrier`); `ws4_no_top_reach` routes through reachability with faces provably inessential (review S2). No-view is **Partial**: V1 (`ws4_view_is_positioned`) is definitional `rfl`, a face-routed V2 is **absent** (review R2). Faces cannot bound here — this *is* the WS5 M1/M2 negatives |
| (v) attention / incomplete self-knowledge, blind spot = diagonal, Ω complete-yet-unclosed | **Split.** Lawvere diagonal Discharged (carrier-independent); Ω non-termination Discharged (new); self-face-proper **Partial** (degenerate case only); blind-spot = diagonal **coexistence, equality open**; attention definitional; convergence deferred | `ws6_lawvere_incomplete` (Cantor diagonal); `ws6_omega_nonterminating` (complete in extent, self-membered — closed at no depth); `ws6_selfface_trivial` proves the R2 self-face is *always* empty or improper — a nontrivial proper self-face is unattainable on R2 |
| (vi) non-degenerate / no collapse to a point | **Discharged (plurality) + the collapse as sharp Impossibility.** | `≥ 2` distinct non-atomic states (`ws3_plurality_core`); the degenerate collapse is exactly `ws2_collapse` / `ws5_global_groundless_collapses`, a proved obstacle, not a shortfall |

**Two** of these are **sharp negative theorems that count as success** (charter §7): the Parmenides collapse (i, vi) and the global-groundlessness impossibility (i). And criterion (iv)'s "by the self-cost of facing" is the one the reviews reclassified from *Healed* to *Relocated* — the honest core of the series.

## 4. What restriction-quality does — and does not — do

The reviews converged on a single, sharp line. Below it, faces are the working machinery and the results are solid; above it, the Lean substitutes a cardinality fact or a definitional identity and the face vocabulary is decoration.

### 4.1 Where faces genuinely work (solid, correctly labelled)

- **Plurality (WS3).** Distinct faces give distinct atomless objects (`ws3_loopface_ne`, `ws3_plurality_core`), on a genuinely-built labelled terminal coalgebra `νLk`. The coincidence (`ws3_same_succ_diff_face`) shows the same bare shape collapses on `νPk` and splits on `νLk` — plurality is *earned* against the standing collapse, not stipulated.
- **Composition, unconditionally leak-free (WS3).** A real state-forming operator `lcomp` (built by corecursion on `Option`) with `ws3_faces_never_annihilate`: composing non-atomic faced states yields a non-atomic state, with **no** `BotFree`-style hypothesis. Because the face is internal, there is no external `⊥` for composition to reach. This is *strictly stronger* than Series 3's weighted carrier (`ws14`), which genuinely leaked at the nilpotent Łukasiewicz weight. The internality payoff is realized.
- **The imported-weight leak, located exactly (WS2).** Any external quality algebra with a `⊥`-divisor produces an atom under composition (`ws2_leak`); `⊥`-free algebras are safe but only by external fiat (`ws2_botfree_safe`). A concrete witness (`BotDivisorWitness` / `ws2_leak_witness`) exhibits the leak. So imported quality either leaks or is *forbidden, not unable*.
- **The Parmenides collapse (WS2).** `ws2_collapse`: in the plain gradeless world any two hereditarily-nonempty states are equal — a proper Aczel–Mendler bisimulation (`ζ(x,y) = str x × str y`) collapsed by `bisim_eq`. This is the hinge that *forces* quality.
- **The global-groundlessness Impossibility (WS5).** `ws5_global_groundless_collapses`: requiring atomlessness *everywhere* forces a subsingleton. Groundlessness and plurality coexist only locally; the bound cannot be globally freed while keeping plurality.
- **The second incompleteness at Ω (WS6 B2).** `ws6_omega_nonterminating`: Ω faces all of itself (`face Ω Ω = ReachSet Ω`) yet is self-membered (`Ω ∈ str Ω`), so its self-model is complete in extent but closed at no finite depth — the coinductive incompleteness the plain carrier could not express. Plus the carrier-independent Lawvere diagonal (`ws6_lawvere_incomplete`).

### 4.2 Where faces do not work (the reviews' corrections, now labelled honestly)

- **No-top is a cardinal wall, not a face wall (review S1/S2).** The purported endogenous wall (`ws4_no_top_reach`) is a *reachability* statement — `Reaches` exists with no face structure, the proof holds verbatim with faces stripped, and it is powered by the deferred cardinality fact `#reach x < #carrier`. The real, unconditional wall is `ws4_no_top_cardinal` (successor-count bound). Faces provably cannot supply the bound: the **WS5 M1/M2 negatives** (`ws5_contraction_insufficient`, `ws5_quotient_insufficient`) prove faces tame *quality*, not *branching* — so no face-counting wall exists on R2. No-top is **Relocated (cardinal wall)**, not Healed-as-endogenous.
- **No-view is not a real coincidence (review R2).** V1 (`ws4_view_is_positioned`) is `rfl` — "a view is a face" holds because a view was *defined* as a face. The forced partner V2 ("an unpositioned total view is impossible, routed through faces") does not exist as a distinct theorem; `ws4_no_global_observer` is the cardinal wall applied observer-side. So no-view is **Partial — V1 definitional, V2 absent**.
- **"One finitude" is a conjunction, not a derivation (review R1; sharpened by review-3 W1/W2).** `ws7_payoffs_hold` (renamed from `ws7_one_finitude`) conjoins six independently-proved payoffs; it does *not* take `FinitudeOfFacing` as hypothesis and derive them. And *no* payoff genuinely derives from finitude: `ws7_incompleteness_off_from_finitude` *projects* `FinitudeOfFacing`'s first clause (its proof is `h.1`, and the off-diagonal properness it "derives" is that very built-in conjunct), so it is a projection, not a derivation from an independent finitude (review-3 W1). Distinctness is mechanized for two pairs, of which only `ws7_plurality_vs_collapse_distinct` carries genuine force (two carriers); `ws7_deductions_dont_collapse` anchors predicate-exclusivity (disjoint domains), not deduction-independence (review-3 W2). The typed verdict is downgraded from `oneFinitude` to **`payoffsEstablished`**.
- **The R2 self-face is trivial (review R3 / WS6 scope).** `ws6_selfface_trivial`: the derived self-face is always empty (`x ∉ str x`) or improper (`x ∈ str x`) — never a nonempty proper part. So the charter's "proper self-face" holds only in the degenerate empty-face case (`ws6_selfface_proper_nonselfrelating`); the interesting incompleteness comes from the diagonal and from Ω, not from the self-face.

### 4.3 The pattern

Wherever the charter wanted faces to do **totality-work** — bound the world, position every standpoint, unify the payoffs under one principle — the Lean substitutes the cardinal fact or a definitional `rfl`, and the face vocabulary is decoration. Wherever faces do **local, constructive work** — distinguish, compose, resist collapse — the results are genuine. Internality buys plurality and leak-free composition; it does not buy an endogenous bound or a positioned totality, and on the R2 carrier it provably cannot.

## 5. The two review passes

- **`spec/project-review-1.md` (reconciliation).** Attempted charter-strength theorems first; delivered a real composition operator (`lcomp`), a face-routed no-top *attempt*, the R2 self-face triviality finding, a second distinctness anchor, and the first machine-run axiom check.
- **`spec/project-review-2.md` (adversarial).** Established that the pass-1 no-top "endogenous" wall was a reachability wall with faces painted on; that no-view's coincidence is `rfl` + the cardinal wall; and that the "one finitude" verdict is a conjunction, not a derivation. Corrections applied faithfully — mostly *relabel, not fix*, because faces cannot do the work on R2. No-top → Relocated; no-view → Partial; verdict → `payoffsEstablished`.

Both passes left `charter.md` untouched: every shortfall is stated as an explicit hypothesis, typed structure, or honest status downgrade — never a relabelled charter target.

## 6. Open problems (each named and routed)

1. **General internal-rigidity (WS2, F2).** The forced-answer dichotomy is proved; unconditional "every internal quality *is* restriction-quality" remains a defended heuristic under a canonicity witness.
2. **A face-counting no-top wall (WS4).** Withdrawn on R2 (faces do not bound); would require an R3-style carrier where faces are independent bounding data.
3. **The endogenous bound off the loop-spine (WS5).** The bound is endogenous only on the Ω-spine (`omegaGroundlessDiagonal`); extending it to carry plurality is open, and globally impossible (WS5).
4. **Blind-spot = diagonal equality (WS6, A3).** Both blind spots proved nonempty; their equality is downgraded to coexistence.
5. **A nontrivial proper self-face (WS6, A1).** Unattainable on R2 (`ws6_selfface_trivial`); needs a richer self-model.
6. **A real face-routed V2 (WS4).** Absent; unavailable on R2.
7. **The "one finitude" reduction + a six-way distinctness anchor (WS7).** Only partially mechanized; the verdict is scoped accordingly.
8. **The quantitative attention dynamics (WS6, Part C).** The Series 3 replicator / pitchfork characterization is not reproduced in this self-contained pass.

None is hidden; each sits in the open-obligations register of [`charter-status.md`](./charter-status.md).

## 7. The honest headline

Series 4 proves, sorry-free and axiom-clean: **(1)** gradeless groundless worlds collapse to a point (Parmenides); **(2)** internal faces restore plurality and compose without annihilation, unconditionally (the genuine positive, stronger than the earlier weighted object); **(3)** a second, coinductive incompleteness at Ω; and **(4)** global groundlessness is incompatible with plurality (the sharp Impossibility). It does **not** establish an endogenous bound, a real no-view coincidence, or a mechanized "one finitude" — and it locates *why* precisely: on this carrier, faces do quality-work, not totality-work. That boundary is the contribution.
