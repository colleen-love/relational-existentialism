# WS6 — The two incompletenesses

**Design doc. Series 4. Owns: incompleteness-by-blind-spot (off the diagonal) with its coincidence to the Lawvere fixed point; incompleteness-by-non-termination (on the diagonal, Ω); and attention as face-thickening.**

*References: the Lawvere/Cantor diagonal `ws5_carrier_incomplete` and `Function.cantor_surjective` (ws5); `strEqBisim`, `ws11_extensional_downward`, and the self-model former `selfModel` (ws11/ws15); `face`, `ws1_omega_face` (WS1); `Reaches`, `ReachSet`, `omegaCoalg` (ws1/ws12). WS6 reuses ws5's diagonal verbatim as one half of its coincidence theorem.*

## The object at stake

Charter §3.6 and §5.3, third payoff. Series 3 proved incompleteness once, via the Lawvere diagonal (`ws5_carrier_incomplete`: no state's attention support surjects onto its own self-descriptions). Restriction-quality makes the self-model a **face** — `x↾(x,x)`, the part turned inward — and this (a) threatens to make incompleteness *definitional* (a face is a proper part, so of course self-knowledge is partial — the trivialization trap in its sharpest form), and (b) surfaces a *second* incompleteness on the diagonal that the Series 3 machinery could not express. WS6 must earn (a) with a coincidence theorem and establish (b) as genuinely new.

## Part A — Incompleteness off the diagonal (blind spot)

### Candidates for the statement

- **A1 — Definitional (the cheap form, forbidden alone).**
```lean
theorem ws6_selfface_proper (x : (νPk κ).X) (hx : not-a-loop x) :
    face x x ⊊ ReachSet x
```
"The self-face is a proper part." **Paper triage:** true and near-trivial for non-loop states (the inward face misses the parts reachable only outward). Decidable, easy — and *exactly* what the coincidence rule forbids reporting as Discharged on its own. It says self-knowledge is partial *because we modeled it as a proper sub-object*.

- **A2 — The Lawvere diagonal (the forced form, imported).**
```lean
theorem ws6_lawvere_incomplete (u : (νPk κ).X) : ¬ Surjective (selfDescription u) :=
  ws5_carrier_incomplete u
```
**Paper triage:** already proved (ws5), consumes no cardinality fact, `(F,κ)`-robust. Import verbatim. This is *forced* — it holds even if you tried to build a complete self-model, by pure diagonalization.

- **A3 — The coincidence theorem (the earning, new).**
```lean
/-- The part the self-face omits IS the Lawvere diagonal fixed point. -/
theorem ws6_blindspot_is_diagonal (x : (νPk κ).X) (hx : not-a-loop x) :
    (ReachSet x \ face x x) = { the Lawvere fixed point of selfDescription x }
```
**Paper triage — the crux of Part A.** This says the *geometric* blind spot (what the inward face misses) equals the *logical* blind spot (the diagonal sentence no self-map captures). Decidable to state; the proof must exhibit the Lawvere fixed point (from `Function.cantor_surjective`'s witness) and show it lands exactly in `ReachSet x \ face x x`. **This is what makes A1 non-trivial:** the proper-part fact (A1) and the diagonal fact (A2) are shown to be the *same* fact, so incompleteness is not merely definitional — the definition's blind spot *is* the diagonal's. **The design bet:** the Lawvere witness for `selfDescription x` is a self-description that refers to `x`'s outward-only reach, which is precisely `ReachSet x \ face x x`. If the self-model former (`selfModel`, ws15) is defined as face-thickening (Part C below), this alignment is natural rather than forced.

**Winner: A1 + A2 + A3 as the coincidence bundle**, with A3 the load-bearing new theorem.

## Part B — Incompleteness on the diagonal (non-termination)

On the self-loop spine, `ws1_omega_face` gives `Ω↾(Ω,Ω) = Ω`: Ω faces *all* of itself, so A1's proper-part argument *fails* — Ω has no blind spot. This looks like Ω completely knows itself, contradicting "no object ever wholly knows itself." The resolution is a *different* incompleteness.

### Candidates

- **B1 — Deny it (wrong).** Claim Ω is the exception and does know itself completely. **Paper triage:** rejectable — it would falsify the universal charter claim and, worse, miss the real structure. Not a candidate, listed to close it off.

- **B2 — Extent vs closure (the target).** Ω's self-face is *complete in extent* (all of Ω) but the self-model is *itself an object with its own self-face*, coinductively, so self-knowledge is total at every finite unfolding and **closed at none**.
```lean
/-- Ω's self-model is total in extent but never terminates: for every finite
    depth n, Ω knows itself to depth n, and the self-knowing at depth n itself
    requires self-knowing at depth n+1. -/
theorem ws6_omega_nonterminating :
    (∀ n, selfModelDepth omegaState n = ReachSet omegaState)   -- complete at every depth
  ∧ (¬ ∃ N, selfModelClosed omegaState N)                       -- closed at no depth
```
**Paper triage:** decidable and the two conjuncts are genuinely different from A's blind spot. The first uses `ws1_omega_face` (extent is total); the second uses the coinductivity of `νPk` (the self-model is corecursive, no finite closure) — directly analogous to how `Ω = {Ω}` never "finishes." **This is the new incompleteness the charter promised**, and it formalizes the founding axiom *self is a paradox*: complete in the act, never as a possession.

- **B3 — Via ws11's downward-determination (a sharper mechanism, optional).** ws11 proved (`ws11_extensional_downward`, `strEqBisim`) that on strongly extensional carriers identity is downward-determined and the upward stream is redundant. Ω's self-knowledge being "total but unclosed" can be phrased as: the downward unfolding is complete yet the fixed-point equation `Ω = {Ω}` has no finite certificate. **Paper triage:** a nice reuse but adds machinery; hold as an enrichment of B2, not a separate result.

**Winner: B2**, optionally sharpened by B3.

## Part C — Attention as face-thickening

Charter §3.5, §5.3. Series 3's attention was a replicator bolted onto the carrier (ws8/ws9). Restriction-quality makes it internal: attending to a relation = thickening its face; starving = thinning.

### Candidates

- **C1 — Redefine the replicator as face-mass redistribution.**
```lean
/-- Attention is a redistribution of face-mass across a state's edges. -/
def attend (x : (νPk κ).X) (weights : succ x → Face) : (νPk κ).X   -- thickens/thins faces
```
**Paper triage:** decidable; the design question is whether face-thickening reproduces the Series 3 replicator dynamics (so the ws8/ws9 convergence characterization, pitchfork μ⋆ = ½, transfers) or changes them. **Reuse target:** ws8's `ws8_replicator_converges` and ws9's `ws9_bifurcation` should re-derive as statements about face-mass, *if* face-thickening is defined to match the replicator. Design instruction: define `attend` so the induced map on face-mass *is* the replicator, making the transfer a relabeling rather than a re-proof.

- **C2 — Self-model as attention's fixed point.**
```lean
theorem ws6_selfmodel_is_attention_fixedpoint :
    selfModel x = fixed point of (attend x ·)   -- the inward face is where attention settles
```
**Paper triage:** ties Part C to Parts A/B — the self-model `x↾(x,x)` is the attractor of the attention dynamics, so the "bolted-on" caveat dissolves: the dynamics and the self-model are one structure. Decidable; depends on C1's definition landing.

**Winner: C1 (attend as face-mass, matching the replicator) + C2 (self-model as its fixed point).** The convergence characterization is *inherited* from ws8/ws9 by construction, not re-proved — the payoff of internality.

## The coincidence duty (charter §7)

Part A *is* a coincidence theorem by design: A3 proves the definitional blind spot (A1) equals the forced diagonal (A2). WS7 audits that A3 is a real identity of two independently-defined objects (the face-complement and the Lawvere witness), not a definition dressed as a theorem. Part B is genuinely new (no cheap form to launder). Part C's caveat-dissolution must not hide a change in the dynamics — WS7 checks the ws8/ws9 transfer is faithful.

## Outcome classes

- **Discharged:** A (coincidence bundle) + B2 + C1/C2, with the convergence characterization inherited from ws8/ws9.
- **Partial:** A3 (the blind-spot/diagonal identity) is the likeliest to resist — if it holds only up to a containment rather than equality, report A as "blind spot ⊆ diagonal, equality open."
- **The clearest expected win (charter §9):** Part B (non-termination) is new, low-risk, and the most distinctive result — the founding axiom made into a theorem.

## Deliverable

`series-4/formal/ws6.lean`: `ws6_selfface_proper` (A1), `ws6_lawvere_incomplete` (A2, re-export), `ws6_blindspot_is_diagonal` (A3), `ws6_omega_nonterminating` (B2), `attend` + `ws6_selfmodel_is_attention_fixedpoint` (C1/C2), and the ws8/ws9 convergence re-exports phrased over face-mass. Axiom check owed; A2's core is `Classical`-only (inherited from ws5).
