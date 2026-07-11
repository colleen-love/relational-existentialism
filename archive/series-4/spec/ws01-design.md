# WS1 — The world and its faces

**Design doc. Series 4, blocking workstream. Owns: the restriction functor, the "face is forced not annotated" claim, the fixed point, and the weak-pullback gate on which the whole program is conditional.**

*References Series 3 Lean by name where machinery is reused: `PkObj`, `Coalg`, `IsTerminalCoalg`, `lambek`, `Bisim`, `bisim_eq`, `omegaCoalg`, `exists_terminal_coalg` (ws1); `PkPreservesWeakPullback`, `ws2_weak_pullback`, `PkRel` (ws2); `Reaches`, `ReachSet`, `level` (ws10/ws12).*

## The object at stake

Series 3's carrier is the terminal coalgebra of `PkObj κ` (`str : X → PkObj κ X`, a state is its `< κ`-set of successors). Series 4 refines the *structure map* so each successor carries a **face**: the part of the source turned toward it. The design question is which of several functor shapes (a) makes the face **forced by the successor relation** rather than extra data, (b) **preserves weak pullbacks** so that bisimulation stays identity (charter point 1 / criterion iii), and (c) **refines** `PkObj` (the lossiness thesis — Series 4 is `PkObj` with discarded structure restored, not a different object).

The gate (b) is existential for the program (charter §9). Every candidate below is triaged first on a decidable-on-paper version of (b).

## Candidates

### R1 — Extrinsic face: an arbitrary sub-state tag

```lean
def RObj (κ) (X) := {s : PkObj κ X // ∀ x ∈ s.val, Sub x}   -- face : an arbitrary subobject of source, chosen per edge
```
Face is a *freely chosen* sub-object attached to each edge, part of the coalgebra data.

**Paper triage.** Fails (a) immediately: the face is annotated, not forced — two coalgebras with the same successors but different tags are distinct, so "an object is its relating" already fails at the structure level, and the lossiness thesis is false (this is strictly *more* data than `PkObj`, not less-forgetful). Reject without reaching the pullback test.

### R2 — Intrinsic face via reachability: `x↾(x,y) = ReachSet x ∩ (stuff through y)`

```lean
-- face of x toward successor y := the part of x reachable *through* the edge to y
def faceThrough (x y : (νPk κ).X) : Set (νPk κ).X :=
  {z | Reaches x z ∧ RoutedThrough x y z}   -- z reachable from x on a path whose first step is y
```
Face is **defined from the plain successor relation** (`Reaches`, ws12) — no new data. The coalgebra is still `str : X → PkObj κ X`; the face is a *derived* operation on the existing carrier.

**Paper triage.** Passes (a): forced, since `faceThrough` is a function of `str` alone. Passes (c): the carrier *is* `νPk κ`, so the lossiness thesis is not just satisfied but trivial — Series 4 is a *reading* of the Series 3 object, and every Series 3 discharge transfers verbatim. Passes (b) *for free*: weak-pullback preservation is a property of the functor `PkObj`, already proved (`ws2_weak_pullback`), and R2 does not change the functor — it adds a derived operation, so `PkPreservesWeakPullback κ` still holds and criterion (iii) is inherited, not re-proved. **This is the shape that makes the gate a non-event.**

### R3 — Genuine restriction functor: face as a source-subobject *in the functor*

```lean
def RFObj (κ) (X) : Type := {p : PkObj κ X // faces : ∀ x ∈ p.val, PkObj κ X}
-- the functor itself carries, per successor, a sub-collection of the *source's own* successors
```
The face is part of `F`, but constrained to be a sub-collection of the source's successors (so still "internal"), giving a bona fide new endofunctor `RF` with `νRF` a new carrier.

**Paper triage.** Passes (a) if the face-constraint is tight enough to force it; passes (c) only up to a comparison map `νRF → νPk` (refinement becomes a theorem, not a triviality). The live question is (b): `RF` references the source's structure, so it is **not obviously a polynomial/container functor**, and `ws2_weak_pullback`'s proof (a Barr-lifting argument on `PkRel`) does **not** transfer. Paper triage is *decidable but negative-leaning*: check whether the relation lifting `RFRel` equals the pullback of `PkRel` along the face-constraint; if the face-constraint is a *sub*-object (monomorphism-like), Barr lifting is preserved and (b) holds; if it can be an arbitrary relation, (b) fails. **Verdict: hold as the fallback if R2's derived-operation reading proves too weak to state the payoffs (see below).**

### R4 — Two-sided (dependent-pair) functor carrying both faces

```lean
def R2Obj (κ) (X) := {s : PkObj κ X // ∀ x ∈ s.val, (faceOut : Sub source) × (faceIn : Sub x)}
```
Records both `a↾(a,b)` and `b↾(a,b)` on the edge (the double-empathy two-sidedness of charter §5.1).

**Paper triage.** The `faceIn` component references the *successor's* subobject, i.e. it is contravariant-flavoured. Decidable-on-paper test: a functor with a contravariant component is not an endofunctor on `Type` in the required variance, so `νR2` need not exist by the standard terminal-coalgebra route (`exists_terminal_coalg` does not apply). Reject as the *carrier*; **retain `faceIn` as a derived notion** on the R2 carrier (it is computable from `Reaches` in the other direction) for WS4/WS6's positioned-view content.

## Winning candidate: R2 (derived intrinsic face on the `νPk κ` carrier), with R3 as typed fallback

The decisive move: **the face is a derived operation on the Series 3 carrier, not a change of functor.** This collapses the existential gate (b) to an already-proved fact and makes the lossiness thesis trivially true.

### Definitions

```lean
namespace Series4.WS1
open Series3   -- PkObj, Coalg, νPk, IsTerminalCoalg, lambek, Bisim, bisim_eq, Reaches, ReachSet

variable {κ : Cardinal.{u}} (hinf : ℵ₀ ≤ κ)

/-- A path of length ≥ 1 from `x` whose first successor is `y`. -/
def RoutedThrough (x y z : (νPk κ).X) : Prop :=
  y ∈ ((νPk κ).str x).val ∧ Reaches y z

/-- **The face**: the part of `x` reachable through its edge to successor `y`.
    Forced by `str` alone — no annotation. -/
def face (x y : (νPk κ).X) : Set (νPk κ).X :=
  {z | RoutedThrough x y z} ∪ {y}

/-- The face is a sub-object of `x`'s reachable part (internal). -/
theorem face_sub_reach (x y) : face x y ⊆ ReachSet x := by
  intro z hz; rcases hz with ⟨hstep, hreach⟩ | rfl
  · exact Reaches.trans (Reaches.single hstep) hreach
  · exact Reaches.single (by exact hstep? )   -- y is a one-step reach of x
```

### The three obligations, each decidable-on-paper

**D1 — Face is forced (lossiness thesis, trivial form).**
```lean
theorem ws1_face_forced :
    ∀ (C : Coalg κ) (_ : IsTerminalCoalg C), ∃! f : C.X → C.X → Set C.X,
      ∀ x y, f x y = face x y
```
*Strategy:* `face` is literally a function of `str`; uniqueness is `rfl`-level. This is the whole content of "Series 4 refines rather than replaces": the carrier is `νPk κ`, the face is definable, so **every Series 3 theorem holds unchanged** and the inheritance ledger (WS-A3, folded into this doc) is "everything transfers." *Paper-decidable:* yes — it is a definitional identity.

**D2 — The gate, inherited.**
```lean
theorem ws1_weak_pullback_inherited : PkPreservesWeakPullback κ := ws2_weak_pullback
```
*Strategy:* one line. Because R2 does not touch the functor, the gate is `ws2_weak_pullback` verbatim, so bisimulation-is-identity (`bisim_eq`) holds and criterion (iii) is inherited. *This is the design's central payoff:* the risk that killed programs — a bespoke functor failing weak-pullback preservation — **does not arise**, because there is no bespoke functor. *Paper-decidable:* yes.

**D3 — Ω recovered with its face.**
```lean
theorem ws1_omega_face (hinf) :
    face (omegaState hinf) (omegaState hinf) = {omegaState hinf}
```
*Strategy:* Ω's only successor is itself (`omegaCoalg`), so the only routed-through target is Ω; the face is `{Ω}`, i.e. all of Ω. This is the **improper-face-on-the-diagonal** fact the charter flags (§5.3, and the disarmed pole-coincidence curiosity): `Ω↾(Ω,Ω) = Ω`. *Paper-decidable:* yes, from `omegaCoalg`'s definition.

### Why R2 and not R3

R3 is the "honest new functor" and is more faithful to the charter's prose picture of a genuinely enriched carrier. But it puts the existential gate back in play — weak-pullback preservation of a non-container functor is exactly the thing that has no proof and might be false. R2 *proves the same faces exist and are forced* while keeping the gate discharged for free. The design principle (Series 3 §8.2 discipline): **take the surrogate that recovers the intended content inside an already-safe object, and only escalate to the risky functor if a payoff provably cannot be stated on the safe one.**

### The one place R2 might be too weak (routed to fallback)

R2's face is a *set of states* (a sub-object as a subset), not a *sub-coalgebra with its own independent structure map*. If WS3's plurality witness or WS5's bounding argument needs faces that can be **compared across different sources as objects in their own right** (not just as subsets of a common carrier), R2's subset-face may not carry enough structure, and R3's functor-level face is required. Decidable-on-paper trigger, checked at WS3/WS5 kickoff: *does the payoff quantify over faces as elements of the carrier, or only as subsets of it?* If the former, escalate to R3 and pay the pullback-preservation proof; if the latter, R2 suffices. **Pre-registered:** WS1 reports R2 as the carrier and records R3 as a typed fallback `RFObj` with `WQPreservesWeakPullback`-style open obligation, exactly as Series 3 ws4 registered its Layer C hole.

## Outcome classes (per charter §7)

- **Discharged:** D1–D3 proved (expected; they are near-definitional on the R2 reading).
- **Impossibility proved:** only reachable if the R3 fallback is forced *and* its weak-pullback preservation is refuted — a sharp negative redirecting the carrier. Not expected via R2.
- **Partial:** R2 carrier delivered, R3 escalation flagged open for a specific downstream payoff.

## Deliverable

`series-4/formal/ws1.lean`: `RoutedThrough`, `face`, `face_sub_reach`, `ws1_face_forced`, `ws1_weak_pullback_inherited`, `ws1_omega_face`; the `RFObj` fallback typed but unbuilt. Axiom check: `#print axioms ws1_weak_pullback_inherited` should reduce to `ws2_weak_pullback`'s record (`propext, Classical.choice, Quot.sound`).
