# Phase B Revision Instructions (four findings; do this BEFORE Phase C)

**Why this exists.** The Phase B designs are structurally right and one workstream (WS1) is excellent. But a design review found four defects, two of which would hand the blind Phase D reviewer a legitimate SERIOUS finding and one of which regresses the program's oldest failure. Fix these in the design docs first; do not start the build until all four are closed. Each finding closes in exactly one of two ways per protocol §0.2a, and the revision commit message must name which: (Fixed) the specified correction was made, or (Relabeled) the correction is impossible and the precise obstruction is recorded in `charter-status.md`. "Adjusted something adjacent" is neither and is prohibited.

**What must NOT change.** WS1 in its entirety (the `Opening` shape, the coincidence with distinct quantifiers, `ws1_coincidence_not_identity`). The `Converges` core equation (`c.raise x W (c.orient x) = c.orient W`). The parametricity discipline (concrete compasses only inside existentials). The C7 trichotomy. The C5/C6 rejected decoys. The disclosed pointwise-`IsReify` deviation. The `cHold`/`cFail` isolation of the difference to the free raising. These are correct; the findings below are surgical.

---

## Finding 1 (SERIOUS): the witness carrier regressed to the point-tag silhouette; the generalization is gone

**Where:** `spec/ws4-witness-design.md`.

**The defect.** The carrier shrank to two states (`X = ULift Bool`, `aW`, `bW`) and `dirOf x = if x = bW then ⟨1⟩ else ⟨0⟩`. On a two-element carrier that is extensionally the point-indicator on `bW`, and the whole witness is two Booleans separated by a label, which is the exact extensional shape of `ws4_label_survives_quotient`, the failure this program has twice re-graded as its gravest inherited error. The intensional justification (`ws_witness_rank_is_tower`, `aW ∈ sW.1`, `bW = reifyW sW`) is real and must be kept, but it is not enough: a blind reviewer running the strip test deletes the tower vocabulary and finds the two-Boolean labelled-separation fact, and will correctly flag the silhouette. The prior witness design carried two certificates this version dropped: rank was NON-INJECTIVE (distinct states sharing a rank, so rank is genuinely coarser than identity and provably not a point-indicator), and rank GENERALIZED (a theorem separating any reified relatum with a reified constituent from any base relatum, tower load-bearing in the general statement, not just at one hand-picked pair).

**The fix.**
1. Restore a carrier of at least three states on which `rank` is NON-INJECTIVE. The minimal shape: two rank-0 base states (`a`, `a'`, each self-looping) and one reified state (`b = reify {a}`, with `dest b = {a}`), so `rank a = rank a' = 0` and `rank b = 1`. Five states (the earlier `a, a', b, b', c` carrier with `rank c = 2`) is also fine and gives a two-step tower; choose whichever keeps the Lean tractable, but non-injectivity of `rank` is non-negotiable and must be stated as its own lemma (`ws_witness_rank_noninjective : rankW a = rankW a' ∧ a ≠ a'`).
2. Reinstate the generalization theorem (the prior `ws4_purchase_general` shape): for any `dest`, `reify`, base set `Ω₀` with rank-0 closed successors, any `s` with `dest (reify s) = s` pointwise and a constituent `w₀ ∈ s.1` of rank at least 1, and any base relatum `y ∈ Ω₀`, no label-bisimulation over the rank-labelled lift relates `reify s` and `y`. The concrete witness pair is then an INSTANCE of the general theorem, and `reify`/`rank`/the base-closure are load-bearing in the general statement.
3. Keep the constituency-edge facts (`aW ∈ sW.1`, `bW = reifyW sW`) explicit, on whichever carrier is chosen, because WS4's model pair sits on that edge.
4. Update the self-classification section to cite all three certificates: non-injectivity, tower-definedness, and the generalization. The strip-test annotation must then honestly read: stripped, the fact is "a rank-labelled lift separates a reified relatum from a base relatum on a carrier where rank is coarser than identity, generally," which is NOT the two-Boolean fact.

**Relabel condition (if the fix is impossible):** if no carrier admits a non-injective rank with a discharged model pair, that is a finding about the witness (degenerate inhabitation, charter §4.d) and must be recorded as such in `charter-status.md`, routed to WS2, with Phase C blocked on it.

---

## Finding 2 (SERIOUS): the tower is phantom in the compass and convergence definitions; the layering is prose

**Where:** `spec/ws3-design.md` (the `Compass` type, `ws3_compass_layered`) and `spec/ws4-design.md` (`ConvergesUp`).

**The defect.** As designed, `Compass` is `{orient : X → Or, raise : X → X → Or → Or}` with `dest`/`reify` as unused type indices; `Converges` uses neither; `ConvergesUp` is `Relation.ReflTransGen Converges` over ARBITRARY pairs, so "up its layers" follows no layers; and `ws3_compass_layered` proves `prec {x} (reifyStep {x}) ∧ (P ∨ ¬P)`, whose compass-relevant conjunct is excluded middle. The charter's WS3 demands the compass be LAYERED, coupled through the structure of what informs it, neither one nor independent, and the coupling must live in the SHAPE (not in value-constraints). As typed, compasses are maximally independent and the tower is decorative: strip `dest`/`reify` from the definitions and nothing changes, which is a strip-test failure on the definitions themselves.

**The fix.** Put the tower into the shape, leave the values free.
1. Define the constituency edge once, ambient for WS3/WS4:
```lean
def ConstituentOf {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (x W : X) : Prop :=
  ∃ s : PkObj κ X, dest (reify s) = s ∧ x ∈ s.1 ∧ W = reify s
```
(The pointwise reification fact is part of the edge, consistent with the disclosed deviation.)
2. Restrict the layered form to the tower's edges. The minimal change (and the recommended one, because it leaves `Compass` untouched and every existing theorem valid):
```lean
def ConvergesUp {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or) : X → X → Prop :=
  Relation.ReflTransGen (fun x W => ConstituentOf dest reify x W ∧ Converges dest reify c x W)
```
Now "up its layers" follows constituency edges and `reify` is load-bearing in the definition. The witness edge (`aW`, `bW`) discharges the base case (its `ConstituentOf` facts already exist). A stronger alternative, edge-indexing the raising itself (`raise : (x W : X) → ConstituentOf dest reify x W → Or → Or`), is acceptable if the executor prefers it, but it touches every `Compass` mention; the `ConvergesUp` restriction is sufficient and cheaper.
3. Replace `ws3_compass_layered` with a theorem that has actual compass content. The honest statement of "coupled without being one and without being independent" is a two-sided freedom fact over a genuine edge, quantifier-honest:
```lean
theorem ws3_compass_layered (hinf : ℵ₀ ≤ κ) (hedge : ConstituentOf (destW hinf) (reifyW hinf) aW bW) :
    (∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool), Converges … c aW bW)
  ∧ (∃ c : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool), ¬ Converges … c aW bW)
```
That is: over a genuine tower edge, the coupling channel exists (the edge is where raising applies) and the coupling's value is free in both directions (not one: some compass does not cohere; not independent of the tower: the statement is only about tower edges). Note this is the underdetermination pair used at WS3 strength, which is fine (both live inside existentials); cite the WS4 model pair rather than duplicating witnesses. Delete the `P ∨ ¬ P` version entirely.
4. Update the WS3/WS4 strip-test annotations: stripped, `ConvergesUp` must now read "reflexive-transitive closure of a compass equation ALONG CONSTITUENCY EDGES," and the tower must not strip away.

**Relabel condition:** none anticipated; this fix is definitional. If the executor believes edge-restriction is wrong (for instance, that convergence should also be definable off-tower), the objection goes to `charter-status.md` routed to WS3 with the argument, and the charter's "up its layers" language is the bar it must answer to.

---

## Finding 3 (REAL): `ws4_wall_is_structural` is a bare conjunction claiming a bridge it does not prove

**Where:** `spec/ws4-design.md`, C4/D4.

**The defect.** The theorem is (the model pair) `∧` (`ws2_residue_free`). The conjuncts never interact; the claim "the wall is where the diagonal put it" is carried by the docstring, not the proof term. That is the coincidence-shaped move (a theorem that holds but is not the fact named) the program's audits exist to catch, and the blind reviewer will catch it.

**The fix.** Prove the real independence statement, which is already latent in the model pair: the two compasses live over the IDENTICAL plain structure, so everything the structure supplies is shared and only the non-recoverable compass differs, yet the verdicts are opposite. The honest theorem shape:
```lean
theorem ws4_wall_is_structural (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        (∀ x, plainOf-visible data at x is IDENTICAL for the two compassed structures)   -- shared structure
      ∧ Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW                                     -- opposite verdicts
```
Concretely, the shared-structure conjunct can be stated as: both compasses are over the same `destW` (definitionally shared; state it as `rfl`-provable equality of the underlying coalgebra, so the sharing is IN the theorem rather than in the metadata), plus, if the executor wants teeth, that `c₁` and `c₂` share `orient` (already true of `cHold`/`cFail`) so the difference is isolated to the raising. If a cleaner bridge to the diagonal is wanted, an acceptable alternative is a two-part theorem: (i) the model pair on one structure with shared orient, and (ii) a lemma that any function deciding `Converges` for all compasses on this carrier would distinguish the plain-bisimilar pair, hence be non-`Recoverable` (tying the decider itself to the opening). Either version is honest; the bare conjunction is not. If neither is provable in reasonable effort, DEMOTE: fold the structural gloss into D3's docstring and delete D4 as a theorem, recording the demotion in `charter-status.md`.

---

## Finding 4 (REAL): WS5's verdict ignores its certificate; the fork is inexpressible

**Where:** `spec/ws5-design.md` (and the `Audit` in `spec/ws7-design.md`).

**The defect.** `def verdict (_cert : Audit κ) : Series12Verdict := .shapeDrawn` discards its argument and returns a constant. Requiring a discharged `Audit` to call it is a weak gate, but this is the returned-constant-ignoring-its-certificate pattern by the letter, and it makes the pre-registered alternatives inexpressible: if WS4 had landed convergence-decided, no value of `verdict` could say so.

**The fix.** Make the audit carry the fork and the verdict case on it.
1. Add to `Audit` a field carrying WHICH disjunct of the C7 trichotomy was discharged, as a sum:
```lean
inductive ConvergenceFork (κ : Cardinal.{u}) : Prop → Prop → Prop → Type u
-- or, simpler and sufficient at Prop level:
structure Audit (κ : Cardinal.{u}) : Prop where
  …existing fields…
  fork : (∀ c, Converges … c aW bW) ∨ (∀ c, ¬ Converges … c aW bW) ∨
         (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW ∧ NonDegenerate … ∧ NonDegenerate …)
```
2. Define the verdict by cases on `fork`: first or second disjunct maps to `convergenceDecided` (carry the direction if the executor wants a richer verdict type), third maps to `shapeDrawn`. Because `Or`-elimination at `Prop` into a `Type`-valued verdict is not direct, either make `Series12Verdict` a `Prop`-level disjunction mirror, or make `fork` data-level (a small inductive with three constructors, each carrying its proof), which is the cleaner Lean; the executor chooses, but the verdict MUST branch on the certified disjunct, not return a constant.
3. `ws5_verdict_eq : verdict … = .shapeDrawn` remains, but now as a THEOREM (following from the audit's fork field being the third disjunct via the model pair), not a definitional constant.

---

## Where the revisions go

Edit the design docs in place on this branch (`spec/ws4-witness-design.md`, `spec/ws3-design.md`, `spec/ws4-design.md`, `spec/ws5-design.md`, `spec/ws7-design.md`, and `spec/README.md` §2.9/§2.10/§6 to match). Update `charter-status.md`: Phase B remains in progress until these four are closed; record each closure as Fixed or Relabeled with the theorem or obstruction named. Do not touch `charter.md` or `protocol.md`. Do not begin Phase C until all four are closed and the closures recorded. Em-dash discipline applies to all edited files; no series other than Series 07 is named in any design.
