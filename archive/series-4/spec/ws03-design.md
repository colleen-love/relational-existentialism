# WS3 — Plurality without atoms

**Design doc. Series 4. Owns: two atomless objects distinguished purely by faces, and the characterization of when face-composition stays atom-free.**

*References: `νPk`, `omegaCoalg`, `bisim_eq`, `Bisim` (ws1); `face`, `RoutedThrough` (WS1); `ws2_collapse` (WS2, the forced counterweight); the collapse mechanism `ws10_unlabeled_atomless_collapses` (ws10); the composition/closure split pattern and `BotFree` from `ws14_core_closed` / `ws14_core_not_closed_Luk` (ws14).*

## The object at stake

Charter §5.3, first payoff. On the plain carrier, `ws2_collapse` says any two hereditarily-nonempty states are equal. WS3 must exhibit **two hereditarily-nonempty states that differ only in their faces** — same successor *sets*, distinct faces toward a shared neighbour — and prove them distinct. The subtlety: on the R2 reading (WS1), the carrier *is* `νPk κ`, where `ws2_collapse` holds. So two states with identical hereditary successor structure **are literally equal**. Faces are a derived operation; they cannot distinguish states that are already equal. This is the design tension WS3 must resolve, and it is decidable on paper which way it goes.

## The central dichotomy (paper-decidable, decides the whole workstream)

Either:

- **(I) Faces distinguish only via the successor structure they are derived from.** Then two states with the same hereditary successors have the same faces, `ws2_collapse` applies, and **plurality-by-faces is impossible on the R2 carrier** — faces are epiphenomenal, and WS3 must escalate to WS1's R3 fallback (faces as genuine functor data, a new carrier `νRF`).
- **(II) Faces carry information not recoverable from the bare successor set.** Then two states can share a successor *set* yet differ in *how* they route through it, and plurality lives on `νPk κ` after all.

**The paper-decidable test:** does `face x y` depend on anything beyond `ReachSet x` and `str`? By WS1's definition, `face x y = {z | RoutedThrough x y z} ∪ {y}`, and `RoutedThrough` is defined from `str` and `Reaches`. So `face` is a **function of `str`**. Two states equal in `str`-unfolding have equal faces. **Therefore (I) holds on the R2 carrier**, and this is decidable now, before any Lean.

### Consequence: WS3 forces the R2/R3 escalation trigger from WS1

This is exactly the "one place R2 might be too weak" that WS1 pre-registered. The plurality payoff *quantifies over faces as bearers of independent distinguishing information*, which R2 cannot supply (faces are `str`-derived). So WS3 is the workstream that **escalates the carrier to R3** — faces become genuine functor data, and the weak-pullback gate must now be discharged for `RF`. This is not a failure; it is the design working as intended: the cheap carrier is tried first and the payoff that needs more escalates deliberately.

## Candidates for the R3 plurality witness

On `νRF κ` (faces as functor data: a state assigns to each successor an *independently chosen* sub-collection of the source's successors), build two atomless states distinct only by face.

### P1 — Twin self-loops with different self-faces
```lean
-- two states, each with successor set {itself}, but different faces toward that successor
def loopFace (F : Sub) : (νRF κ).X   -- self-loop whose self-face is F
theorem ws3_loopface_ne {F₁ F₂ : Sub} (h : F₁ ≠ F₂) : loopFace F₁ ≠ loopFace F₂
```
**Paper triage:** the closest analogue of ws14's `ws14_loop_ne` (which distinguished loops by *weight*; here by *face*). Decidable: distinctness must survive the terminal identification `RF`-`bisim_eq`, which holds iff the face is part of the bisimulation relation `RFRel`. Since in R3 the face is functor data, `RFRel` includes it, so distinct faces give distinct states. **Strong candidate**, directly parallel to the proven ws14 result.

### P2 — Shared-neighbour states (the charter's own example)
```lean
-- a, b both relate to a common z, but a↾(a,z) ≠ b↾(b,z)
theorem ws3_shared_neighbour_ne : ∃ a b z, z ∈ succ a ∧ z ∈ succ b ∧ face a z ≠ face b z ∧ a ≠ b
```
**Paper triage:** matches charter §5.3 prose exactly ("the parts they turn toward a shared neighbour differ"). Slightly more complex than P1 (three states, not two). Decidable and true on R3 for the same reason as P1. **Use as the illustrative headline; prove P1 as the minimal core.**

### P3 — Distinguish by face where successor sets are literally identical
```lean
theorem ws3_same_succ_diff_face : ∃ a b, succ a = succ b ∧ a ≠ b   -- impossible on νPk, possible on νRF
```
**Paper triage:** this is the sharpest statement — it is *false* on `νPk` (that is `ws2_collapse`'s territory) and *true* on `νRF`. Proving both is the **coincidence theorem** for this payoff: plurality is earned exactly by the move from R2 to R3. **This is the one to feature**, because it makes the earning explicit.

### P4 — Atomless plurality bundle (headline)
```lean
theorem ws3_plurality_core :
    ∃ a b : (νRF κ).X, a ≠ b ∧ HereditarilyNonempty a ∧ HereditarilyNonempty b
      ∧ (bare successor structure of a and b coincides)   -- distinguished only by face
```
**Paper triage:** assembles P1/P3 with hereditary-nonemptiness (both are self-loops with nonempty self-face, so trivially atomless). Direct analogue of ws14's `ws14_graded_core_plural`. Decidable; the atomlessness half is immediate for self-loops with nonempty face.

**Winner: P4 as the bundle, built from P1 (minimal distinctness) and P3 (the coincidence — false on `νPk`, true on `νRF`).**

## The composition question (the internal echo of the WS2 leak)

Charter §5.3 and §9: when faces compose, can a composed face degenerate to the **empty object** (the atom re-entering, now internally rather than through an imported `⊥`)? This is the R3 analogue of ws14's ⊥-divisor fork, and the design mirrors ws14's split exactly.

### Candidates for the closure result

- **C-split (winner, from ws14 pattern).** Prove composition preserves nonempty faces *under a hypothesis* and exhibit a *failure witness* without it — the direct transplant of `ws14_core_closed` (positive under `BotFree`) and `ws14_core_not_closed_Luk` (negative at nilpotent). The R3 analogue of `BotFree` is a **no-face-annihilation** condition: composing faces `F₁` then `F₂` yields empty only if one was empty.
```lean
def FaceComposable : Prop := ∀ F₁ F₂, (F₁ ∘face F₂ = ∅) → (F₁ = ∅ ∨ F₂ = ∅)

theorem ws3_composition_closed (h : FaceComposable) : (composition preserves atomlessness)
theorem ws3_composition_leaks (h : ¬ FaceComposable) : ∃ (witness), composed face = ∅
```
**Paper triage:** decidable that this is the right shape (it is ws14's split with `BotFree` → `FaceComposable`). The interesting *difference* from ws14: here the annihilation condition is about **reachability composing to the empty reach**, which is a *structural* property of the carrier, potentially *always true* (reach never empties unless a source was already empty) — in which case the negative half is **vacuous** and composition is unconditionally closed. That would be *stronger* than ws14 (which genuinely leaked at nilpotent `Luk`), and is the hoped-for payoff of internality: no external `⊥` means possibly no annihilation at all.

- **C-unconditional (the optimistic target).** Prove `FaceComposable` holds *always* on `νRF`, because a composed reachable-face is empty only if a factor's reach was empty, i.e. a factor was an atom.
```lean
theorem ws3_faces_never_annihilate : FaceComposable κ
```
**Paper triage:** *this is the key open bet.* It is decidable-in-principle but not decidable-by-inspection: it depends on whether R3's face-composition is defined as reach-composition (in which case it plausibly holds — reach of a nonempty-reach through a nonempty-reach is nonempty) or as something that can cancel. **Design instruction:** define R3 face-composition as reach-composition precisely to make `ws3_faces_never_annihilate` provable; if a payoff forces a cancelling composition, fall back to C-split.

**Winner: attempt C-unconditional (`ws3_faces_never_annihilate`) by defining composition as reach-composition; fall back to C-split (ws14 transplant) if cancellation is forced.** Either outcome is reportable: unconditional closure is the internality payoff realized; the split is the honest ws14-parallel.

## The coincidence duty (charter §7)

Explicit and central here: **P3 is the coincidence theorem.** WS3 proves plurality *and* re-proves (`ws2_collapse`, imported) that without faces the same states collapse. The pair — "distinct on `νRF`, provably equal on `νPk`" — shows the plurality is bought exactly by the face structure, not assumed. WS7 audits that P3's two halves are genuinely the same states seen with and without faces.

## Outcome classes

- **Discharged:** P4 (plurality bundle) + P3 (coincidence) + one of {C-unconditional, C-split}.
- **Impossibility proved:** if C-unconditional fails, the C-split negative witness is a sharp result.
- **Partial:** plurality delivered, composition-closure conditional (if neither C-unconditional nor a clean split lands).
- **Trivialized (routed to WS7):** if P3's two halves turn out not to be about the same states — flagged, not expected.

## Deliverable

`series-4/formal/ws3.lean`: the R3 carrier escalation (`RFObj`, `νRF`, its `bisim_eq`, and the weak-pullback obligation inherited-or-discharged from WS1's fallback), `loopFace`, `ws3_loopface_ne` (P1), `ws3_same_succ_diff_face` (P3 coincidence), `ws3_plurality_core` (P4), and the composition result (`ws3_faces_never_annihilate` attempted, C-split as fallback). Cross-references `ws2_collapse` for the coincidence. Axiom check owed on `ws3_plurality_core`.
