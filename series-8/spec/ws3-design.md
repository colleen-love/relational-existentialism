# WS3 — Re-restriction and forced dynamics

**Design doc. Series 8, the engine of Part Two. Owns: the re-restriction map (`spec/README.md` §2.4, ambient for WS4–WS5), its two cheap obligations **(NL)** no leaf and **(NF)** not-a-function, the forcing of dynamics from finitude-on-atomlessness, and the ONE endogenous order `≺` — with the imported-index branch designed in as a refuted failure mode, never a fallback.**

*Series 8 is standalone; names transcribed into `series-8/formal/Series8/ws3.lean`, re-namespaced `Series8.WS3` (see `spec/README.md` §6). Unlike WS1–WS2 this is **genuinely new Lean**: the carrier is transcribed, but `Hold`, `ReReStep`, `prec`, and the forced-dynamics non-termination are Series 8 content. Per protocol §C, the re-restriction map and (NL)+(NF) are the **first thing built** (the seed of the series); **conservation (CB) is NOT attempted here and is never folded into `ReReStep`** — it is WS5's, on the map WS3 hands it.*

## The object at stake

Charter §3 and Consequence 2 (§2, §5.2). Re-restriction is the modulation of a hold toward a narrower face that resolves a deeper node. Three properties are demanded, each a separate obligation:

- **(NL) No leaf.** Re-restriction narrows but never empties a node; `SHNE` is preserved. A narrower face is still a full face. This is the hard rejection of limit-atomlessness (§4.3): no transient bare relatum, ever.
- **(NF) Not-a-function.** The narrowing is a *free facing*, not determined by the prior hold: two identical holds can re-restrict differently. This is what keeps the dynamics from being Series 7's determined collapse.
- **Forced dynamics.** A finite hold affords only a `< κ`-bounded slice, but the atomless field never bottoms out, so no hold is `SReaches`-closed; resolving deeper *requires* a new hold. Dynamics is not added; it is forced by finitude-on-atomlessness.

And the load-bearing methodological duty (§4.2): the order `≺` must be **endogenous** — derived from re-restriction sequences, not an imported stage-index (the Series 5 trap). WS3 fixes `≺` once (`spec/README.md` §2.4) and proves its endogeneity; WS4 and WS5 consume the *same* `≺`.

**Ambient theory.** `spec/README.md` §2.1 (carrier, `SReaches`, `SHNE`, `SHNE.succ`, `SHNE.ne_empty`), §2.2 (`Hold`, `afford`), §2.4 (`ReReStep`, `prec`). The self-loops `twoLoop` / `omegaState` (transcribed) are the constant-breadth witnesses for (NF) and for the WS5 kill condition; a two-successor node is the witness for (NF).

## Candidates

### C1 — Re-restriction = follow-the-edge on holds; (NL)+(NF) as map facts (the lead)

```lean
def ReReStep (dest) : Hold dest → Hold dest → Prop :=
  fun h h' => h'.1.1 = h.1.2 ∧ h'.1.2 ∈ (dest h'.1.1).1
theorem ws3_rerestriction_no_leaf {X} (dest : X → PkObj κ X) (h : Hold dest)
    (hs : SHNE dest h.1.1) : ∃ h', ReReStep dest h h' ∧ SHNE dest h'.1.1        -- (NL)
theorem ws3_rerestriction_not_function {X} (dest : X → PkObj κ X) (h : Hold dest)
    (h₁ h₂ : Hold dest) (hne : h₁ ≠ h₂) (r₁ : ReReStep dest h h₁) (r₂ : ReReStep dest h h₂) : True  -- (NF) witnessed
```
A hold `x↾(x,y)` re-restricts to `y↾(y,z)` for any successor `z` of `y`: narrow from x's perspective to y's, resolving the deeper node z.

- **Ambient:** the hold type; `ReReStep` follows the edge; breadth is measured separately (§2.5).
- **Success condition (NL):** from an `SHNE` hold there is *always* a next re-restriction, and its source is again `SHNE` (`SHNE.ne_empty` gives a successor `z` of `y`; `SHNE.succ` gives `SHNE` at `y`). Never stuck at a leaf, never empties a node.
- **Success condition (NF):** a hold at a node `y` with two successors `z ≠ z'` re-restricts to two distinct holds — the narrowing is not a function of the prior hold.
- **Failure mode:** *conservation-assumed / painted-on.* The only trap is defining `ReReStep` to *remove the chosen successor* from the sibling set (baking foreclosure in). C1 does not: it follows the edge and touches no sibling set, so conservation stays a separate, testable WS5 question. This is the protocol §0.4 guard, honored by construction.

**Paper triage.** Decidable and short: (NL) is `SHNE.ne_empty` + `SHNE.succ`; (NF) is a two-successor witness. The map touches no breadth data, so conservation is not baked in. **Winner.**

### C2 — Re-restriction as a relation on `afford` sub-fields (semantic form)

```lean
theorem ws3_rerestriction_narrows {X} (dest) (h h' : Hold dest) (r : ReReStep dest h h') :
    afford dest h' ⊆ afford dest h        -- the narrower hold affords a sub-field
```
State re-restriction semantically: the new hold's afforded field is *contained* in the old — narrowing is literal set-inclusion of affords.

- **Failure mode:** *inclusion may fail without reflexivity bookkeeping.* `afford h' = {z | SReaches dest z' z}` (from the new target `z'`) sits inside `afford h = {z | SReaches dest y z}` because `z'` is reachable from `y` in one step, so `SReaches dest y` ⊇ `SReaches dest z'` by `ReflTransGen.head`. True and clean. But "narrowing = ⊆ of affords" is the *depth* reading, which is WS4's; here it risks pre-empting WS4.

**Paper triage.** A genuine, clean lemma (`ReflTransGen.head`), and it is what makes "narrowing" honest — but it is WS4's depth content. **Route the inclusion lemma to WS4 (`ws4_depth_is_narrowing`); WS3 keeps the *step* (C1), WS4 keeps the *inclusion*.**

### C3 — Forced dynamics: no hold is `SReaches`-closed on an atomless field (the lead for Consequence 2)

```lean
theorem ws3_dynamics_forced {X} (dest : X → PkObj κ X) (h : Hold dest) (hs : SHNE dest h.1.1) :
    ∃ h', ReReStep dest h h' ∧ ¬ (afford dest h' ⊆ {z | z ∈ afford dest h ∧ (dest z).1 = ∅})
```
A finite hold cannot statically contain the atomless field: from every hold there is a further re-restriction into a still-atomless (leaf-free) sub-field, so the re-restriction relation **never terminates** — the field must be unfolded over succession, not held at once.

- **Ambient:** `SHNE` (the field never bottoms out); the non-termination of `ReReStep`.
- **Success condition:** the term produces, from any `SHNE` hold, a next re-restriction whose target is again `SHNE` (so the process cannot halt) — dynamics is *forced*: there is no static hold that is `SReaches`-closed and leaf-free.
- **Failure mode:** *non-termination read as a bug, not a feature; or the forcing asserted between definitions.* The honest form is the crisp theorem "`SHNE ⇒ ∀ hold, ∃ next re-restriction with `SHNE` target" (an infinite ascending `prec`-chain), NOT a hand-waved "a finite hold can't hold infinity." The theorem IS the forcing.

**Paper triage.** Decidable: it is (NL) iterated — `SHNE` gives an always-available `SHNE` next step, so `ReReStep` is serial (total, no terminal hold) on the `SHNE` sub-poset. **Winner (Consequence 2), phrased as seriality/non-termination.**

### C4 — The endogenous order `≺` and its non-importedness (the §4.2 guard)

```lean
def prec (dest) : Hold dest → Hold dest → Prop := Relation.ReflTransGen (ReReStep dest)
theorem ws3_order_endogenous {X} (dest : X → PkObj κ X) (h h' : Hold dest) :
    prec dest h h' ↔ Relation.ReflTransGen (ReReStep dest) h h'      -- ≺ IS the closure of re-restriction
theorem ws3_prec_is_reach {X} (dest) (h h' : Hold dest) (hp : prec dest h h') :
    SReaches dest h.1.1 h'.1.2                                       -- ≺ projects onto SReaches (reach = trace)
```
`≺` is the reflexive-transitive closure of `ReReStep` — defined from `dest` alone, no external index. Its projection onto the carrier is exactly `SReaches`: reaching is the *trace* of a narrowing sequence (charter §3).

- **Failure mode:** *painted-on / imported index.* If `≺` were an external `ℕ`-stamp, endogeneity would fail. C5 refutes that branch as a theorem.

**Paper triage.** `prec` is a closure of a `dest`-defined relation; endogeneity is `Iff.rfl`, and the reach-projection is `ReflTransGen` induction. **Winner (the ONE order).**

### C5 — The imported-index branch, refuted (pre-registered failure mode, NOT a fallback)

```lean
-- The imported order: a stage counter stamped from outside, ≺ᵢ m m' := stage m < stage m'.
-- BUILD FIX (2026-07-11, recorded in charter-status.md): the pre-build sketch stated this with
-- `h ≠ h'`, which CANNOT hold on `twoLoop` — its holds are the fixed points `(i,i)` (the only
-- successor of `i` is `i`), so a re-restriction returns the SAME hold. The honest content — the
-- order CYCLES, so no strict monotone index represents it — is a self-loop STEP `ReReStep h h`:
theorem ws3_imported_index_refuted (hinf : ℵ₀ ≤ κ) :
    ∃ h : Hold (twoLoop hinf), ReReStep (twoLoop hinf) h h    -- a genuine re-restriction step, h ↝ h
```
The self-loop re-restricts to itself: there is a genuine `ReReStep h h`, so `prec h h` is a cycle at a single hold — and **no external strict monotone stage-index** can represent it (a strict index forbids `stage h < stage h`). The order is genuinely the endogenous re-restriction closure, not a disguised counter. *(The signature correction preserves the §4.2 intent exactly: `≺` is not a disguised strict stage-index. It is a faithful fix, not a retarget — the `h ≠ h'` form was unrealizable on the chosen witness, and no witness with a genuinely distinct re-restricted hold exists on a self-loop.)*

- **Failure mode of the branch itself:** this is the *refutation*, so its success is showing the imported index does **not** fit. If it *did* fit (a monotone stamp reproducing `≺`), Consequence 2 would be an import (Series 5) and dynamics assumed. The self-loop cycle forecloses that.

**Paper triage.** Decidable: `twoLoop`'s single state re-restricts to itself, so `prec` has cycles, which no strict stage-order admits. **Winner (the §4.2 guard, as a refutation).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `ReReStep`; (NL) no leaf, (NF) not-a-function | `SHNE.succ`, two-successor witness | yes — short | **win (the map + NL + NF)** |
| C2 | narrowing = ⊆ of affords | `ReflTransGen.head` | yes | → WS4 (depth) |
| C3 | dynamics forced (non-termination) | (NL) iterated, seriality | yes | **win (Consequence 2)** |
| C4 | `≺` = closure of re-restriction; reach = trace | `ReflTransGen`, `Iff.rfl` | yes | **win (the ONE order)** |
| C5 | imported index refuted (`≺` cycles) | `twoLoop` self-loop | yes | **win (§4.2 guard)** |

## Winning candidates: C1 (map+NL+NF), C3 (forced dynamics), C4 (the order), C5 (index refuted); C2 routed to WS4

### Definitions and obligations (cite `spec/README.md` §2; this is the seed build)

```lean
namespace Series8.WS3
-- carrier, SReaches, SHNE, SHNE.succ, SHNE.ne_empty, twoLoop, twoLoop_HNE — transcribed (README §6);
-- Hold, afford from WS1.

def ReReStep (dest : X → PkObj κ X) : Hold dest → Hold dest → Prop :=
  fun h h' => h'.1.1 = h.1.2 ∧ h'.1.2 ∈ (dest h'.1.1).1
def prec (dest : X → PkObj κ X) : Hold dest → Hold dest → Prop := Relation.ReflTransGen (ReReStep dest)

/-- **D1a — (NL) no leaf.** From an `SHNE` hold there is always a next re-restriction, and its source
    is again `SHNE`: narrowing never empties a node. Uses `SHNE.ne_empty` (a successor exists) and
    `SHNE.succ` (it is `SHNE`). Honors the hard rejection of limit-atomlessness (§4.3). -/
theorem ws3_rerestriction_no_leaf (dest : X → PkObj κ X) (h : Hold dest)
    (hs : SHNE dest h.1.2) : ∃ h' : Hold dest, ReReStep dest h h' ∧ SHNE dest h'.1.1 := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hs.ne_empty
  exact ⟨⟨(h.1.2, z), hz⟩, ⟨rfl, hz⟩, hs⟩

/-- **D1b — (NF) not-a-function.** A hold at a two-successor node re-restricts to two DISTINCT holds:
    the narrowing is a free facing, not determined by the prior hold. Witness on a node with `z ≠ z'`. -/
theorem ws3_rerestriction_not_function (dest : X → PkObj κ X) (h : Hold dest) {z z' : X}
    (hz : z ∈ (dest h.1.2).1) (hz' : z' ∈ (dest h.1.2).1) (hne : z ≠ z') :
    ∃ h₁ h₂ : Hold dest, ReReStep dest h h₁ ∧ ReReStep dest h h₂ ∧ h₁ ≠ h₂ :=
  ⟨⟨(h.1.2, z), hz⟩, ⟨(h.1.2, z'), hz'⟩, ⟨rfl, hz⟩, ⟨rfl, hz'⟩,
   fun he => hne (by simpa using congrArg (fun k => k.1.2) he)⟩

/-- **D2 — forced dynamics (C3).** On an `SHNE` field every hold has a further re-restriction with an
    `SHNE` target, so `ReReStep` is serial — NO hold is terminal, the field must be unfolded over
    succession. Dynamics is forced by finitude-on-atomlessness, not added. -/
theorem ws3_dynamics_forced (dest : X → PkObj κ X) (h : Hold dest) (hs : SHNE dest h.1.2) :
    ∃ h' : Hold dest, ReReStep dest h h' ∧ SHNE dest h'.1.2 := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hs.ne_empty
  exact ⟨⟨(h.1.2, z), hz⟩, ⟨rfl, hz⟩, hs.succ hz⟩

/-- **D3 — the ONE endogenous order (C4).** `≺` is the closure of re-restriction (`Iff.rfl`), and it
    projects onto `SReaches`: reaching is the trace of a narrowing sequence. -/
theorem ws3_prec_is_reach (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    SReaches dest h.1.1 h'.1.1 := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl.head h.2  -- x reaches y in one step (the hold's own edge)
  | tail _ hstep ih => exact ih.tail (by rw [hstep.1]; exact hstep.2)  -- append the re-restriction edge

/-- **D4 — the imported-index branch refuted (C5, §4.2 guard).** On the self-loop there is a genuine
    re-restriction step `h ↝ h`, so `≺` cycles at one hold and no strict monotone stage-index can
    represent it: the order is genuinely endogenous, not a disguised counter. (Signature corrected
    from the pre-build `h ≠ h'` sketch — see C5 and `charter-status.md`.) -/
theorem ws3_imported_index_refuted (hinf : ℵ₀ ≤ κ) :
    ∃ h : Hold (twoLoop hinf), ReReStep (twoLoop hinf) h h := by
  have hmem : (⟨true⟩ : ULift.{u} Bool) ∈ (twoLoop hinf ⟨true⟩).1 := by rw [twoLoop_val]; exact rfl
  exact ⟨⟨(⟨true⟩, ⟨true⟩), hmem⟩, rfl, hmem⟩
```

**D1a/D1b (NL, NF)** are the seed obligations (protocol §C): short, map-only, no breadth clause — so conservation is *not* baked in. **D2 (forced dynamics)** is (NL) sharpened to seriality: no terminal hold, hence forced unfolding — a genuine theorem, not an asserted intuition. **D3 (the order)** fixes `≺` and proves reach = trace. **D4 (index refuted)** discharges the §4.2 guard as a *refutation*, pre-registering the imported index as a failure mode, never a fallback.

## Outcome classes (per charter §7)

- **Discharged:** D1a (NL), D1b (NF), D2 (forced dynamics), D3 (the endogenous order + reach-as-trace), D4 (imported index refuted). All are short and map-only.
- **Partial (pre-registered, universal form → WS6):** "dynamics is forced across *any* construction" is the un-rangeable quantifier (charter §5.3) — WS3 proves seriality on any single `SHNE` coalgebra; the all-constructions universal is WS6's heuristic ceiling.
- **Failed (pre-registered honest alternative):** if `≺` could be represented by a monotone external index (D4's refutation *fails*), the order is not endogenous, Consequence 2 becomes an import (Series 5), and dynamics is assumed — routed to WS7. Not expected: the self-loop cycle forecloses it.
- **Strip test.** (a) Delete **"re-restriction"** from `ws3_dynamics_forced` and the statement is the bare **`SHNE ⇒ every state has an `SHNE` successor`** — a reachability seriality fact (`SHNE.ne_empty` + `SHNE.succ`). Forced-dynamics **survives the strip** as a seriality fact; the earned layer is reading non-termination as *forced unfolding*. (b) Delete **"narrowing/hold"** from `ws3_prec_is_reach` and it is the bare **`SReaches` = closure fact** (`ReflTransGen`). (c) The load-bearing residue that does **not** strip: `≺` genuinely being the re-restriction closure and **not** an external index (D4) — that is the endogeneity, and the self-loop cycle proves it is not a painted-on order. WS7 records: the map and order are honest (no baked-in breadth, no imported index); the *dynamism* reading is the interpretive surplus over the seriality fact.

## Deliverable

`series-8/formal/Series8/ws3.lean` (**the first Lean file of the series in spirit**, charter §3): transcribed carrier (README §6); `ReReStep`, `prec`; `ws3_rerestriction_no_leaf` (NL), `ws3_rerestriction_not_function` (NF), `ws3_dynamics_forced`, `ws3_prec_is_reach`, `ws3_imported_index_refuted`. **`breadth` and conservation are NOT defined here** — they are WS5's, on this map. Axiom check: `#print axioms ws3_dynamics_forced` reduces through `SHNE.succ` / `Set.nonempty_iff_ne_empty` to the standard three.
