# Series 4 — Executor Instructions: Reconcile Lean to Charter

**Purpose: bring the formalization up to the charter and design specifications. The charter is the fixed bar. Every instruction below moves the *code* toward the charter; none softens a charter claim to match the code. Where the bar cannot be met, the required output is an honest Partial / Impossibility with the obstruction made mathematically precise and routed — never a relabeled target (charter §5, §8.2).**

*Source of this list: a blind project review of `series-4/formal/ws1.lean … ws7.lean` against `charter.md` and `spec/wsNN-design.md`. Four workstreams prove something narrower than their charter claim; the status file currently records the broader claim. The gaps are label drift, not false theorems — there is no `sorry` and no false statement. These instructions close the drift by strengthening the Lean, and where that is impossible, by reporting Partial against the unchanged charter.*

## Governing rule for the executor

For each item: **first attempt the charter-strength theorem.** Only if it provably resists do you fall back — and the fallback is *always* "report Partial with the obstruction named," never "restate the theorem at the strength that happens to hold." A charter criterion that is not met is recorded as not-met in `charter-status.md`, with the precise obstruction, and the charter text is left untouched. Do not edit `charter.md`.

Do not change any charter claim, success criterion, or the fractures tracker's *targets*. You may only change: the Lean files, the docstrings/comments in them, and the *status* columns of `charter-status.md` (to reflect what is actually proved, up or down).

---

## WS4 — the flagship. No-top must be endogenous or reported Partial.

**Charter bar (§5.3, §8):** no object relates to everything *by the self-cost of facing* — "you can only turn part of yourself toward another, and you are not big enough to face everything." The wall must be a fact about faces, not a cardinal cap on the carrier.

**What is currently proved:** `ws4_no_top_facing` derives the contradiction from `#(str x) < κ ≤ #carrier` (`carrier_card_ge`). Faces appear nowhere in the proof. `FacingInjective` and `ws4_faces_inject` are proved but unused. This is the Series 3 cardinality fiat with a self-cost docstring — it does not meet the charter bar.

**Instruction — attempt the charter-strength theorem (primary).**

Prove no-top *through faces*, routing the contradiction through `ws4_faces_inject`, not through `str`-cardinality:

1. State the honest crux hypothesis explicitly as a definition (do not hide it): a state `x` is **cofinally facing-injective** if the map `y ↦ face x y` on its successors is injective (`FacingInjective x`, already defined).
2. Prove: if `x` faced every object (`∀ y, y ∈ str x`), then under `FacingInjective x` the map `y ↦ face x y` injects the whole carrier into `{S : Set (νPk κ).X // S ⊆ ReachSet x}`, the sub-objects of `x`'s reach. Use `ws4_faces_inject`.
3. Derive the contradiction from **the size of `x`'s own reach**, not the carrier: `#(sub-objects of ReachSet x)` must dominate `#carrier`, but `ReachSet x` is a bounded part of `x`. If the reach is `< κ`-controlled (it is, on the ℵ₀ witness — cf. Series 3 `ws12_reachable_card_le`, transcribe if needed), the injection is impossible. The contradiction now reads "x would need more distinct faces than it has parts," which is the self-cost wall.

```lean
theorem ws4_no_top_endogenous (x : (νPk κ).X)
    (hinj : FacingInjective x)
    (hreach : Cardinal.mk (ReachSet x) < Cardinal.mk (νPk κ).X) :
    ¬ (∀ y, y ∈ ((νPk κ).str x).1) := by
  -- if x faces everything, y ↦ face x y injects carrier into subobjects of ReachSet x;
  -- but faces are subsets of ReachSet x, and #(carrier) exceeds what ReachSet x supports.
  ...
```

**Instruction — if the primary provably resists (fallback).**

If `FacingInjective` cannot be established cofinally (it may be false — distinct targets can share a reachable face; this is the charter §9 named crux), then:

- **Keep** the existing `ws4_no_top_facing` but **rename it** `ws4_no_top_cardinal` and rewrite its docstring to state plainly: "No-top via the κ-bound on each object's successor set. This is the Series 3 cardinality wall, inherited, *not* derived from face-structure. The endogenous (face-counting) wall is `ws4_no_top_endogenous`, which holds only under `FacingInjective` (charter §9 crux)." Remove the `noResortToFiat` comment — it is false of this proof.
- **Record in `charter-status.md`:** no-top payoff status → **Partial**. Fractures tracker: change the *verdict cell* (not the target) from "Healed (unconditional endogenous wall)" to "**Inherited (cardinal wall); endogenous wall conditional on facing-injectivity — charter §9 crux, open**." This is the honest split, and it is a valid terminal outcome per charter §7.
- **Do not** delete `FacingInjective` / `ws4_faces_inject`; they are the statement of the open crux, not scaffolding. Mark them "the endogenous route, pending cofinal facing-injectivity."

**Acceptance:** either `ws4_no_top_endogenous` is proved (charter bar met, headline stands), or the workstream reports Partial with `FacingInjective`-cofinality as the precise named obstruction (charter bar honestly not-yet-met). Both are acceptable; the current state — cardinal proof labeled endogenous — is not.

---

## WS3 — composition closure must be built or reported unbuilt.

**Charter/design bar:** faces compose, and the design (`spec/ws03-design.md`, C-unconditional) requires proving composition of faces never yields the empty object — the internal analogue of the WS2 leak being foreclosed.

**What is currently proved:** `ws3_faces_never_annihilate` proves only that a single loop's successor set is nonempty (`(Cofix.dest (loopState q)).1 ≠ ∅`). There is no composition operator in the file. This duplicates `loop_nonAtomic` and does not touch composition.

**Instruction — attempt the charter-strength theorem (primary).**

1. Define a face/label composition operator on `νLk κ Q`: given a state whose successors are themselves labelled states, form the composite (the internal analogue of Series 3 `wqAlg`). The minimal form: compose along one edge, producing the labelled successor structure of the composite.
2. Prove `ws3_faces_never_annihilate` at its intended meaning: if the composed states are each non-atomic, the composite's successor set is nonempty. Because the label is internal (no external `⊥`), the only way to reach empty is for a factor to have been empty — i.e. an atom, already excluded. State this as: composition of non-atomic labelled states is non-atomic, **unconditionally** (no `BotFree`-style hypothesis — that is the internality payoff, and the point of contrast with Series 3 `ws14` which needed the hypothesis).

```lean
def lcomp (t : LkObj κ Q (νLk κ Q)) : νLk κ Q := ...   -- the composite state
theorem ws3_faces_never_annihilate
    (t : LkObj κ Q (νLk κ Q)) (ht : t.1.Nonempty)
    (hmem : ∀ p ∈ t.1, NonAtomic p.2) :
    NonAtomic (lcomp t) := ...
```

**Instruction — if the primary resists (fallback).**

- **Rename** the current theorem `ws3_loop_nonatomic` (it is that, honestly) and note it duplicates `loop_nonAtomic`.
- **Record in `charter-status.md`:** WS3 composition row → **Partial** — "composition operator not built in this pass; non-atomicity of loops proved; unconditional closure is the named open (design C-unconditional), fallback is the Series 3 ws14 `BotFree`-conditional split." Fractures tracker: plurality stays **Healed** (it does not depend on composition); only the composition sub-claim is downgraded.

**Acceptance:** either a real composition operator with the unconditional closure theorem, or an honest Partial that stops claiming "composition stays atom-free (unconditional)" on the strength of a loop-nonemptiness lemma.

---

## WS6 — A1 must cover the interesting case or state its scope.

**Charter bar (§5.3, criterion v):** *no ordinary object wholly knows itself* — the self-face is a proper part, with the blind spot where perspective lives.

**What is currently proved:** `ws6_selfface_proper` covers only `x ∉ str x` (objects that do not self-relate), where the self-face is *empty*. The interesting case — a self-relating, non-spine object whose self-face is nonempty but still misses its outward-only reach — is untouched.

**Instruction — attempt the charter-strength theorem (primary).**

Prove properness for self-relating non-spine objects:

```lean
theorem ws6_selfface_proper_general (x : (νPk κ).X)
    (hself : x ∈ ((νPk κ).str x).1)          -- x does relate to itself
    (hnonspine : ∃ y ∈ ((νPk κ).str x).1, ¬ Reaches x y → False)  -- x's reach exceeds its self-face
    (h : face x x ≠ ReachSet x) :             -- not the improper Ω-spine case
    face x x ⊂ ReachSet x := ...
```
The content: for a self-relating `x` that is not on the improper diagonal, there is a reachable state the inward face omits (something reached only through an outward edge, not through the self-loop), so `face x x ⊂ ReachSet x` strictly. This is the geometric blind spot in the nontrivial case.

**Instruction — if the primary resists (fallback).**

- Keep `ws6_selfface_proper` but **rename** it `ws6_selfface_proper_nonselfrelating` and add to its docstring: "covers the case `x ∉ str x`, where the self-face is empty. The self-relating non-spine case is `ws6_selfface_proper_general` (open)."
- **Record in `charter-status.md`:** A1 row → **Partial** — "proper self-face proved for non-self-relating objects; the self-relating non-spine case is the named open." Do not let the trivial (empty-face) case stand in for the charter's general claim.

**Acceptance:** properness for self-relating non-spine objects, or an explicit scope statement that the current theorem is the trivial case only. A3 is already correctly downgraded to coexistence (`ws6_blindspot_nonempty`) with equality flagged open — leave that as is; it is honest.

---

## WS7 — the verdict's distinctness anchor must cover its claimed scope.

**Charter bar (§4 WS7, §8):** the verdict *one finitude, substantively* requires that the payoffs are **distinct consequences** of the finitude of facing — not one deduction restated. The distinctness must be the objective anchor (T3), at the scope the verdict claims.

**What is currently proved:** `ws7_deductions_dont_collapse` shows only that the *two incompleteness* deductions (off-diagonal proper, on-diagonal improper) cannot share a witness. The other four payoffs' mutual distinctness is asserted in a comment, not proved. So a six-way "substantively distinct" verdict rests on a two-way anchor.

**Instruction — attempt the charter-strength theorem (primary).**

Extend the distinctness anchor to the scope the verdict claims. For each pair of payoffs, exhibit that they are consequences of *different* clauses of `FinitudeOfFacing` (or apply to different states / use different intermediate lemmas), so no two collapse into one deduction:

```lean
/-- Each payoff's deduction uses a distinct consequence of FinitudeOfFacing.
    Anchor: exhibit, for each pair, a state or clause distinguishing their deductions. -/
theorem ws7_deductions_pairwise_distinct (hinf : ℵ₀ ≤ κ) :
    -- plurality lives on νLk (labelled), the others on νPk — different carriers;
    -- no-top is a universal ¬∀, incompleteness-off is an existential ⊂ per state;
    -- on-diagonal uses improperness, off-diagonal uses properness (the existing T3);
    -- endogenous-bound-on-spine is the improper Ω, distinct from the proper off-spine.
    ... := ...
```
Minimum bar: a proof (even a structural/enumeration one) that the six deductions do not pairwise factor through a common lemma. The two-way incompleteness case (`ws7_deductions_dont_collapse`) is one row of this; supply the rest.

**Instruction — if the primary resists (fallback).**

- Keep `ws7_deductions_dont_collapse` and **restate the verdict's scope honestly** in the docstring of `ws7_verdict` and in `charter-status.md`: "Verdict: one finitude, substantively — the distinctness anchor is **proved for the two incompleteness deductions** (`ws7_deductions_dont_collapse`); pairwise distinctness across all six payoffs is asserted structurally but mechanized only for the incompleteness pair. Full six-way anchor is the named open."
- The verdict value `ws7_verdict := oneFinitude` may stand **only** if the reduced scope is stated wherever the verdict is reported. If it cannot be honestly stated, the verdict reports **Partial**: "one finitude, substantively, anchored partially."

**Acceptance:** either the pairwise-distinctness anchor at six-payoff scope, or the verdict explicitly scoped to the distinctness actually proved. The verdict must not read as fully earned while its anchor covers 2 of 6.

---

## Cross-cutting — the axiom check is unrun; mark it static.

**Charter/protocol bar:** no "sorry-free / axiom-free" claim without a machine-checked `#print axioms` against a pinned Lean/Mathlib, with commit hash and clean-build log.

**What is currently the case:** `AxiomCheck.lean` contains the `#print axioms` lines for all 34 headline theorems, but there is no committed build log, and the claim "builds sorry-free, no custom axioms (34 theorems)" in `charter-status.md` rests on a source audit only.

**Instruction.**

1. Run `cd lake && lake build` against the pinned toolchain; run the `AxiomCheck.lean` targets; capture the output.
2. If clean: commit the build log, cite the commit hash, and only then remove the *(static)* qualifier.
3. Until then: **edit `charter-status.md`** to mark every "axiom-clean / sorry-free" assertion **_(static — source audit only; `#print axioms` not yet run in a pinned build)_**. This is a status correction, not a charter change.

**Acceptance:** the status file distinguishes source-audited from machine-verified. No headline may claim axiom-cleanliness as machine-fact until the log exists.

---

## What must NOT change

- `charter.md` — not one word. If a bar cannot be met, that is a Partial in the status file, not a charter edit.
- The success criteria (§8) and the fractures tracker's **target** column — fixed. Only the **verdict/status** columns move, and only to reflect what is actually proved.
- The pre-registered outcome classes — a sharp Impossibility (e.g. WS5's global collapse) stays a success; do not weaken it into a caveat.

## Summary of required status-file corrections (once the above is done)

| Payoff / row | Current status-file claim | Honest claim after this pass |
|---|---|---|
| No-top (WS4) | Healed — unconditional endogenous wall | Endogenous wall proved (if primary lands) **or** Inherited cardinal wall + endogenous conditional on facing-injectivity (Partial) |
| Composition (WS3) | Discharged, unconditional | Composition operator built + closure (if primary) **or** Partial: loops non-atomic, closure open |
| Incompleteness off-diagonal (WS6 A1) | Discharged | Proper self-face for self-relating non-spine (if primary) **or** Partial: proved for non-self-relating case only |
| Verdict anchor (WS7 T3) | One finitude, substantively (six payoffs) | Six-way distinctness anchor (if primary) **or** verdict scoped to the two-way anchor proved |
| Axiom check (all) | Sorry-free, axiom-clean, 34 theorems | Same, marked *(static)* until `lake build` + log committed |

*These instructions reconcile code to charter without moving goalposts. Each item names the charter-strength target first and an honest Partial second; the charter itself is untouched throughout. No em dashes in final academic paper copy; these working instructions are not final copy.*
