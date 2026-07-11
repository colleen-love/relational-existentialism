# WS2 — The Static Collapse, and the forced answer

**Design doc. Series 06, the intellectual spine. Owns: the Static Collapse Theorem in its genuine-atomlessness form (any static, genuinely globally atomless construction is a subsingleton), the diagnosis that every static plurality is bought by an imported atom (`νLk`'s labels, the tower's index), the precise definitions of "static" and "no imported atom", and the forced-answer claim that dynamism is the escape.**

*Series 06 is standalone; upstream names transcribed into `series-06/formal/ws2.lean`, re-namespaced `Series06.WS2` (see `spec/README.md` §5).*

## The object at stake

The charter's hinge (§3): the two prior motivating impossibilities — Parmenides (Series 04) and Explosion (Series 05) — are one theorem read at full generality. A *static* world is its behavior; *genuine* global atomlessness erases every behavioral distinction; so a static, genuinely-atomless world is a point. The design question is how to state this at a breadth that (a) subsumes the plain-carrier collapse (`ws2_collapse`), (b) **diagnoses the apparent escapes as imports** — the labelled loops of `νLk` and the tower's index each carry plurality only by an atom moved out of the carrier — and (c) grounds the forced-answer claim (dynamism, endogenous time, is the unique non-importing escape), without a circular or vacuous definition of "static" and "no imported atom."

**Ambient theory.** `spec/README.md` §2/§5. The theorem lives on the finished objects: `νPk` (plain), `νLk` (labelled), and the Series 05 tower colimit `Winf`. The escape (WS1) is `Proc`, which is *not* one of these.

## Candidates (for the statement of the collapse)

### C1 — Plain-carrier only (`νPk`), cite Series 04 verbatim

```lean
theorem ws2_static_collapse_plain (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X
  := ws5_global_groundless_collapses hinf h        -- transcribed Series 04
```
- **Success:** the collapse holds on `νPk`.
- **Failure mode:** **too narrow.** Says nothing about `νLk` or the tower, so it does not diagnose *why* the prior series' pluralities are not counterexamples — the reader can point at `ws3_plurality_core` and think the charter refuted.

**Paper triage.** True and transcribed, but it is the *instance*, not the theorem. Retain as the base case; it cannot be the whole WS2, or the charter's breadth claim is unearned.

### C2 — Abstract static object + genuine atomlessness (the intended breadth)

```lean
/-- A **static construction**: a type with a coalgebra structure whose behavioral
    equivalence is identity (bisimulation = identity). Covers νPk, νLk, and the
    tower colimit as instances. -/
structure Static where
  X       : Type u
  dest    : X → PkObj κ X
  bisim_id: ∀ R, Bisim dest R → ∀ x y, R x y → x = y     -- behavioral identity

/-- **No imported atom**: the distinction between objects is carried by the relating
    itself — there is no injection from an external atom-set (a label alphabet, an
    index) into the ways objects differ. Formalised as: the behavioral quotient has
    no more points than the hereditarily-nonempty core, i.e. every distinction is
    a descent distinction. -/
def NoImportedAtom (S : Static) : Prop := ...

theorem ws2_static_collapse (S : Static) (hgen : GenuinelyAtomless S) :
    Subsingleton S.X
```
- **Success:** one theorem, `νPk`/`νLk`/tower all instances; the labelled loops fail `GenuinelyAtomless` (their distinction is an imported label), so they are not counterexamples.
- **Failure mode:** **circularity / vacuity of `NoImportedAtom`.** If `GenuinelyAtomless` is defined *as* "behaviorally distinguished with no leaf", the theorem risks being `ws2_collapse` wearing a structure, and the diagnosis of `νLk` risks being "true because we defined the escape out." The definition must be independently motivated and *checkable against `νLk`*.

**Paper triage.** The intended shape. Its whole weight is on a **non-circular `NoImportedAtom`** that provably *fails* for `νLk` and the tower (so the diagnosis is a theorem, not a stipulation). Decidable-on-paper test below. **Winner, conditional on the definition passing that test.**

### C3 — Behavioral-quotient functor form (any `F`, any behaviorally-identified object)

```lean
-- for an arbitrary bounded functor F, the terminal F-coalgebra restricted to its
-- hereditarily-nonempty core is a subsingleton whenever F has "no imported atom slot"
```
- **Failure mode:** **over-general / unbuildable.** Quantifying over arbitrary `F` needs a general accessibility/finality apparatus Series 06 does not build; and "no imported atom slot" for arbitrary `F` is exactly the label-vs-no-label distinction, which is clean only for powerset-shaped `F`.

**Paper triage.** The honest ceiling (the charter's "fully general characterization of static"). **Reject as the built target; state it as the pre-registered heuristic** (charter §9: the forced-answer general form may resist proof). C2 over powerset-shaped statics is the built floor.

## Winning candidate: C2 (abstract `Static` + non-circular `GenuinelyAtomless`), with C1 as base case and C3 as heuristic ceiling

### The load-bearing definition, and its decidable test

`GenuinelyAtomless S := HereditarilyAtomless S ∧ NoImportedAtom S`, where:

- `HereditarilyAtomless S := ∀ x, HereditarilyNonempty (S.dest) x` — no leaf anywhere (transcribed shape).
- `NoImportedAtom S := ` **the ways two objects can differ are exhausted by descent** — formally, there is no set `L` with `2 ≤ #L` and an injection `L ↪ S.X` whose image is a set of pairwise-non-bisimilar-yet-behaviorally-identical-below-the-top objects. Concretely for powerset-shaped statics: *the distinction is not carried by a first-level label coordinate.*

**The decidable-on-paper test (the diagnosis).** `NoImportedAtom` must **provably fail** for `νLk`:
```lean
theorem ws2_escapes_are_imports (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ¬ NoImportedAtom (staticOfNuLk κ Q)        -- the labelled loops import a label
  ∧ ¬ NoImportedAtom (staticOfTower ...)       -- the tower imports an index
```
The `νLk` half is `ws3_plurality_core` read correctly: `loopState q₁ ≠ loopState q₂` are hereditarily nonempty *and behaviorally identical except for the label coordinate `q`* (same bare successor shape, `ws3_same_succ_diff_face`), so their distinction factors through the injection `Q ↪ νLk` — exactly an imported atom. The tower half: `Winf`'s plurality across levels factors through the index injection. **If this theorem is provable, `GenuinelyAtomless` is non-circular** (it is refuted by a real construction, not by fiat), and the charter's diagnosis is earned. **This is the single decidable check WS2 stands on**; it is the strip test applied to the *impossibility*.

### The theorem and subsumptions

```lean
theorem ws2_static_collapse (S : Static) (hgen : GenuinelyAtomless S) : Subsingleton S.X
theorem ws2_subsumes_parmenides (hinf : ℵ₀ ≤ κ) :
    GenuinelyAtomless (staticOfNuPk κ) → Subsingleton (νPk κ).X          -- C1 as instance
theorem ws2_subsumes_tower (T) : GenuinelyAtomless (staticOfTower T) → Subsingleton (Winf T)
```
*Strategy:* the core is `ws2_collapse`'s bisimulation argument abstracted over `Static.bisim_id`: `HereditarilyAtomless` makes the maximal relation a bisimulation, `bisim_id` collapses it. `NoImportedAtom` is *not consumed by the collapse proof* — it is the hypothesis that makes the theorem non-vacuous by ruling out the `νLk` escape, and its role is entirely in `ws2_escapes_are_imports`. So the collapse is `ws2_collapse` generalized; the novelty is the *diagnosis* that pins the escapes as imports. *Paper-decidable:* the collapse is the transcribed argument; the diagnosis is `ws3_plurality_core`/`ws3_same_succ_diff_face` read as a factoring-through-`Q`.

### The forced answer

```lean
/-- Dynamism is the escape: `Proc` (WS1) is genuinely atomless (no imported atom —
    no label alphabet) yet plural (WS6), so it satisfies the antecedent's atomlessness
    without being static, hence without collapsing. -/
theorem ws2_forced_answer (hinf : ℵ₀ ≤ κ) :
    (∀ S : Static, GenuinelyAtomless S → Subsingleton S.X)      -- static ⇒ collapse
  ∧ (¬ IsStatic (Proc κ) ∧ GenuinelyAtomlessProc (Proc κ) ∧ Plural (Proc κ))  -- Proc escapes
```
*Strategy:* first conjunct is `ws2_static_collapse`; second consumes WS1 (`Proc` is not a finished behaviorally-identified object — `ws1_no_collapse`), WS6 (genuinely atomless and plural — `ws6_atomless_and_plural`), so the escape is *exhibited*, not merely asserted. **Essential-uniqueness** (that *every* non-importing escape is dynamic) is the heuristic ceiling (C3), pre-registered as defended-not-proved per charter §9. *Paper-decidable:* the dichotomy is a conjunction of an abstracted transcribed theorem and the WS1/WS6 exhibition.

## Outcome classes (per charter §7)

- **Impossibility proved (success):** `ws2_static_collapse` (genuine-atomless statics collapse) + `ws2_escapes_are_imports` (the diagnosis). The motivating engine, as Parmenides/Explosion were.
- **Discharged:** the two subsumptions; the forced-answer dichotomy.
- **Partial (pre-registered):** essential-uniqueness of the forced answer left heuristic (C3 ceiling), exactly as Series 04/05 left theirs; and `NoImportedAtom` stated for powerset-shaped statics, not arbitrary `F`.
- **Failure to watch:** if `ws2_escapes_are_imports` is *not* provable — if `νLk`'s loop distinction cannot be shown to factor through `Q` — then `GenuinelyAtomless` is circular and the breadth claim collapses to C1 (plain carrier only). This is the SERIOUS finding the review must probe.

## Deliverable

`series-06/formal/ws2.lean`: transcribed `ws2_collapse`, `ws5_global_groundless_collapses`, `ws3_plurality_core`, `ws3_same_succ_diff_face`, the tower `Winf`; `Static`, `HereditarilyAtomless`, `NoImportedAtom`, `GenuinelyAtomless`; `ws2_static_collapse`, `ws2_escapes_are_imports`, `ws2_subsumes_parmenides`, `ws2_subsumes_tower`, `ws2_forced_answer`; the C3 general-`F` ceiling typed but unbuilt. Axiom check: `#print axioms ws2_static_collapse` on the standard three.
