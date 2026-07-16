# Relational Existentialism — Series 07

**The import theorem: why atomless plurality is impossible, so every relational world that holds more than one thing must pay for the plurality with an atom — a permanent leaf, an imported label, an index, a weight, or a transient leaf healed only in the limit.**

*Working draft, Revision 0. Series 07 is self-contained: it states its own question, proves its own theorem from scratch. Series 06 is prior art that informs the design — the way Series 05 informed Series 06 — but nothing here presupposes it. A reader who has never seen Series 06 should be able to follow this charter end to end.*

---

## 1. The one-paragraph version

The program has built four relational worlds that hold more than one thing, and every one of them paid for its plurality by importing something. Series 03 imported weights; Series 04 imported labels, reified as the face; Series 05 imported an index of levels; and Series 06, refusing all three, tried to buy plurality with endogenous time — and found the purchase failed, its process collapsing to a single point moment by moment. Series 07 proves why, in one theorem, and turns the whole program's recurring pushback into a result. **Atomless plurality is impossible without an import.** Precisely: over the plain relating (the unlabelled bounded-powerset functor), any construction faithful to "an object is its relating" in which every object is genuinely atomless — hereditarily non-empty, at every object and every moment — has at most one object. The engine is a single short lemma, and it is more general than any collapse the program has proved before: **atomless behavior is unique.** On *any* plain coalgebra, not merely the terminal one, all hereditarily-non-empty states are bisimilar, because everything atomless relates to everything atomless — the relation "both are atomless" is itself a bisimulation. So the only distinguisher a groundless world has is a leaf, an atom reached by descent; genuine atomlessness removes every leaf; and difference has nowhere left to live. The only ways to restore a distinguisher are the four the program already discovered, and the theorem proves they are the *only* four: import a label, an index, or a weight — an atom moved outside the carrier — or relax atomlessness to hold only in the limit, letting transient leaves at finite stages carry the difference and heal above. There is no third kind of distinction, and dynamism supplies none, because atomless moments are unique. The theorem is the capstone that reads the entire program backward: the import was never a failure of nerve or ingenuity. It was forced. Every relational world that holds more than one thing must pay for the plurality with an atom, and the only freedom is *which* atom, and whether you are honest that you paid.

That is the whole story. The rest of this charter makes each step precise and lays out the work.

---

## 2. What we are trying to prove

Series 07's deliverable is not an object but a **theorem** (with its sharp scope and its honest loophole). Four ingredients are in tension, and the claim is that they are jointly unsatisfiable:

1. **Plain relating.** The world is built over the plain, unlabelled functor `F X = P_κ X` — relating only, with no imported coordinate (no label alphabet `Q`, no weight algebra, no external index) riding alongside the relation. This is the honestly atom-free type (Series 06 §3): a bare label or weight is an atom moved out of the carrier into an alphabet.
2. **An object is its relating.** Identity is behavioral: two objects are equal exactly when they relate alike, all the way down (bisimulation is identity). This is the founding principle of the whole program (point 1 of every prior charter), what makes "the object *is* its pattern of relating" exact.
3. **Genuine global atomlessness.** Every object is hereditarily non-empty — it relates to something, and everything it relates to relates to something, without end — and, for a dynamic construction, this holds at *every moment*, not merely in a limit. No leaf anywhere, ever.
4. **Plurality.** There is more than one object.

> **The claim (target of WS2).** *Ingredients 1, 2, and 3 together force the negation of 4: a plain, behaviorally-identified, genuinely-atomless world is a subsingleton. Equivalently, plurality requires dropping one of 1–3 — importing a distinguisher (drop 1), abandoning behavioral identity (drop 2), or relaxing atomlessness to the limit (drop 3). There is no fourth ingredient to drop, and no way to keep all three and still be plural.*

The canonical inhabitant remains the self-relating point

> **Ω = {Ω}**,

now cast as the *unique* atomless behavior — the single point every genuinely-groundless world collapses onto, the fixed content of "everything atomless relates to everything atomless."

The tension is that 1–3 are exactly the three commitments the program has most wanted to keep *together*, and every prior series kept only two: it dropped 1 (Series 03's weights, Series 04's labels, Series 05's index), or it kept all three and lost 4 (Series 06's process, which collapsed), or — the one untried escape — it drops 3 to the limit (the metric route). Series 07 proves that this menu is complete.

---

## 3. The collapse: atomless behavior is unique

This section is the hinge of Series 07. Everything afterward is a response to it, and it is a single lemma read at a generality the program has not used before.

### 3.1 The lemma

> **Atomless-behavior-is-unique (target of WS1).** *On any plain coalgebra `c : X → P_κ X` — not only the terminal one — any two hereditarily-non-empty states are bisimilar.*

The proof is one relation and one line. Let `R x y` hold exactly when `x` and `y` are both hereditarily non-empty. Then `R` is a bisimulation: if `R x y`, then `c x` is non-empty and every successor of `x` is again hereditarily non-empty, and likewise for `y`, so any successor of `x` can be matched to *any* successor of `y` (all of them are hereditarily non-empty, so `R` holds of the pair), and symmetrically. A bisimulation whose field is "everything atomless" — hence all atomless states share one behavior. That behavior is Ω's.

This is the Parmenides collapse (Series 04 `ws2_collapse`) with its terminality assumption stripped out. `ws2_collapse` concluded *equality* on the terminal coalgebra; the lemma concludes *bisimilarity* on an arbitrary one, which is strictly more general and is what lets the theorem reach dynamic constructions.

### 3.2 From the lemma to the impossibility

Add ingredient 2 (behavioral identity: bisimulation implies equality) and the collapse is immediate: all hereditarily-non-empty states are bisimilar (§3.1), hence equal, hence there is at most one. This recovers the program's two existing collapses as instances of one theorem:

- **Static instance.** On the terminal coalgebra `νPk`, the hereditarily-non-empty core is a subsingleton (Series 04 `ws2_collapse` / `ws5_global_groundless_collapses`).
- **Dynamic instance.** On the stagewise process over `νPk`, the *unique* productive thread is Ω (Series 06 `ws1_productive_unique`, `ws1_no_productive_plurality`) — the collapse reaching into every founded approximation, because an atomless founded stage cannot branch (its atomless children are unique, and sets deduplicate).

The lemma is the common root: whether the world is a finished object or a process of approximations, the atomless part of it has exactly one behavior, and behavioral identity turns "one behavior" into "one thing."

### 3.3 What the collapse means

The lemma is not a technical convenience; it is a **discovery about difference in a groundless world**, and it dictates the shape of everything after:

> **Difference must be bought.** In a world that is nothing but relating, the only distinction two objects can have is a leaf — a place where descent bottoms out differently. That leaf is an atom. Genuine atomlessness forbids leaves, so it forbids difference, so it forbids plurality — *unless* the difference is supplied from somewhere that is not the relating. Every such "somewhere" is an import: a label, an index, a weight, or the transient leaves of an unfinished limit. Plurality is never given by a groundless world; it is always **bought**, and the price is an atom.

So the four prior worlds are not four different achievements; they are four different *purchases*. The task is to prove the price list is complete.

---

## 4. The false escapes: every world drops exactly one ingredient

The natural attempts to have 1–4 all at once each quietly drop one of 1–3. Cataloguing them is not a survey; it is the body of the theorem, because the claim is precisely that *every* plurality drops one, so naming the ways is naming the price list.

### 4.1 Drop 1 — import a distinguisher (weights, labels, levels)

Series 03 hung a **weight** on each relation; Series 04 a **label**, reified as the face `a↾(a,b)`; Series 05 an **index** of levels. Each restores difference by adding a coordinate the relating does not carry — a weight algebra, a label alphabet `Q`, an ordinal index — and each coordinate is an atom moved out of the carrier and into an external set. Series 04's own labelled loops are the sharpest case: `loopState q₁ ≠ loopState q₂` are hereditarily non-empty and distinct, but distinguished *only* by `q ∈ Q` (`ws3_plurality_core`, `ws3_same_succ_diff_face`), so their difference factors through the injection `Q ↪ νLk` — an imported atom, exactly. *The purchase: plurality, paid for with an imported atom. Honest, and forced.*

### 4.2 Drop 2 — abandon behavioral identity (keep intensional ghosts)

One could refuse ingredient 2 — let two objects that relate identically still count as different, by fiat, carrying a distinction invisible to the relating. But a distinction invisible to the relating is, by definition, not carried by the relating; it lives in the ambient encoding (which set-theoretic object you happened to use), which is an import in disguise, or it is the intensional *history* of the object — and Series 06 proved the history collapses under atomlessness (all atomless histories are Ω's). *The purchase fails: dropping behavioral identity either re-imports (drop 1 relabelled) or buys nothing, because the only intensional invariant is the history, and atomless histories are unique.*

### 4.3 Drop 3 — relax atomlessness to the limit (transient leaves)

The one escape that is neither an import nor a collapse: let the finite stages of a process carry leaves — genuine atoms — and demand atomlessness only of the refused limit. The metric / Cauchy route lives here: distinct sequences of leafy approximations, all converging to the unique atomless Ω, distinct because their finite (atom-bearing) stages differ. *The purchase: plurality, paid for with transient atoms — leaves at every finite stage, healed only in a limit the world never reaches.* Whether this *counts* as an atomless plural world, or is import-in-time wearing the costume of a limit, is the honest fork WS5 must adjudicate. It is a real relaxation of ingredient 3, not a hole in the theorem.

### 4.4 What the catalogue must show

The catalogue is the theorem's teeth: to prove 1–3 force ¬4, it is not enough to collapse the plain world (§3); one must show that *every* restoration of plurality is one of §4.1–§4.3 — an import (drop 1), an intensional ghost that re-imports or collapses (drop 2), or a limit-relaxation (drop 3). That completeness is the **trichotomy of distinction** (WS3), and it is what turns a collapse theorem into an impossibility theorem.

---

## 5. The theorem, its scope, and its one honest loophole

### 5.1 The theorem

> **The Import Theorem (target of WS2, proved via WS1 and WS3).** *No construction satisfies all four of: (1) plain relating, (2) behavioral identity, (3) genuine every-moment atomlessness, (4) plurality. Any three are satisfiable; all four are not. Consequently every plural relational world drops exactly one of (1)–(3), and the drop is its price: an imported atom (drop 1), an intensional distinction that reduces to an import or to the unique history (drop 2), or transient atoms healed only in the limit (drop 3).*

### 5.2 The trichotomy that makes it exhaustive

The impossibility is airtight only if §4's catalogue is *complete* — if every possible distinguisher between two objects is a leaf, an import, or an intensional-history difference, with no fourth kind. WS3 owns this:

> **Trichotomy of distinction (target of WS3).** *Any distinction between two objects of a plain construction is (i) a leaf — a descent difference, i.e. an atom, forbidden by (3); (ii) an import — a coordinate not carried by the relating, forbidden by (1); or (iii) an intensional-history difference — which under atomlessness collapses (Series 06), and otherwise is (i) or (ii) in disguise. There is no fourth kind, because anything beyond the observational history is, by definition, not carried by the relating, hence an import.*

### 5.3 The scope, stated honestly

Two boundaries are load-bearing and named now, because the theorem is true only inside them.

- **Every-moment, not limit.** Ingredient 3 must be *every-moment* atomlessness. Under the weaker *limit* atomlessness the theorem is false — that is exactly the §4.3 escape. The theorem's strength and its one loophole are the same clause, and WS5 draws the line.
- **The provable core versus the universal thesis.** The provable core is the coalgebraic lemma (WS1, covering every plain coalgebra) plus the process instance (Series 06, transcribed) plus the trichotomy (WS3). The fully universal "*any construction whatsoever* faithful to relating" is not a formalizable quantifier — "construction" cannot be exhaustively ranged over — so the universal form is a **defended thesis**, exactly as the program's forced-answer claims (Series 04's essential-uniqueness of restriction-quality, Series 05's of the tower) were always marked heuristic beyond their mechanized core. WS6 owns the boundary; reporting the universal as heuristic, if it resists, is required.

### 5.4 What the theorem buys, beyond the collapse

- **The program, explained (the capstone).** Weights, labels, levels, and the failed time are one phenomenon: each is a drop of one ingredient, forced by the theorem. The recurring "honest negative" of every prior series — that the import could not be removed — was not a limitation of the construction; it was this theorem, unproved. *(WS4.)*
- **The one real escape, characterized.** Limit-atomlessness is isolated as the sole way to keep plain relating and plurality, at the price of transient atoms — and adjudicated as either a genuine (if modest) achievement or an import-in-time. *(WS5.)*
- **A clean statement of what a groundless world can and cannot be.** It can be atomless, or plural, or behavioral-identity-faithful over plain relating — any two — but not all three at once. That trilemma is the sharpest single thing the program can say about relation-first ontology. *(WS2, WS7.)*

### 5.5 The honest hazards, named at the outset

- **Circularity — the signature risk.** The theorem could be true only because "genuinely atomless / no import" was *defined* to exclude exactly the escapes. This is the one way Series 07 fails as a result while succeeding as a proof. The defense is that ingredients 1 and 2 are **independently motivated** — the plain functor and behavioral identity are the founding commitments of the whole program, not gerrymandered for this theorem — and that the escapes are refuted as *theorems* (νLk *provably* carries a label coordinate; the tower *provably* carries an index), not ruled out by fiat. WS2 and WS7 must make the non-circularity explicit, or the theorem is a tautology dressed as a discovery.
- **The trichotomy may leak (WS3).** If there is a fourth kind of distinction — a distinguisher that is neither leaf, nor import, nor history — the impossibility is not exhaustive and reverts to a mere collapse-plus-examples. The trichotomy's completeness is the hardest genuinely-open part.
- **The loophole may be the real world (WS5).** If limit-atomlessness with transient atoms is judged a legitimate atomless plural world, the headline weakens from "impossible" to "impossible except in the limit" — still a strong result, but a different one. This is a real possible outcome, not a failure.
- **The universal may be only heuristic (WS6).** "Any construction faithful to relating" may resist formalization, leaving a defended-but-not-universally-proved thesis, as every prior forced-answer claim did.

---

## 6. Workstreams

Seven workstreams. WS1 proves the engine; WS2 states and proves the theorem; WS3 makes it exhaustive; WS4–WS5 catalogue the drops and the loophole; WS6 draws the heuristic boundary; WS7 audits against circularity and returns the verdict.

- **WS1 — Atomless behavior is unique.** Prove the general lemma (§3.1): on any plain `P_κ`-coalgebra, hereditarily-non-empty states are bisimilar, via the "both-atomless" bisimulation. Recover Series 04 `ws2_collapse` and Series 06 `ws1_productive_unique` as instances of the one lemma. *Blocking; the engine. Transcribes the `P_κ` / bisimulation machinery from Series 04/06.*

- **WS2 — The Import Theorem, and its non-circularity.** State ingredients 1–4 precisely and prove 1∧2∧3 ⇒ ¬4 (§5.1), for static and dynamic constructions, from WS1 plus behavioral identity. Prove the **non-circularity**: ingredients 1 and 2 are the program's founding commitments (independently motivated), and the prior pluralities are refuted as imports by *theorem* — `νLk` carries a label coordinate, the tower an index, weights an algebra — not excluded by a rigged definition of "atomless." *The spine.*

- **WS3 — The trichotomy of distinction.** Prove every distinction is a leaf, an import, or an intensional-history difference (§5.2), and that the third collapses under atomlessness (transcribe Series 06's `ws1_productive_unique`) or reduces to the first two. **Coincidence duty:** the three kinds are genuinely distinct and jointly exhaustive, not a definitional partition — the completeness is the theorem's teeth, and its failure is a named open.

- **WS4 — The imports catalogued: the program explained.** Exhibit weights (Series 03), labels/faces (Series 04), and levels (Series 05) each as the specific ingredient-1 drop its series relied on, and show the Import Theorem *predicts* each — that the series succeeded at plurality exactly by, and only by, importing. This is where Series 07 pays back the whole program: the recurring honest negative was this theorem all along. *Interpretive spine; light on new Lean, heavy on the unification.*

- **WS5 — The limit-atomlessness loophole.** Characterize the sole escape (§4.3, §5.3): relaxing ingredient 3 to the limit, with transient atoms at finite stages (the metric / Cauchy route). Prove it necessarily reintroduces leaves at finite stages (so it is a relaxation, not a counterexample), and **adjudicate honestly** whether "atomless in the limit, plural via transient atoms" is a genuine atomless plural world or import-in-time. Pre-registered fork; either verdict is terminal and valid.

- **WS6 — The heuristic ceiling.** Draw the line (§5.3) between the provable core (coalgebras + the process instance + the trichotomy) and the universal "any construction faithful to relating." Attempt the universal; report it **heuristic** if "construction" resists formalization, exactly as Series 04/05 reported their forced answers. *Owns the honest boundary of the claim.*

- **WS7 — The anti-circularity audit.** The signature risk is not trivialization but **circularity**: the theorem true because the definitions excluded the escapes. Verify ingredients 1–2 are independently motivated and the escapes refuted as theorems (WS2), and that the trichotomy (WS3) is not a definitional partition. Deliver the typed verdict — **`importForced`** (the strong result: plurality demonstrably requires an import, non-circular), **`payoffsEstablished`** (the theorem holds and its scope is honest, but the universal or the trichotomy stays partial), or **`Circular`** (the definitions were rigged — a sharp negative about the result, honestly returned). Returning `Circular` honestly is a success in the program's sense.

---

## 7. Methodology and outcome vocabulary

The deliverable is a theorem, so **the central result is itself an Impossibility** — and impossibilities are first-class successes in this program (the Parmenides collapse, the Explosion Dilemma, the Static Collapse all did the real work). Each ingredient becomes a precise definition; the theorem is proved from the lemma; the escapes are catalogued and each shown to drop a named ingredient.

Each workstream obligation is **Discharged** (proved), **Impossibility proved** (a sharp negative — a success), **Partial** (part proved, obstruction precise), or **Failed** (documented why). Series 07 inherits the program's two disciplines, re-pointed at an impossibility:

> **The non-circularity rule (replacing the coincidence rule).** No ingredient of §2 may be *defined* so as to exclude the escapes it is meant to rule out. "Genuine atomlessness" is hereditary non-emptiness (independently motivated); "plain relating" and "behavioral identity" are the program's founding commitments. Each escape must be refuted as a theorem (it *provably* imports), never by a definition that assumes the conclusion. An ingredient that only excludes an escape by fiat is reported **Circular** for that escape, with the non-circular refutation as the named open.

> **The strip test (inherited).** Delete the load-bearing word — "atomless", "plain", "import" — and check whether the theorem still goes through, or whether it silently used a rigged definition. WS3/WS5/WS7 carry the annotations; WS7 aggregates.

And the outcome the ordinary vocabulary cannot express: **Circular**, the finding that the theorem is a tautology of its definitions rather than a discovery about relating. WS7 owns it; returning it honestly is a program success.

---

## 8. Success criteria

Success is a single theorem — the Import Theorem — that provably:

(i) collapses any plain, behaviorally-identified, genuinely-atomless construction to a subsingleton, via the general lemma (WS1), recovering the static (`ws2_collapse`) and dynamic (`ws1_productive_unique`) collapses as instances; (ii) is **non-circular** — the ingredients independently motivated, the escapes refuted as theorems (WS2); (iii) is **exhaustive** — every distinction a leaf, an import, or a collapsing history (the trichotomy, WS3); (iv) **explains the program** — weights, labels, levels each the forced ingredient-1 drop of their series (WS4); (v) **isolates the one loophole** — limit-atomlessness with transient atoms, adjudicated (WS5); and (vi) draws its **honest scope** — the provable core versus the heuristic universal (WS6).

Against the central question, success takes one of these shapes, all valid:

- **The theorem stands, non-circular and exhaustive (headline positive).** `importForced` (WS7): atomless plurality is impossible without an import, demonstrably and not by definition.
- **The theorem stands with an honest boundary.** The core is proved and its scope drawn, but the trichotomy's completeness or the universal quantifier stays partial (`payoffsEstablished`), or the limit-loophole is judged a genuine escape (headline weakens to "impossible except in the limit"). Each is terminal and valid.
- **The verdict, either way (WS7).** *Import forced, substantively* — or *Circular*, the finding that the impossibility was baked into the definitions. Both are successes; the second is a sharp negative about the result.

> **The characteristic risk, stated plainly.** Series 07's danger is not that it fails to prove the theorem but that it proves a **tautology** — that "atomless" and "no import" were defined to make plurality impossible, so the theorem says nothing about relating that the definitions did not already say. The criteria are written so that **catching that** (WS7's `Circular`) counts as success, not concealment. A theorem that could only be proved would prove nothing.

---

## 9. Open problems and honest risks

- **Circularity (the signature risk).** That the theorem is true by construction of its definitions. The non-circularity rule (§7) and WS7 exist to catch it, but the judgment that ingredients 1–2 are "independently motivated" rather than gerrymandered is itself a per-ingredient call that could be got wrong. Cannot be fully retired in advance; it is what the program tests.
- **The trichotomy may not be exhaustive (WS3).** A fourth kind of distinction would demote the impossibility to a collapse-plus-examples. The completeness proof is the hardest genuinely-open piece; an honest Partial if a candidate fourth kind resists classification.
- **The loophole may be the real achievement (WS5).** If limit-atomlessness with transient atoms is a legitimate atomless plural world, the headline is "impossible except in the limit," and the program's positive future is the metric route, not a fifth impossibility. A real and reportable outcome.
- **The universal may be only heuristic (WS6).** "Any construction faithful to relating" may resist a formalizable quantifier, leaving the strong claim defended but not universally proved — as every forced-answer claim before it.
- **Interpretive gap (permanent).** Whether this theorem says something about *the* relational world or about a faithful mathematical model of it is a philosophical question to frame, not a theorem to prove. Proving that difference must be bought narrows the gap — the model now carries the price of plurality in its very type — but does not close it.

---

## 10. Positioning

Philosophically: the theorem is the program's Parmenides result at full strength — "difference must bottom out somewhere" (Series 04 §3) generalized from one carrier to *every* construction faithful to relating, so that the One is not an accident of a particular world but the fate of any groundless world that refuses to import. It sharpens the "relations without relata" objection to radical ontic structural realism (Ladyman & Ross, French): a world of pure structure with no atom *and* more than one node is not merely suspicious, it is impossible — structure-without-relata cannot be plural unless it smuggles a relatum back as an import. It gives the Buberian I-Thou a mathematical edge (the two-sidedness that would distinguish a Thou is exactly an imported face), and it reads the special-sciences "no fundamental level" debate (Schaffer's infinitism) as forced to choose: infinite descent *or* plurality, not both, unless each level imports its own distinctions. Formally: universal coalgebra and the theory of bisimulation (Aczel; Rutten, Jacobs), where the "both-atomless" bisimulation is the whole engine; final-sequence and behavioral-metric arguments (Adámek, Barr; the Lawvere-enriched behavioral distance) for the limit-atomlessness loophole; and the program's own four collapses (`ws2_collapse`, `ws5_global_groundless_collapses`, Series 06's `ws2_static_collapse` and `ws1_productive_unique`) as the instances the one lemma unifies. The distinctive claim of Series 07, in one line: **a relational world can be atomless, or plural, or faithful to "an object is its relating" over plain relating — any two of the three, never all three — so every world that holds more than one thing has already, somewhere, paid for it with an atom, and the only honesty is to say which.**

*Working draft, Revision 0: the program document before any workstream has reported. §1 gives the whole argument in a paragraph; §§2–5 walk it — the four ingredients in tension, the one lemma that collapses the plain world, the catalogue of drops that turns the collapse into an impossibility, and the theorem with its scope and its one loophole; §6 fixes the seven workstreams; §7 replaces the coincidence rule with the non-circularity rule and keeps the strip test and the (here, Circular) failure outcome; §§8–9 fix success criteria and honest risks; §10 positions the work as the program's capstone. To be revised as REV-A, REV-B, … as each workstream reports, following the strict discipline of the protocol: substitute openly, recover the intended content inside the surrogate where possible, state any residual obstruction precisely, route it to the owning workstream, and never relabel a shortfall as the goal. No em dashes are permitted in the final copy of any paper drawn from this charter; this working draft is not final copy.*
