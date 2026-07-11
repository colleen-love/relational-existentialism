# Relational Existentialism — Series 04

**Quality as restriction: why a groundless world must let each thing turn only part of itself toward another.**

*Working draft, Revision 0. Series 04 is self-contained: it states its own question, builds its own object, and proves its own results from scratch. Series 03 is prior art that informs the design — the way Series 02 informed Series 03 — but nothing here presupposes it. A reader who has never seen Series 03 should be able to follow this charter end to end.*

---

## 1. The one-paragraph version

We want to build a world made entirely of relationships, with no basic building blocks underneath — no atoms. In the plainest version of such a world, we will prove something stark: **if you truly forbid atoms, everything collapses into a single point.** A world of pure, gradeless relation, with nothing simple at the bottom, cannot tell any two things apart, so it has exactly one thing in it. This is a mathematical echo of Parmenides: all is One. To get a world with *more than one thing* in it while keeping the promise of no atoms, relations must carry some **quality** — two things can then differ by *how* they relate, not by bottoming out in different simple parts. The obvious way to add quality is to hang a number or a weight on each relation, imported from outside. We will show that this quietly cheats: the imported scale has a "zero," and a relation whose quality is zero is a relation to nothing — an atom, smuggled back in through the side door. Series 04's proposal is the one repair we can find that does **not** cheat: let the quality of a relation be *a part of the thing doing the relating* — the part it turns toward the other. Quality becomes internal. Nothing is imported, no external zero exists to reintroduce an atom, and — the bet of this program — the very finitude of "you can only turn part of yourself toward another" is what bounds the world into existence, gives it more than one inhabitant, and lets it never finish knowing itself.

That is the whole story. The rest of this charter makes each step precise and lays out the work.

---

## 2. What we are trying to build

A **groundless relational world**: a single domain of *objects*, where

1. every object is nothing but its pattern of relating to other objects (an object *is* how it relates — there is no further hidden substance);
2. relations are themselves objects, free to be related to in turn (no separate second kind of thing that is "just glue");
3. there are **no atoms**: no object is simple, every object decomposes into further relating, without ever bottoming out;
4. there is more than one object (the world is **plural**, not a single point);
5. no object is the all-encompassing "everything," and no object surveys the whole from outside it (**no top, no view from nowhere**);
6. each object attends to itself with limited attention, and so can never wholly capture itself (**incomplete self-knowledge**);
7. the world never collapses to a single undifferentiated point (**non-degeneracy**).

Points 1 and 2 tell us the *mathematical shape* of the thing: objects defined by their relating, with relations reified as objects, is exactly what **coalgebra** was built to describe. An object is a point of a space `X` together with a map that reads off "who this object relates to," and those relata are again points of `X`. The canonical inhabitant is the self-relating object

> **Ω = {Ω}**,

the object whose only relation is to itself — the tightest possible expression of "no atom beneath me." A world satisfying points 1–2 is a **fixed point**: the space of objects is exactly the space of ways those objects relate, `X ≅ F(X)`, where `F` is the operation "take the collection of things you relate to."

The tension this whole program lives inside is between point 3 (no atoms) and point 4 (more than one thing). They sound independent — one about the bottom, one about the size — and one sounds easy. Point 3 sounds like the *cheap* promise: "nothing is fundamental" seems like it should come for free once you refuse to name any atoms. Section 3 proves the opposite. Point 3 is the expensive one, and points 3 and 4 are at war.

---

## 3. The collapse: a groundless world with no quality has exactly one thing in it

This section is the hinge of Series 04. Everything afterward is a response to it.

### 3.1 The plainest world

Take `F` to be "the collection of objects you relate to" — the (suitably size-controlled) powerset operation — and build the fixed point `X ≅ F(X)`. An object is *just* a set of other objects (its relata). Two objects are the same exactly when they relate to the same things, who relate to the same things, and so on all the way down. This "sameness all the way down" is called **bisimulation**, and in the plain world it *is* identity: there is nothing to an object but its unfolding pattern of relating, so two objects with the same unfolding are the same object. (This is point 1, made exact.)

In this world there is exactly one currency of difference: **presence or absence of a relation.** Two objects differ only if, somewhere down in their unfolding, one relates to something the other doesn't. That is the *only* way to tell things apart. Hold onto this — it is the pin the collapse turns on.

### 3.2 The theorem

Now impose point 3 honestly. "No atoms" means: no object anywhere in the unfolding is empty — every object relates to *something* (an empty object, one that relates to nothing, is a simple thing with no internal relating, i.e. an atom). Call an object **hereditarily non-empty** if it relates to something, and everything it relates to relates to something, and so on without end. Point 3 says: *every* object is hereditarily non-empty.

> **Collapse Theorem (target of WS2).** *In the plain (gradeless) groundless world, any two hereditarily non-empty objects are equal. Hence a world with no atoms has exactly one object: the self-relating point Ω = {Ω}.*

The proof is short and worth seeing in outline, because *why* it works is the entire motivation for quality. Suppose `a` and `b` are both hereditarily non-empty. Try to tell them apart. The only tool (§3.1) is to find a relatum of one that isn't matched by a relatum of the other. But every relatum of `a` is itself hereditarily non-empty, and so is every relatum of `b`, so the same question recurs one level down, forever, and *never bottoms out in a decisive difference* — because bottoming out would require reaching an empty object, and we have forbidden those. The relation "pair up `a` with `b`, and recursively pair up their relata" is a bisimulation (each side can always answer the other, precisely because nobody is ever empty). Bisimulation is identity (§3.1). So `a = b`. Every hereditarily non-empty object collapses onto every other, and onto Ω.

### 3.3 What the collapse means

The collapse is not a bug to be patched; it is a **discovery about gradeless relation**, and it dictates the shape of the solution:

> **Difference has to bottom out somewhere.** In the plain world, two things are ultimately different because their *leaves* differ — because descent reaches different simple objects. The atom is the **ground of distinction.** Forbid atoms and you have removed the only place difference could live. "No atoms" and "more than one thing" cannot both hold, because *the atom was doing the work of plurality all along.*

So a genuine groundless world — one with no atoms *and* more than one object — must find a **second currency of difference**, one that does not live at the leaves. Two objects must be able to differ not by *whether* they relate but by *something about how* they relate. That "something" is what we mean by the **quality** of a relation. The Collapse Theorem is a proof that quality is not a decoration we might add for richness; it is a **necessity**, forced by the joint demand of groundlessness and plurality.

The rest of the charter is the search for the right quality — and the argument that almost every candidate cheats.

---

## 4. The false repair: imported weights smuggle an atom back in

### 4.1 The obvious fix

The natural first move is to make relations carry a **weight**: instead of "`a` relates to `b`" being yes/no, let it be a degree — a number in `[0,1]`, or a value in some algebra `Q` of weights brought in for the purpose. Now two objects can differ by relating to the *same* things with *different strengths*. Difference no longer needs the leaves; it can live in the weights. On its face this defeats the collapse: build two objects that each relate only to themselves, one with weight `½` and one with weight `¾`, and they are hereditarily non-empty (no atoms) yet distinct (plural). Plurality without atoms, apparently achieved.

### 4.2 Why it cheats

The imported weight algebra `Q` has to support two operations to model a relational world: you must be able to **combine** parallel relations (a join) and **compose** relations in series (a product `⊗`, since a relation to a relation must compose). Any such algebra has a **bottom element `0`** — the weight of "no relation at all" — and the product respects it: something composed with `0` is `0`.

Here is the leak. In a world of pure relation, a relation-to-a-relation is how objects are built. Compose two relations whose weights multiply to `0` — and in the standard weight algebras (for instance the finite Łukasiewicz chains, where the product is *nilpotent*: enough weak links in series multiply down to `0`) — and you get a relation of weight `0`. **A relation of weight `0` is a relation to nothing. It is an atom.** The imported scale did not remove the atom; it hid one inside its arithmetic, at the value `0`, and composition drags objects down onto it. The moment you use the weights to *build* (compose) rather than merely to *label*, the bottom of `Q` reappears as a simple, relationless object — exactly what point 3 forbade.

> **The no-quiet-atom criterion (governing WS2).** *A quality is admissible only if it introduces no element that behaves as an atom — in particular, no "zero relation" that composition can produce. Any quality drawn from an external algebra with a bottom element fails this criterion the instant composition can reach the bottom.*

One can try to forbid the bottom (work only with weight algebras that have no zero-divisors, so composition never reaches `0`). This is a real escape route and Series 04 will chart exactly how far it goes (WS2). But it is a **restriction imposed from outside** on which weight algebras are allowed — another fiat, another wall around the world rather than a feature of it. We want a quality that *cannot* reintroduce an atom, not one that is *forbidden* from doing so by an external rule.

### 4.3 What we have learned to demand

The collapse (§3) forced quality. The false repair (§4) sharpens the demand: the quality must be one that has **no external zero to fall back onto** — ideally, a quality drawn from *inside the world itself*, so there is no imported bottom element in the first place. If the quality of a relation were made of the very same stuff the world is made of — objects and their relating — then "no atoms" would apply to the quality too, and the leak of §4.2 would have nowhere to happen.

That is precisely the proposal of Series 04.

---

## 5. The repair that does not cheat: quality as restriction

### 5.1 The idea

When `a` relates to `b`, record on that relation **the part of `a` that is turned toward `b`** — written `a↾(a,b)`. Not a number, not an imported weight: a **restriction of `a` itself**, a sub-object of the relating thing, its face toward `b`. Symmetrically the relation carries `b↾(a,b)`, `b`'s face toward `a`, so a relation is inherently **two-sided**: what it is from `a`'s side and what it is from `b`'s side, which need not agree.

The quality of a relation is *which part of me I turn toward you.* A thin, impoverished face is a weak relating; a rich, deep face is a strong one. This is quality — degree, strength, kind — but drawn entirely from the relata. Nothing is imported.

### 5.2 Why it cannot smuggle an atom

The false repair failed because the imported algebra `Q` had a bottom element `0`, and composition could reach it. Restriction-quality has **no imported algebra at all.** The "value" on a relation is a sub-object of the source — an object of the very same world, subject to the very same no-atoms promise. There is no external `0` sitting underneath the values, because the values *are not in an external scale*; they are parts of things that already exist. The only way a face could be "empty" is if it were the empty object — but the empty object is an atom, which point 3 has already outlawed *for objects*, and the faces are objects. The no-quiet-atom criterion (§4.2) is satisfied not by an external prohibition but because **there is no external place for the atom to hide.** Quality made of the world's own stuff inherits the world's own groundlessness.

> **The forced answer (framing claim of the program).** *Restriction-quality is not one option among many for adding quality. It is — we conjecture, and WS2 is charged with making this precise — the essentially unique way to supply the second currency of difference that §3 proved necessary, without the external-zero leak that §4 proved every imported quality suffers. Difference lives in the faces; faces are internal; internality is what forecloses the smuggled atom.*

### 5.3 What restriction-quality buys, beyond not cheating

Because the faces are *parts of the relata*, three further things follow — each a response to one of the points of §2, and each the subject of a workstream. These are stated here as the payoff and made into obligations in §6.

- **Plurality returns, honestly (point 4, vs the collapse).** Two atomless objects can now differ because the parts they turn toward a shared neighbour differ — a difference that lives in the faces, never at a leaf. This is the plurality §3 forbade to the plain world, recovered without a single atom and without an imported weight. *(WS3.)*

- **The world bounds itself (points 5 and 7).** A face is a part of the source, so relating *costs* a part of yourself. To relate to everything, an object would need a distinct part of itself for every object in the world — more distinct parts than there are objects, which is impossible. So **no object can relate to everything**: there is no all-encompassing top, and no observer that surveys the whole — not because we cap the world's size from outside, but because *you can only ever turn part of yourself toward another, and you are not big enough to face everything.* The bound that lets the world exist becomes the world's own grain rather than a wall around it. *(WS4, WS5.)*

- **The self is complete only in the act, never as a possession (point 6).** An object's self-relation carries its face toward itself — the part it turns inward. For any ordinary object this face is a *proper* part: it cannot turn all of itself inward, so it cannot wholly know itself. There is always a positioned blind spot, and that blind spot is where its perspective lives. Only the pure self-relating point Ω turns all of itself toward itself — and even Ω does not *finish*, because "all of itself" includes its own self-relating, coinductively, without end: complete at every step, closed at none. Two shapes of incomplete self-knowledge, one from finitude and one from groundlessness. *(WS6.)*

### 5.4 The honest hazards, named at the outset

Restriction-quality is a bet, not a theorem, and Series 04 is built to be able to report that the bet failed. Three hazards are load-bearing and named now:

- **The faces must behave (the technical gate).** For "an object is its relating" (point 1) to keep working, the restriction structure must preserve the property that sameness-all-the-way-down is identity. In coalgebraic terms the face-carrying operation must **preserve weak pullbacks**; the face component refers to sub-objects of the *source*, an unusual shape, and this is not automatic. If it fails, point 1 breaks and the whole construction must move to a different carrier or stop. *This is the single most likely place the program dies, and WS1 settles it first.*

- **Faces must actually distinguish targets (the plurality/no-top crux).** The self-bounding argument of §5.3 needs that facing different things generally requires *different* faces. If an object could face many different targets with the very same part of itself, the counting collapses and "no top" falls back to an external cap. Plausible, not automatic; WS4 owns it.

- **Elegance is not proof (the trivialization risk).** One idea — quality as restriction — is being asked to answer for plurality, boundedness, no-top, no-view-from-nowhere, and incomplete self-knowledge all at once. When a single move explains everything, the danger is that it explains nothing: that these are not five results but one definition wearing five costumes, so their interconnection was *assumed* rather than *discovered*. Series 04's central discipline (WS7) is to prove, for each, that the easy definitional version *coincides with* an independently forced version — and to be willing to report that it does not.

---

## 6. Workstreams

Seven workstreams. WS1–WS2 establish the object and the forced-answer claim; WS3–WS6 deliver the payoffs of §5.3, one theme each; WS7 audits the whole against the trivialization risk.

- **WS1 — The world and its faces.** Define the restriction functor: an object is a size-controlled family of faced relations `(relatum, face)`, with `face` a sub-object of the source. Prove the face is **forced, not annotated** — the canonical choice is "the part of the source reachable through this relation," so no external data is added and the plain world is refined, not replaced. **Gate: prove the construction preserves weak pullbacks**, so that sameness-all-the-way-down remains identity (point 1). Deliver the fixed point `X ≅ F(X)` and recover Ω = {Ω} inside it. *Blocking; settled first. Outcomes in play: Discharged, or Impossibility proved (the gate fails), which redirects the carrier.*

- **WS2 — The collapse, and the forced answer.** Prove the **Collapse Theorem** (§3.2): the plain groundless world with no atoms has exactly one object. Prove the **imported-weight leak** (§4.2): any quality from an external algebra with a bottom element reintroduces an atom under composition, exhibited concretely on a nilpotent chain. Then state and defend the **forced-answer claim** (§5.2): restriction-quality supplies the necessary second currency of difference with no external zero to leak. The strongest available form — an essential-uniqueness result — is the target; a clean statement of *why* internality forecloses the leak is the floor. *This workstream is the intellectual spine; §§3–5 are its prose.*

- **WS3 — Plurality without atoms.** Exhibit two objects that are hereditarily non-empty (no atoms) and genuinely distinct (plural), told apart purely by differing faces toward a shared neighbour — no imported weight. Confront the composition question: when faces compose, can a face degenerate to the empty object (the internal echo of the §4.2 leak)? Characterize exactly when composition stays atom-free. **Coincidence duty:** deliver the plurality *and* re-prove that without faces the collapse still holds, so the rescue is earned, not assumed.

- **WS4 — No top, no view from nowhere.** Prove **no object relates to everything**, via the self-cost argument of §5.3: a maximal object would need more distinct faces than there are objects. This is a genuine size-wall, replacing any external cap. Prove **no observer surveys the whole** (its faces cannot reach every object) and the positive companion (distinct objects hold genuinely distinct positioned views, because a view *is* a face and every face is positioned). **Crux hypothesis: facing distinguishes targets** (§5.4); the wall lives or dies here. **Coincidence duty:** the wall must be forced by the face-counting, not read off the definition of "face."

- **WS5 — The self-bounding of the world.** Make precise the claim that the bound on the world is *endogenous* — that the world is set-sized because faces are parts of sources, not because a size was imposed. Adjudicate the candidate mechanisms (faces don't enlarge the world; collapsing objects with identical faces; and, delicately, whether faces shrink along relations so the world is founded *in its quality* while groundless *in its objects* — with the sharp requirement that faces stay improper exactly on the self-loops, so Ω = {Ω} survives). *Owns the "grain, not wall" thesis; reports honestly if the bound cannot be freed from fiat.*

- **WS6 — The two incompletenesses.** Prove that an ordinary object's self-face is a proper part, so **no ordinary object wholly knows itself** — and, the coincidence theorem, that the part its self-face *omits* is exactly the classical self-reference blind spot (a Lawvere/Gödel diagonal), so the geometric statement and the logical one are the same fact. Prove separately that Ω's self-face is total in extent yet **never closes** (coinductive non-termination). Deliver **attention as face-thickening**: attending to a relation is thickening the face toward it, starving it is thinning — so the dynamics of attention are internal to the object, not a system bolted onto it. **Coincidence duty:** the proper-part statement must not stand on its definition alone; the blind-spot coincidence is what earns it.

- **WS7 — The anti-trivialization audit.** Across WS3–WS6, verify the coincidence discipline: for each payoff, the easy definitional form and an independently forced form were proved *distinct statements that coincide*, not one statement restated. Deliver the central Series 04 finding — **whether plurality, boundedness, no-top, and incomplete self-knowledge genuinely reduce to a single fact (the finitude of facing), or whether that unification is an artifact of an over-strong definition.** This workstream can return the verdict **Trivialized** — a sharp negative about the program's own conjecture — and returning it honestly is a success, not a failure.

---

## 7. Methodology and outcome vocabulary

Each point of §2 becomes a precise specification; a concrete object is exhibited; an adequacy theorem shows the object meets the specification (existence, sameness-is-identity, plurality, the size-wall, incompleteness). **Negative results are first-class outcomes** — the Collapse Theorem and the imported-weight leak are *proved* obstacles that do the program's real motivating work, and the program counts a sharp impossibility as a success.

Each workstream obligation is classified as **Discharged** (its stated target is proved), **Impossibility proved** (a sharp negative — a success), **Partial** (part proved, with the remaining obstruction made mathematically precise), or **Failed** (not achieved, with a documented why). A Partial or Failed result triggers a **methodology note** — a correction to the plan or an explicit hand-off — never a redefinition of the target.

Series 04 adds one rule for its own signature risk:

> **The coincidence rule.** No payoff of §5.3 may be reported **Discharged** on its definitional form alone. Discharge requires a *coincidence theorem*: the definitional form and an independently motivated forced form, separately stated and proved equal. A payoff holding only definitionally is reported **Partial — definitional-only**, with the forced form as the named open obligation.

And one outcome the ordinary vocabulary cannot express: **Trivialized**, the finding that the §5.3 unification is definitional rather than substantive. WS7 owns it; returning it honestly is a program success in the sense above.

---

## 8. Success criteria

Success is a single object — the groundless world with restriction-quality — that provably:

(i) contains no atoms and yet (ii) has more than one object (plurality), the two held together by faces rather than leaves; (iii) identifies each object with its relational unfolding (sameness is identity); (iv) has no object that relates to everything and no observer of the whole, by the self-cost of facing rather than by external cap; (v) carries attention as face-thickening under which no ordinary object wholly knows itself, with the blind spot shown to be the classical diagonal, and with Ω complete-yet-unclosed; and (vi) is non-degenerate — more than one object, and the dynamics do not starve every object down to a point.

Against the central question, success takes one of these shapes, all valid:

- **The forced answer stands (headline positive).** Restriction-quality is shown to be the essentially unique atom-free supplier of plurality (WS2), and the world bounds itself without fiat (WS5) — the bound is grain, not wall.
- **A payoff is characterized honestly.** For each theme of §5.3, a reported outcome: *delivered with its coincidence theorem*, *delivered but definitional-only* (forced form open), or *obstructed* with the obstacle made precise. Each is terminal and valid.
- **The verdict, either way (WS7).** *One finitude, substantively* — the payoffs genuinely reduce to the finitude of facing, coincidence theorems throughout — or *Trivialized* — the reduction is definitional. Both are successes; the second is a sharp negative about the conjecture.

> **The characteristic risk, stated plainly.** Series 04's danger is not that it fails but that it *succeeds too cheaply* — that restriction-quality settles everything by making everything one definition. The criteria above are written so that **catching that** (WS7's *Trivialized*) counts as success, not concealment. A charter that could only succeed would prove nothing.

---

## 9. Open problems and honest risks

- **The technical gate (WS1) is existential.** If the face-carrying construction does not preserve weak pullbacks, "an object is its relating" (point 1 / criterion iii) breaks and is not merely weakened. Most likely single point of failure; settled first. Honest outcome if it fails: Impossibility proved for the reachable-restriction construction specifically, and the program either finds a preserving variant or declares a different carrier and pays the re-proof cost.
- **Trivialization (the signature risk).** That §5.3's payoff is one over-strong definition restated — so the interconnection is assumed, not found. The coincidence rule (§7) and WS7 exist to catch it, but only if the forced forms are genuinely independent of the definitional ones, itself a per-payoff judgement that could be got wrong. This risk cannot be fully retired in advance; it is what the program tests.
- **Facing-injectivity (WS4) may be false.** If one object can face many targets with the same part of itself, the no-top wall collapses to an external cap, and the "grain, not wall" headline fails for its flagship instance. Plausible, not automatic; the crux of WS4.
- **The self-shrinking route to the bound may hide a floor (WS5).** If faces are *always* strictly smaller along relations, the world is secretly well-founded and has atoms-in-disguise (the minimal faces), betraying point 3. The escape — faces improper exactly on the self-loops — is a specific, checkable structure, not a given. Contained to one of several bounding routes, so it does not endanger the whole bound.
- **Composition may degenerate (WS3).** When faces compose, a face could in principle collapse to the empty object — the internal echo of the §4.2 leak. Characterizing exactly when composition stays atom-free is the technical heart of WS3; a total failure would leave plurality worse off than the imported-weight repair, to be reported honestly if it occurs.
- **The forced-answer claim may be only heuristic (WS2).** "Restriction-quality is *the* atom-free quality" is the program's boldest claim. The essential-uniqueness form may resist proof, leaving a defended-but-not-proved thesis. Reporting it as heuristic rather than theorem, if so, is required.
- **Interpretive gap (permanent).** Whether this object *is* the groundless relational world or a faithful mathematical model of it is a philosophical question to frame, not a theorem to prove. Restriction-quality narrows the gap — the model now carries perspective in its very type — but does not close it.

---

## 10. Positioning

Philosophically: radical ontic structural realism and the "relations without relata" objection (Ladyman & Ross, French); the denial of a view from nowhere (Nagel); the double empathy problem (Milton), for which the two-sided relation — `a`'s face and `b`'s face, which may not match — is a direct formalization; and Buber's I-Thou / I-It, read here not as two ends of one dial but as the difference between a rich face and a thin one, with a gradeless I-It world collapsing to the single Parmenidean point exactly as §3 proves, and quality-of-facing being what lets a genuine Thou exist at all. Formally: non-well-founded set theory and universal coalgebra (Aczel; Rutten, Jacobs) for objects-as-relating; Lawvere's fixed-point theorem and its diagonal, for the incompleteness coincidence (WS6); Lawvere-enriched categories, as the natural home of quality-read-as-distance; and the theory of distributive laws, for how faces compose (WS3, WS6). The distinctive bet of Series 04, in one line: **the quality a relation carries is not imported but is a part of the relata themselves, and this single internal move is what turns a bounded world from a walled thing into a grained one — where the smallness is not imposed on relating but *is* relating, the turning of only part of oneself toward another.**

*Working draft, Revision 0: the program document before any workstream has reported. §1 gives the whole argument in a paragraph; §§2–5 walk it — the world we want, the collapse that forbids a plain version, the imported-weight repair that cheats, and restriction-quality as the repair that cannot; §6 fixes the seven workstreams; §7 adds the coincidence rule and the Trivialized outcome; §§8–9 fix success criteria and the honest risks; §10 positions the work. To be revised as REV-A, REV-B, … as each workstream reports, following a strict discipline: substitute openly, recover the intended content inside the surrogate where possible, state any residual obstruction precisely, route it to the owning workstream, and never relabel a shortfall as the goal. No em dashes are permitted in the final copy of any paper drawn from this charter; this working draft is not final copy.*
