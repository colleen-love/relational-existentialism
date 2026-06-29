# Relational Existentialism: One Step Toward the Formalization

> **Normalized axioms (handoff XX/XXI) — read alongside [`AXIOMS.md`](AXIOMS.md).** This essay predates the
> axiom normalization; read its axiom references through the canonical four: **A3 is now a *process***
> (relations co-direct attention asymmetrically in the relata), with the **self its *derived* fixed point**,
> not a posited eigenform; **D1** generalizes `σ = Tr` to the **modular flow** (the trace its
> infinite-temperature limit); **A1** is one dimension-generic arena. The four axioms are one canonical,
> version-pinned layer in `theory/`.

> **Scope note.** This page describes the **broader program**. The mechanized, scoped result is **paper
> one** in [`docs/spec/`](.) ([`paper-two.md`](../../paper-2/spec/paper-two.md)); the rest of what this page sketches
> — the sparsity dichotomy (Conjecture 3.7), the cosmos readings, the functorial semantics — is supporting
> development, archived under [`docs/archive/`](../../archive/spec/) for later papers, not part of paper one.

This is the middle rung of a ladder. Below it is [the view in plain
language](relational-existentialism.md) — the philosophy with no machinery showing. Above it is the
[formal spec](.) and the [Lean and Agda proofs](../formal/) — the philosophy as checkable
mathematics. This page stands between them. It keeps the plain language, but it names the
*mathematical bones* under each idea, so that when you open the spec the words there are already
familiar. There are no symbols here, only the shapes the symbols stand for.

A guiding rule runs through all of it, and it is the same rule the proofs hold themselves to: **say
exactly as much as the structure earns, and mark where description takes over from proof.** Where
this page says "this is a theorem," a machine has checked it. Where it says "the view reads it as,"
that is a lens laid on a theorem, honest only as a lens.

---

## 1. Relation first means: arrows before things

The starting move is that relation comes first and the self is what relation produces. The
mathematical home for "relation comes first" is a **category**. A category is a world made of two
ingredients: *objects* and *arrows between them*. The trick — the whole reason it fits — is that in
a category you can never point at an object directly. You can only ever speak of it through the
arrows running into and out of it. An object simply *is* its pattern of arrows; two objects with
the same pattern are the same object. That is "you are your relatings" turned into a setting rather
than a slogan, and it is a standard fact (it goes by the name *Yoneda*).

So we read an arrow as a *relating* — a relating of one thing to another — and composing two arrows
as *relating through* a middle term. Selves are not among the starting ingredients. They will have
to be *built*.

## 2. A self is a fixed point — "to relate is to create"

Take the simplest relating: a thing relating to itself, its output fed back into its own input.
The formal name for "feed the output back to the input" is a **trace** (or *feedback*). Now ask:
when you loop a relating back on itself, is there a state the loop leaves *unchanged* — a state
that, run through the relating once more, comes back as itself?

Such a state is a **fixed point**, and the theory's name for the self-sustaining fixed point of a
loop is an **eigenform**. The first theorem (**3.1**, *to relate is to create*) is that the loop
*has* one. Looping does not merely shuffle what was already there; it produces a fixed point that
need not have existed before the looping started. Two people in real conversation generate a third
thing — the conversation — and the third thing is a fixed point of their relating.

Honesty, exactly as the proof states it: what is actually checked is the bare existence of such a
fixed point (a classical result called *Knaster–Tarski*, which hands you a fixed point for *any*
loop that is monotone — "more in, at least as much out"). Existence is cheap. The discriminating
claim is not *that* selves can form but that they *rarely* do — and that is a different theorem (§5
below).

## 3. The mirror that can't close is a diagonal argument

The most charged case of self-relation is a self trying to get all the way around itself — a
complete inner picture of the whole of itself, nothing left out. The claim is that this is
impossible, not by accident but by structure.

The structure is **Lawvere's theorem**, which is the grown-up form of the oldest trick in logic:
the *diagonal argument* (the one behind "this sentence is false," behind Cantor's larger
infinities, behind Gödel). The shape is always the same. Suppose you had a complete self-model — a
way of holding, inside yourself, every possible way of looking at yourself. Then you could build
the one look that does the opposite of whatever the model predicts it will do — and that look is
missing from the model. So the complete model cannot exist. The *looker* is always the residue the
picture omits.

Two things to carry to the spec. First, the argument needs to **copy** its object — you must
duplicate yourself to compare the copy against the original — and the residue is exactly what the
copy leaves out. "Knowing requires copying" will matter again in §7. Second, this is **knowing**,
the act of objectifying; it is a theorem (theorem **3.3**, the knowing side) proved with *no
assumptions at all*, which is fitting, since incompleteness here is just the contrapositive of a
one-line diagonal.

## 4. You are your lived relating, which exceeds how you appear

If a self is what its relating makes it, what is its *identity* — when are two selves the same one?
The answer cannot be "they look the same from outside," because the seam (§3) says the outside
never gets all the way in. So identity is defined from the inside, by a notion called
**bisimulation**: two selves are the same when every move one can make can be matched by the other,
*and the states they move to are again the same in this sense* — all the way down, forever. (It is
a circular definition closed off in the only honest way, by taking the *largest* relation that
survives its own circularity. That "largest self-consistent fixed point" is the same fixed-point
move as in §2, used on relations instead of states.) Call this **lived identity**.

Set it beside the outside notion — **observational equivalence**, "no external probe can tell them
apart." Theorem **3.2** proves two things about the pair. Lived sameness implies observed sameness
(if you are the same inside, no outside test separates you). But *not the reverse*: there are two
selves observationally identical from outside and yet not the same inside. Lived identity is
**strictly finer** than appearance. That gap — same on the outside, different on the inside — is
the formal address of the **first-person surplus**: the part of who you are that exceeds how you
appear. And a further theorem pins down when the gap opens: it requires the freedom to have *done
otherwise* (branching). A clockwork's behaviour reveals all of it; a self that could have branched
keeps a remainder.

## 5. Selves are rare — sparsity

If relating creates, and you are always relating, why doesn't a new self crystallize at every
encounter? Because creation is the *exception*. Relating makes connective fabric constantly; a
fabric that *settles into a lasting self* is rare. The mechanism is **return under finite
attention**: a relation builds a persisting self only when it is looped enough times to hold, and
attention — being finite — cannot loop everything.

This is the one place the theory reaches for a quantitative headline, **Conjecture 3.7
(sparsity)**, and it has two faces. The first is sheer counting: a finite attention budget divided
among selves that each cost at least some positive minimum can only fund *so many* of them —
a number that does *not* grow as the system acquires more relations, so the *fraction* that become
selves falls to zero. (That counting argument is elementary and fully proved — **Lemmas 3.7.1 and
3.7.2** — and there is a sharp flip side: remove the finite budget and *every* loop closes, so the
theory would say nothing. Finiteness is what makes it discriminating.) The second face is
geometric: among all possible behaviours, the self-sustaining ones form a vanishingly thin set —
**nowhere dense**, in the precise topological sense — which has been checked in the Agda proofs. A
third, deeper face is *spectral*: under feedback with gain, only a few modes sit near the top and
sustain themselves; the rest decay away. The theory needs selves to be **rare yet more than one**
(so that *which* self you became is contingent, partly yours), and the spectral analysis delivers
exactly that — sparse *and* plural.

## 6. Knowing is the objectifying move; feeling is a different kind of arrow

Knowing and feeling are two ways the same relating can turn. The view makes them *different kinds
of mathematical object*, and that difference is the whole of theorem **3.3**.

**Knowing** is the objectifying look — the move that turns a relation into an object held at a
distance. Formally it is the same self-applied operation as the trace/mirror, and as an operation
it has a definite *type*: it takes a thing and returns a thing, which is exactly the type the
diagonal argument of §3 can run against. So knowing is obstructed: it leaves a remainder, always.

**Feeling** is not that move. It lives "one level up" — it is a *relation*, not an
object-returning operation — and the diagonal argument simply has nothing to grab: there is no copy
held at a distance for it to fall short of. Here is the discipline the proofs insist on, and the
plain-language essay was tightened to respect it: the theory proves only the **negative** half —
*feeling is not the kind of arrow the obstruction touches.* It does **not** prove the tempting
positive half — that feeling is therefore *whole*, *global*, present all at once. That feeling
*seems* whole is true and important, but it is description, not theorem. "Knowing is obstructed;
feeling is simply not the kind of move obstruction applies to" is the earned claim, and no more.

What knowing *does* to a relation has its own name: **decoherence**. To know a relation is to
retract it onto its classical, copyable shadow — keeping the part you can objectify, discarding the
rest. And here is the consoling theorem (in §3.5 of the spec): the discarded coherence is not
destroyed, only **relocated** — it migrates into the relationship itself, into the *between*, which
you cannot forget because it is part of you. Decoherence is what coherence looks like when you
forget the part of the world that still carries it.

## 7. The other, the seam, and the "we"

Because relating constitutes both parties, a part of you *is* the relationship, which is a part of
the other. So a related other is not a separate object you could fully map — mapping them
completely would be mapping the part of *you* folded into them, and §3 forbids that. The theory
turns this into a clean map: the only thing you can completely know is something you have *no*
relation to (and so no access to); everything you can actually reach, you relate to, and so cannot
fully know. *Intimacy and complete knowledge pull against each other* — proved, not preached.

The **seam** is the residue that remains: no single perspective contains all the others, not even
in principle. Yet perspectives *overlap*, and where they overlap they can agree, and the agreement
across many partial views is what "objective" actually points at. The shared world — the "we" — is
the structure that survives being looked at from everywhere it can be looked at from. It is real,
and the gap inside it (the seam) is real too, and the view says you need not close the second to
trust the first.

## 8. Why "two people are entangled" is ill-typed — the firewall

One sharp, load-bearing result keeps the theory honest about its own reach. There are two ways a
relation can be structured: the **copyable** kind (where you may freely duplicate a state — the
fragment where minds, words, and social facts live) and the **entangled** kind (where there is an
irreducible between that does *not* reduce to the parts — the fragment quantum physics lives in). A
theorem (the **firewall**, with *no-cloning* as its other face) shows these two **cannot coexist**
in one domain without the whole thing collapsing to triviality. Copying and entanglement are
mutually exclusive by structure.

The payoff is a discipline the type system enforces: importing genuine quantum entanglement into a
copyable social domain is not *unwise*, it is **ill-typed** — there is no structure-preserving map
that does it. The theory refuses that particular overclaim *by construction*, which is the opposite
of the usual humanities move of borrowing physics as metaphor.

## 9. What is proved, what is a reading, what is typed out

The reason to climb the next rung — into the [spec](.) and the [proofs](../formal/) — is that
every claim there wears its status openly, and the statuses are not equal:

- **Theorems** carry a machine-checked proof and an audited list of exactly which logical
  assumptions they used (often *none*). The mirror, the seam, the firewall, the identity surplus,
  the counting sparsity — these are checked.
- **Readings** are lenses laid on a theorem: the structure is proved, the interpretation is not.
  "This decoherence differential *is* feeling," "the knower→known arrow *is* time" — the dynamics
  are theorems; that they *are* the named phenomenon is honest only as a reading, and labelled so.
- **Typed-out residues** are the three things the view deliberately does *not* reach and predicts
  it *cannot*: the **warmth** of relation (why "you are loved" lands as more than "you are
  correlated with"), the **hard problem** (why there is something it is like at all), and
  **freedom** (whether the returning that builds you is authored or only feels authored). By the
  knowing/feeling theorem, *formalizing is itself the objectifying move* — so the language captures
  the structure of feeling and, on its own account, not feeling-as-lived. The boundary is not an
  embarrassment; it is drawn on purpose, so that everything inside the lines can be trusted
  precisely because the lines are drawn.

Almost none of the mathematics is new — it is a careful re-proof of established results
(bisimulation, Lawvere, traced categories, the partial trace, Banach and Perron–Frobenius theory).
The contribution is the **synthesis**: the recognition that one structure — the objectifying,
copyable move against the entangled, uncopyable one — runs through identity, decoherence,
causation, and selfhood alike, with a single wall between the two faces. The full honest accounting
is the [provenance ledger](../../paper-2/spec/04-provenance.md), which a reviewer should read first.

---

→ The pure-prose version is [the view in plain language](relational-existentialism.md). The rigorous
version begins at [the doctrine](00-doctrine.md) and the scoped result in
[paper one](../../paper-2/spec/paper-two.md) (the broader catalog is archived under [`docs/archive/`](../../archive/spec/)).
