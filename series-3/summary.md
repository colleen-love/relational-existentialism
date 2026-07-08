# Relational Existentialism — Series 3: A Plain-Language Summary

*What the project set out to ask, what it found, and what the finding means.*

## The question

The project asks a question that sounds like philosophy but was made precise enough to answer with mathematics: **can you build a world made entirely of relationships?**

Not a world of things that then have relationships — a world where there are no basic building blocks at all, where everything is defined by how it relates to everything else, all the way down, with no bottom. In this picture: there are no atoms (nothing is simple); relationships are themselves things that can relate; there is no "everything" you could stand outside of and survey; each thing is shaped both by what it's part of and what's part of it; each thing pays limited attention to itself and so can never fully know itself; and the whole thing never collapses into a single undifferentiated point.

The bet was that the famous objections to this view — "you can't have relations without things to relate," "structure can't go all the way down," "this leads to infinite regress" — aren't fatal flaws. They're *specifications*: descriptions of exactly the kind of mathematical object certain tools (coalgebra, non-well-founded set theory) were invented to handle.

## The answer

**Yes — a version of it. And the mathematics is machine-verified.**

An object was built that provably has almost all the required features, and a computer proof assistant (Lean 4) has checked every step: no gaps, no shortcuts, no hidden assumptions beyond the standard mathematical baseline. That verification passed.

But "yes" comes in a more interesting shape than a simple thumbs-up, and the honest version is the better story:

**First, the literal dream object doesn't exist — and that's a theorem, not a failure.** The most ambitious version of the world-of-relations is provably *too big to exist* as a well-defined mathematical object (for the same deep reason there's no "set of all sets"). So the project built a **bounded** version instead — one with a size limit — and this is the version that actually exists and that everything else is built on. This wasn't a retreat; the project's own analysis had already pointed here.

**Second, two of the "successes" are actually impossibility results.** Two of the required features turned out to be things you prove *can't happen*, and that's exactly what the philosophy predicted and wanted:

- *No thing can fully know itself.* This is proved rigorously, using the same mathematical idea behind Gödel's incompleteness theorem. A thing paying limited attention to itself can never build a complete self-portrait — there's always a positioned, partial blind spot. That blind spot is where perspective lives.
- *There's no clean "top-down + bottom-up" master rule.* The project wanted a single elegant law letting you read any object both from above (what it's part of) and below (what it's made of) in perfect harmony. It proved that law *cannot exist* in the strict form — and the reason is illuminating: when relationships are themselves things, combining them is inherently a little loose, a little order-forgetting. You still get top-down-and-bottom-up constitution, just not in the rigid form first imagined. **The looseness is a discovery about the nature of relationships, not a bug.**

**Third, one feature is mostly-but-not-fully closed.** The "attention" part of the picture — how a thing's focus shifts over time and whether it settles into a stable partial self-image — is proved to work for a simpler model of attention and precisely *diagnosed* for the richer, more realistic one. For the richer model, the project pinned down exactly why it's harder and exactly what one further step would close it. So it's not a mystery; it's a well-understood piece of unfinished business.

## The deeper finding

Here is the part worth sitting with, because it's more than a status report — it's a genuine result about the whole enterprise.

The six requirements were presented as six equal design goals. But building it revealed a **hierarchy** nobody stated up front:

- **Two of them do almost all the real work** and are nearly "free" — they're baked into the choice of mathematical tools rather than extra conditions to check. (That relations are themselves things, and that things can't fully know themselves.)
- **Three of them fractured** — they broke apart, weakened, or turned out to be impossible in their stated form. And these three are precisely the ones that make sweeping claims about *the whole* — about there being no outer limit, no view from outside, no collapse anywhere.

And the reason they fractured is the same in every case, which is what makes it a real finding rather than three separate disappointments:

**The very move that lets the object exist is the move that weakens every claim about the totality.** To exist, the object had to be bounded — given a size limit. But every sweeping "there is no outer edge / no God's-eye view / no degeneracy anywhere" claim depends on the object being *un*bounded and endless. So bounding it buys existence at the cost of the grandest claims. You can have a world of pure relation that genuinely *exists*, or you can have the fully unbounded, no-edges-anywhere version that stays a beautiful idea — but the mathematics says you can't have both at once.

That trade-off is itself a philosophical result. It says something true and non-obvious about what it *costs* for a groundless, relation-first reality to be real rather than merely imagined. The project set out expecting the hard parts to be informative when they resisted — and they were, in exactly this way.

## Where things stand

- The core construction exists and is machine-verified.
- Six of seven required features are established (two of them as illuminating impossibility results); the seventh is established in part and precisely diagnosed for the rest.
- The main remaining technical task is a single, contained step to finish the richer attention model.
- One question is permanently outside what any proof can settle: whether this object *is* the relational world the philosophy describes, or a faithful mathematical model *of* it. That's a matter of interpretation to be argued, not proved.

## The one-sentence version

*A world made entirely of relationships can be built and machine-verified — but only a bounded version exists at all, its most sweeping "no-edges" claims soften exactly where the boundary is imposed, and its deepest features (that nothing is fundamental, and that nothing can fully know itself) turn out to be two faces of the single modesty that lets it exist in the first place.*
