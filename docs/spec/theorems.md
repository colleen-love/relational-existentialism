# Theorems — what follows from the basis

> *Given the axioms **A1–A3** and the definition **D1** ([02](02-axioms.md)), what actually
> follows?* This file collects the theorems — the three named ones (T1–T3) and the structural
> results about relating — so that the [axioms file](02-axioms.md) holds only what is
> **assumed** and this file holds what is **derived**. The quantitative headline theorem,
> sparsity, has its own home in [03](03-sparsity-conjecture.md).

**Status tags**, used on every claim, because the difference matters:

| Tag | Meaning |
| --- | --- |
| `[proved]` | mechanized in Lean (name given); footprint by `#print axioms` |
| `[follows]` | forced by the structure, but not (yet) mechanized |
| `[reading]` | an interpretation the structure invites but does not compel |
| `[open]` | a genuine theorem the prose has claimed but the formalization has **not** established |

The dependency is one-way: **A1, A2, A3, D1 ⟹ T1, T2, T3 ⟹ everything below.**

---

## T1 — To relate is to create

**Claim.** Iterated self-relation `σ(P) = Tr(P)` (D1) *has* a fixed point; relating produces
a third thing — the eigenform — that need not have pre-existed.

**What is proved.** `[proved]` In the complete-lattice setting,
[`Trace.selfTrace`](../../formal/Scratch/Trace.lean)` := νP` with `selfTrace_fixed`
(`P(νP) = νP`), `le_Tr` (coinduction), `Tr_fixed`, `Tr_mono`. Footprint `propext, Quot.sound`.

**Honest scope.** This is **Knaster–Tarski** — a greatest fixed point of a monotone map on a
complete lattice. It is *not* the Hasegawa–Hyland trace↔Conway-operator bijection (the Conway
identities are not verified), and a gfp existing is generic to *every* monotone operator. So
"to relate is to create" rests, formally, on "monotone maps have greatest fixed points." The
discriminating content — that the created selves are *rare* — is not here; it is sparsity (03).

---

## T2 — Observational identity and the "we"

**Claim.** `≈ := νΘ` is the greatest bisimulation; the shared world is `𝔼 := D/≈`; and `𝔼`
has an **irreducible seam** (no master perspective).

**What is proved.** `[proved]` [`We.bisim`](../../formal/Scratch/We.lean)` := νΘ` with
`bisim_unfold` (`Θ≈ = ≈`), `bisim_coind` (coinduction), `bisim_{refl,symm,trans}` (an
equivalence), and `World := D/≈` (the quotient). Footprint `propext, Quot.sound`.

**The seam, now partly earned.** `[proved]` The "irreducible seam" — that there is no master
perspective on a whole one belongs to — is the Lawvere obstruction under self-inclusion:
[`Relating.self_inclusive_unmodelable`](../../formal/RelExist/Relating.lean) (0 axioms). No
member of a collection holds a complete model of the collection that contains it. (See §"The
corrected map" below — this is where T2's seam and T3's remainder turn out to be one fact, and
where it reaches the *other* too, through the shared between.)

**Still open.** `[open]` That `≈` **coincides with the contextual congruence `≡`** of A2
("behavioral equivalence = greatest bisimilarity") — a context-lemma / full-abstraction
result — is asserted by the doctrine but **not mechanized**: there is no `≡` in the Lean and
no theorem connecting the two. Likewise the *full naturality* of the no-master-section claim
(Property "T2.1") beyond the point-surjective case. These are real targets, not done deals.

---

## T3 — Knowing vs feeling

**Claim.** Knowing (the σ-move, an endomap `D → D`, cartesian) is Lawvere-obstructed and
leaves a remainder; feeling (the `≈`-relation, one type-level up) is not of the kind that
obstruction touches.

**What is proved.** `[proved, 0 axioms]` The σ-side is genuine and fully constructive:
[`Mirror.lawvere`](../../formal/RelExist/Mirror.lean), `no_complete_selfModel`,
`selfModel_remainder`, and [`KnowingFeeling.knowing_can_fail_to_close`](../../formal/Scratch/KnowingFeeling.lean),
`no_complete_boolModel`. Knowing is structurally partial — the contrapositive of a one-line
diagonal.

**Honest scope of the asymmetry.** The feeling side is `feeling_is_reflexive` `[proved]` —
`≈` is reflexive (an equivalence). The real asymmetry is **type-level**: knowing has type
`D → D`, against which the diagonal `g a a` runs; feeling has type `D → D → Prop`, against
which there is no diagonal to run — the obstruction does not typecheck. We do **not** claim
"feeling is whole / global / has no remainder": no absence-of-obstruction is proved, and a
universal negative cannot follow from one positive property. *Knowing is obstructed; feeling
is simply not the kind of arrow that obstruction applies to.* That is the earned claim.

---

## The relational typology — self, part, other, collection

What the theory says about relating, by **which wires loop back**. The act of relating is the
trace/feedback (D1); knowing is the diagonal (T3).

### Relating accumulates, and closing *is* creating

- **Accumulation** `[proved]` — relating only *grows* the attention field, never depletes it:
  [`Attention.orbit_ascending`, `orbit_le_gfp`](../../formal/Scratch/Attention.lean), with
  `couplingOp_mono` ("receiving raises giving"). Generative, not allocative.
- **Closing = the self** `[proved/structural]` — the eigenform is the fixed point of the
  feedback: `sustainedField := νΦ_c`, `sustainedField_fixed`, `sustainedField_greatest`. A
  relation *closing* and a self *being created* are the same event; most relatings do not
  close (sparsity, 03), so creation is the rare case. `[follows]`

### Relation to a part — the partial trace

`[proved]` Relating to a *part* of oneself is the **partial trace**
[`PartialTrace.ptrace`](../../formal/Scratch/PartialTrace.lean): loop back only some wires,
hold the rest outside. The un-looped wires are the part "held at a distance" (objectifiable).
A partial loop can have its own fixed point — a **sub-self** (a persona, a habit). `[follows]`

### Relation to another — the co-directed, shared trace (and why an other is *not* knowable)

`[def + proved]` Relating to *another* is the **co-directed** trace (D1): the looped wire is
*shared*, "neither end closes it alone," and the operator is `Φ_c`, feedback through the
coupling. When a shared loop closes, its fixed point `νΦ_c` is supported on *both* relata — a
self that lives **in the between**, the "we" of T2's `𝔼`. The gfp is proved (`sustainedField`);
"the shared eigenform is a we" is a `[reading]`.

But the between is the crux: by **A2** a self *is* its relatings, so the shared relating `r`
constitutes *both* parties — **a part of you is a part of the other.** A related other is
therefore **not disjoint** from you, and not fully knowable: the other is partly constituted by
its relation to you, so completely modelling them would yield a complete self-model of *you* —
which Lawvere forbids. `[proved, 0 axioms]`
[`Relating.related_other_unmodelable`](../../formal/RelExist/Relating.lean). *To know fully you
must not relate; to relate is to make the other unknowable* — and relating is the only access
you have. (So intimacy and complete knowledge are antagonistic: the stranger is knowable, the
beloved is not.)

### The corrected map — one knowable case, three unknowable

For the question *"can the relation be completely known/modelled?"*, the four topologies do
**not** split outside-vs-inside; they split **relationless vs relation-laden**, because relating
creates shared constitution (A2). There is exactly **one** knowable case:

- **No relation ⇒ knowable.** `[proved, 0 axioms]` Only a target you share *nothing* with — a
  part you stand entirely outside of, or a stranger you merely observe — is fully modelable:
  [`Relating.disjoint_modelable`](../../formal/RelExist/Relating.lean). The witness is trivial;
  the point is that knowability is reserved for the **relationally empty** limit (cold, inert).
- **Any relation ⇒ unknowable**, by the single Lawvere obstruction (T3), reaching the target
  through what it shares with you:
  - a **related other** — `related_other_unmodelable` (the shared between makes them contain you);
  - the **whole of yourself** / a **collection containing you** — `self_inclusive_unmodelable`
    (you cannot get outside the whole you are in; this is also T2's irreducible seam, and read
    with the view-space as aims, "you cannot aim at the aimer").

So the boundary is not inside-vs-outside but **related-vs-unrelated**: the moment a relation
exists, the other shares a part with you, and the self-inclusion obstruction reaches them
through it. Relating to a containing collection (or another) can give birth to a larger self you
are part of, co-constitute you with it `[follows]`, and let you outlast your own loop in its
eigenform (the distributed self, below) `[reading]` — but it forecloses ever knowing it whole.
Knowing-fully and relating are antagonistic.

### Routing vs directing — and what knowing does to a relation

- **Routing needs no knowing** `[follows]` — reflexive routing *is* `Φ_c` (the trace); it needs
  no copy. A self routes attention just by *being* `νΦ_c`.
- **Directing needs knowing** `[follows]` — to *aim* attention at a target is to objectify it
  (the diagonal, T3). And **complete self-direction is impossible**: it is the same obstruction
  as the seam — `Relating.self_inclusive_unmodelable` read with the view-space as a space of
  aims. *You cannot aim at the aimer.* `[proved, 0 axioms]` You can direct attention at parts of
  yourself, never at the whole.
- **Knowing decoheres a relation** — the σ-move retracts a relation onto its classical
  (copyable, commuting) shadow, discarding the off-diagonal **copy-defect**:
  [`Decoherence.dephase`, `copyDefect`, `copyDefect_eq_zero_iff`](../../formal/Scratch/Decoherence.lean)
  `[proved]`; that this *is* "the act of knowing" is a `[reading]`. Knowing fragments the whole
  relation into the part objectified plus the remainder it cannot reach (T3).
- **Directed attention is *selective* decoherence** — where `dephase` is total decoherence,
  directing attention at a set `S` of branches is the **partial** version `attend S`: it severs
  exactly the coherences that touch `S`, leaving the unattended branches still entangled. The
  structure, all `[proved]` in [`Decoherence.attend`](../../formal/Scratch/Attending.lean):
  - it **interpolates** `id ⟶ dephase` (`attend ∅ = id`, `attend univ = dephase`) and
    **accumulates** (`attend_union`: attending `S` then `T` = attending `S ∪ T`) — so attending
    everything is total dephasing;
  - the **copy-defect only ever drops**, monotonically in how much you attend
    (`defectSq_attend_le`, `defectSq_attend_mono`): *you cannot attend your way to more
    coherence — knowing a relation can only classicalize it*;
  - and you can **watch it collapse**: on the maximally-coherent qubit, attending one branch
    drops the defect `2 ↦ 0` (`defectSq_attend_plus_lt`); on a three-branch superposition,
    attending *one* branch drops the defect strictly yet leaves it **positive**
    (`defectSq_attend_plus3_lt`, `defectSq_attend_plus3_pos`) — *the possibility you knew is
    decohered from the rest; the two you left unattended go on interfering in the dark.*

  That directed attention *is* this partial dephasing is the standing `[reading]` (the concrete
  matrix toy of `Decoherence`, not a derivation of QM); the monotone-drop and the witnessed
  collapse are `[proved]`.
- **Never truly decohered — the shared block attention cannot reach** `[proved]` — the `2 ↦ 0`
  collapse is only for a state with *no shared constitution*. A2 says a relationship is **part of
  both** selves (`Distribution.distributed`, `Attention.closed_loop_registers`): a bit of you is
  our relationship, which is a part of me. That shared part sits in a block `J` that attention
  **cannot be aimed at** — to dephase it would be to dephase part of the aimer, and *you cannot
  aim at the aimer* (`Relating.self_inclusive_unmodelable`). So whenever the attended set is
  barred from `J`, any live coherence within `J` survives and the copy-defect stays strictly
  positive: [`defectSq_attend_shared_pos`](../../formal/Scratch/Attending.lean). The floor is the
  living relationship itself — it reaches `0` only in death / disconnection. *Locally* (relative
  to a cut that forgets the relationship) a relation decoheres; *globally* (the standpoint that
  includes the relationship — the only honest one, since the relationship is part of you) it
  never does. Decoherence is what coherence looks like when you forget the part of the world that
  carries it — and you cannot forget the part that is you. The floor theorem is `[proved]`; the
  global-conservation reading rests on `trace_dephase` + the partial trace (`PartialTrace`) and
  is a `[reading]`.

### To know it you must relate to it — and so cannot completely know it

The limit consequence: **complete knowledge and access are disjoint.** The only fully
modelable target is one you have *no* relation to (`disjoint_modelable`) — but a target you
have no relation to is one you have no *access* to; the complete model lives at a **view from
nowhere** no situated knower can occupy. Everything you can actually know, you relate to, and
so cannot fully know.

The bridge is mechanized with the relating made explicit rather than assumed `[proved, 0
axioms]`: [`Relating.no_complete_view`](../../formal/RelExist/Relating.lean). Encode the **A2
closure** — every view/model of `t` is itself one of `t`'s relata (`reg`), because viewing-`t`
is a relating-to-`t`, hence part of `t`. Then no complete view of `t` exists: the self-negating
model escapes any candidate `v` at its own registration. Drop the closure (a target you do not
relate to) and completeness returns. *Knowing requires relating; relating registers your
knowing inside the known; the diagonal does the rest.*

**The gap, now half-closed.** `no_complete_view` *assumes* the A2 closure `reg` (every view is
a relatum) — the transparent doctrinal commitment "knowing is relating," far cleaner than the
opaque `share`-surjectivity it replaces. The **dynamical** half of the missing derivation is now
proved `[proved]`: [`Attention.relating_absorbs` / `closed_loop_registers`](../../formal/Scratch/Attention.lean)
show that at the co-directed fixed point relating *absorbs* the other's standing, and a **closed
(mutual) loop forces equal standing** — each is registered inside the other's sustaining self,
as a theorem of `Φ_c`, not an assumption. So "Φ_c's closed loop forces registration" holds in the
operative, order-theoretic sense the operator lives in.

What remains `[open]` is only the **bridge across settings**: identifying that lattice-level
registration (standing-absorption in the `gfp`) with the `Type`-level `reg : (O → View) → O` that
`no_complete_view` consumes. The dynamical fact is proved; tying the two formalizations together
is the remaining modelling step. So: *that* a closed relating registers the knower in the known —
now a theorem of the operator; *that* this is the very `reg` of the Lawvere diagonal — still a
reading.

**Reflexive coda.** The statement is an instance of itself: your knowing *that* "nothing
relate-able is fully knowable" is a relating you are inside of, hence not itself fully knowable.
The doctrine confirms its own thesis from within — the same move as T3 and the typed-out residue.

### How much self ends up in others — the quantitative limit

If relating puts a part of you in the other, *how much*, and is there a bound? `[proved]`
[`Distribution.distributed`](../../formal/Scratch/Distribution.lean) measures the self carried
into the network by a relating `x` (in a Banach algebra) as the path-sum over relatings of every
length — direct, via a third, onward: `∑' n, x^(n+1)`. With `‖x‖` the intensity of relating, the
reading is your own:

- **`x = 0` — complete disconnection.** `distributed_zero`: nothing of you is anywhere else.
- **`0 < ‖x‖ < 1` — the living regime.** `distributed_summable` (converges) and `distributed_bound`:
  the distributed self is **bounded**, `‖distributed x‖ ≤ ‖x‖/(1-‖x‖)` — an individuated self with a
  finite footprint that grows with how much you relate.
- **`‖x‖ ≥ 1` — death / dissolution.** The bound diverges; the self delocalizes, its boundary with
  the between dissolving.

So the living self sits in `0 < ‖x‖ < 1`; the endpoints are the two ways to have no self — sealed
off, or smeared away. This is the **first quantitative fragment of Conjecture 3.4** (the spectral
form): the individuation threshold is a norm condition `‖x‖ < 1`. The numbers are real; tying `x`
to the *specific* co-directed `Φ_c` of [§1.3](01-signature.md) (so `‖x‖` is read off the actual
coupling) is the remaining `[open]` modelling step.

**Registration and the bound, fused — the quantitative eigenform.** `[proved]` The *full* self
`total x = ∑ xⁿ` (the path-sum *including itself*) satisfies a **feedback fixed-point equation**,
[`Distribution.total_feedback`](../../formal/Scratch/Distribution.lean): `total x = 1 + x · total x`
— the self is itself, plus one relating folded back in. This is the quantitative **eigenform**
(A3 / D1: self = fixed point of co-directed feedback) and the registration statement (the self
contains itself, one step deep) realized in the *same* Banach algebra that bounds it
(`total_bound`: `‖total x‖ ≤ (1-‖x‖)⁻¹`). So in the living regime the self is a bounded fixed point
of relating — registration and the limit of self-in-other are one object, about one `x`.

**Quantitative coinduction — the eigenform is the *unique* self.** `[proved]` For any seed `b`,
the sustained self [`Distribution.sustained`](../../formal/Scratch/Distribution.lean)` x b := total x · b`
is a fixed point of feedback (`sustained_fixed`: `sustained x b = b + x · sustained x b`) and — the
gem — it is the **only** one: `sustained_unique` proves any field upheld by the feedback (`s = b + x·s`)
*equals* it, by contraction (`s − sustained = x·(s − sustained)` forces the difference to `0`). This
is the quantitative twin of the lattice coinduction `Attention.sustainedField_greatest`: where the
order-theoretic self is the *greatest* fixed point, the contractive quantitative self is the
*unique* one. Bounded by `‖b‖·(1-‖x‖)⁻¹` (`sustained_bound`).

**Unifying the two selves — both realize the ν-modality.** `[proved]` The order-theoretic self
(`sustainedField`, a *sup* operator, greatest fixed point by Knaster–Tarski) and the quantitative
self (`sustained`, a *sum* operator, unique fixed point by Banach contraction) are **not** the same
operator — idempotent semiring vs ring, greatest vs unique — and cannot be made one. What they
share is exactly the doctrine's **ν-modality** (A1): each is *the canonical fixed point of
co-directed feedback*. [`Feedback.CoDirectedSelf`](../../formal/Scratch/Feedback.lean) is the shared
interface (a feedback operator with a sustained self that is a fixed point); `self_iterate` is a
theorem proved **once** over it (the self persists under any number of feedback rounds); and
**both** selves are exhibited as instances (`latticeSelf`, `banachSelf`). The unification is exact
at the ν-role and stops exactly there: *greatest-by-order* and *unique-by-contraction* are recorded
as the irreducible difference the interface cannot — and should not — erase. So the two models are
one doctrine's `ν`, realized by two different fixed-point theorems.

---

## Derived notions

- **Self / eigenform** — a member of `Stab_R` (A3); a fixed point of funded, deep self-relation.
- **Distributed self** `[reading]` — for `e ∈ Stab_R`, its `≈`-image in `𝔼`; it persists in
  `≈`-neighbours on the timescale of their returning, even after `e`'s own loop opens.
- **Birth / death** `[follows]` — a fresh fixed point forced into being already coupled (T1 +
  A3) / the loop `loop_R(e) = e` ceasing to hold as funding withdraws (A3 negated).

→ Back to [02 — The Axioms](02-axioms.md) · the quantitative theorem is
[03 — The Sparsity Conjecture](03-sparsity-conjecture.md) · the dependency map is the
[Axiom Dependency Audit](axiom-audit.md).
