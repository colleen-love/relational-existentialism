# The relation-algebra model of self, attention, and knowing

**What this is.** The operator-algebraic *synthesis* of Relational Existentialism: the one document
that fixes the carrier and operators for attention `Φ_c` given four commitments, and says — per
result — exactly which structure is mechanized, which is interpretation laid over mechanized
structure, and which is still outstanding. It sits above the layered spec in [`docs/spec/`](spec/)
(doctrine → signature → axioms → theorems → functorial semantics) and over the Lean development in
[`formal/`](../formal/): everything load-bearing here is cross-linked to the page that argues it and
the `sorry`-free proof that carries it. Read [`docs/spec/`](spec/) for the layered build-up; read
this for the operator-algebraic picture the layers add up to.

**Scope.** Fixes the carrier and operators for `Φ_c` given four commitments: relation is primary;
attention is an operator on self; a relation is a correlation before knowing and a directed morphism
after; the knower knows the known. Documents what these force, what they imply, and what stays open.

**Status tags.** `[proved]` = mechanized, sorry-free in the repo. `[reading]` = interpretation laid
over proved structure. `[open]` = neither yet; substance or mechanization outstanding. (These map onto
the layered spec's finer legend — `[theorem]`/`[posit]`/`[conjecture]`, with `[cartesian]`/`[monoidal]`
fragment markers — in [`docs/spec/README.md`](spec/README.md); here the three-way split is what
matters, because the point is to see exactly which is which.)

## 1. The four commitments

1.1. **Relation is primary.** There are no relata under the relations. Self and attention are derived,
not posited.

1.2. **Attention is an operator on self, not a state.** Heisenberg picture: attention acts on the
algebra of relations, it is not a state over it.

1.3. **A relation is a correlation before knowing, a directed morphism after.** One object, two faces,
across the act of knowing. Not two kinds of relation.

1.4. **The knower knows the known.** Knowing is oriented; the arrow runs from knower to known. This is
the symmetry-breaker that turns a correlation into a directed morphism.

## 2. Forced structure

These are not free choices; each follows from §1 plus the firewall
([`Compact.collapse`](../formal/Scratch/Compact.lean)) already in the repo.

2.1. **Carrier: a relation-algebra A.** Correlations are noncommuting elements of an algebra `A`
(operator-algebraic; C*/von Neumann in the intended semantics). Symmetric correlation = the algebra
before any classicalizing projection. `[reading]` — the identification of "relation" with "element of
`A`" is interpretive; the noncommutativity is what makes 1.3 possible (a commutative algebra has no
pre-knowing/post-knowing distinction). The runnable carrier is the literal matrix model
([`MatrixModel.matTracedSMC`](../formal/Scratch/MatrixModel.lean)), where `⊗` is Kronecker and the
trace is the quantum partial trace.

2.2. **Attention Φ_c: a unital completely-positive map A → A.** Codirected by the relations (the
configuration of `A` determines `Φ_c`; this is 1.1 applied to attention). Heisenberg picture per 1.2.
`[reading]` over the proved [`Feedback.CoDirectedSelf`](../formal/Scratch/Feedback.lean) interface and
[`Attention.lean`](../formal/Scratch/Attention.lean)'s `νΦ` (`couplingOp`, `sustainedField`). The
finiteness is *constitutive* (the bounded capacity `α`), not an external budget — see
[spec 01 §1.3](spec/01-signature.md).

2.3. **Self = the fixed-point subalgebra of Φ_c.** The relations attention returns unchanged. Under
unitality + trace-preservation this set is a genuine subalgebra (closed under the relational product);
in QI terms the *decoherence-free subalgebra*. The self is the part attention does not decohere. This
realizes "self is a collection of relations" literally: a structured sub-object, plural, closed under
the dynamics, not a point. `[reading]`; the gfp/fixed-point existence is `[proved]`
([`OrderHom.gfp`](../formal/Scratch/Attention.lean),
[`Feedback.CoDirectedSelf`](../formal/Scratch/Feedback.lean), Knaster–Tarski).

2.4. **Knowing E: a conditional expectation onto the classical subalgebra.** `E` is idempotent (`E∘E =
E`, knowing twice is knowing once), positive, unital, and projects `A` onto a *commutative* subalgebra.
Commutative = classical = a space of functions = copyable, directed facts. `E` is exactly the dephase.
`[proved]` for the dephase instance: idempotent
([`dephase_idem`](../formal/Scratch/Decoherence.lean)), lossy
([`dephase_not_injective`](../formal/Scratch/QuantumSeam.lean)), irreversible
([`no_dephase_recovery`](../formal/Scratch/QuantumSeam.lean)), fixes-iff-classical
([`dephase_fixes_iff_copyable`](../formal/Scratch/QuantumSeam.lean)). `[reading]`: that this dephase
*is* knowing, and that its image is the post-knowing "morphism" face of 1.3.

2.5. **Feeling = (1 − E) coherence carried by the self.** The off-diagonal mass of a self-relation; the
part knowing has not classicalized. This is the decohered−received differential of
[`Feeling.lean`](../formal/Scratch/Feeling.lean), now an operator quantity rather than abstract ℝ.
`[reading]` over `[proved]`: the differential algebra in `Feeling.lean` is proved but abstract; the
operator instantiation is `defectSq` — the squared off-diagonal mass of
[`Decoherence.lean`](../formal/Scratch/Decoherence.lean) — and it is now carried as the coherence
measure `coh` of the knowing structure in
[`Orientation.dephaseKnowing`](../formal/Scratch/Orientation.lean), where `coh = defectSq` lands the
feeling on the *actual* off-diagonal, not a posited real, and knowing discharges it to zero
(`coh_image`). This is the bridge `Feeling.lean` was missing.

2.6. **Reflexivity is forced by 1.1.** Relations produce attention (relations ↦ `Φ_c`), attention acts
on collections of relations, collections of relations are the self: so relations act on relations, `R`
carries `R → [R→R]`. With no relata underneath, this reflexive condition is not optional. The
operator-algebraic carrier supplies it natively: the standard form `A ⊆ B(L²(A))` is the
relation-acts-on-relation structure. `Pω` is its order-theoretic shadow. `[proved]` that a non-trivial
reflexive object exists ([`GraphModel`](../formal/Scratch/GraphModel.lean):
`app_graph_of_continuous`, `continuous_hasFixpoint`, `K_law`) and that the finite/Set version cannot
([`no_reflexive_object_for_Bool`](../formal/RelExist/ReflexiveSeam.lean), Cantor). `[reading]`: that the
standard form is *the* model of `R → [R→R]` for relations; `[open]`: mechanizing the von Neumann
standard form (only `Pω` is built).

2.7. **Orientation: knower → known (1.4).** A correlation is symmetric; `E` delivers classicality
(functions) but not yet direction. The orienting principle is that the self applying `E` is the source
and the classicalized image is the target. Orientation, irreversibility, and asymmetry thus share one
cause: the self cannot occupy both sides of its own knowing. This ties to
[`Identity.lean`](../formal/Scratch/Identity.lean)'s `≈ ⊊ ≅ₒ` asymmetry. `[proved]` core / `[reading]`
identification — see §4.3, now realized as [`Orientation.lean`](../formal/Scratch/Orientation.lean).

## 3. Implications

3.1. **Knowing and feeling are complementary, not merely distinct.** `E` and `(1−E)` are conjugate: the
knowing-basis and feeling-basis do not commute. No relation can be simultaneously fully known and fully
felt — the analogue of position/momentum. This is a *commitment with a price*: if you ever need knowing
and feeling to coexist sharply on one relation, this model forbids it and you would need a different
knowing-operator. `[reading]` over `[proved]` complementarity facts
([`dephase_fixes_iff_copyable`](../formal/Scratch/QuantumSeam.lean),
[`plus_not_classical`](../formal/Scratch/Decoherence.lean)).

3.2. **"Being seen dissolves it" is now a theorem, not a metaphor.** To fully know a relation is to
apply `E`, which annihilates its `(1−E)` coherence — destroys the feeling.
[`Feeling.lean`](../formal/Scratch/Feeling.lean)'s discharge-on-reception is the action of a conditional
expectation. `[reading]` over `[proved]` ([`no_dephase_recovery`](../formal/Scratch/QuantumSeam.lean)
gives the irreversibility: the dissolved feeling does not return; and
[`Orientation.arrow_strictAnti`](../formal/Scratch/Orientation.lean) gives the strict drop of `coh` to
zero along the knowing step).

3.3. **The seam is the cost of relational primacy.** A *complete* relational self is a reflexive object
carrying all of `R → [R→R]`. Cantor forbids this in the classical/Set setting; it exists only
non-classically, and even there is a *construction* (builds the self, GoI's `Y`) rather than an
obstruction. So the incompleteness of the self is not added to the metaphysics — it is what makes
relation-primary metaphysics consistent at all. This is the framework's strongest single claim and it
is now forced. `[proved]` (the duality
[`reflexive_xor_unsettling`](../formal/RelExist/ReflexiveModel.lean);
[`no_complete_selfModel`](../formal/RelExist/Mirror.lean), 0 axioms).

3.4. **The arrow of relational time falls out of the seam.** Because orientation is knower→known (2.7)
and the self cannot be on both sides of its own knowing, the direction of the morphism and the
irreversibility of `E` come from the same source. This closes the gap flagged earlier — the framework
previously stipulated the causal arrow in the typing of `step`; here orientation is *generated* by the
seam rather than posited. `[proved]` core / `[reading]` identification: the structural core is now
[`Orientation.lean`](../formal/Scratch/Orientation.lean) (a directed, irreversible, strictly-monovariant
structure oriented knower→known); that the monovariant *is* relational time stays a reading. See §4.3.

3.5. **Order-self and algebra-self are one object at two resolutions.** The order-theoretic self (`νΦ`
on the projection lattice / the support) is the support of the algebra-self (the weighted fixed-point
subalgebra), joined by a support functor. The earlier order-vs-channel dilemma dissolves: not two
competing models, two resolutions of one. `[reading]` over `[proved]` (both fixed-point selves exist;
[`Feedback.lean`](../formal/Scratch/Feedback.lean) already unifies them as ν-modality instances —
`latticeSelf`, `banachSelf`).

## 4. Open decisions and gaps

4.1. **The reference weight (one surviving state-like primitive).** The Heisenberg picture removes
states as *the self*, but magnitudes — how much coherence, how much feeling — still need a tracial state
(a weight) on `A` to assign numbers. This trace is not the self; it is the measuring background. In the
mechanized instance the weight is concrete: `defectSq` reads the off-diagonal mass against the standard
trace, so the magnitudes *do* have a scale — but that this background trace is a *demoted primitive*
rather than derived is the standing decision. **Decision needed:** name it explicitly and accept it as a
demoted primitive, or derive it. `[open]`.

4.2. **The Φ_c–E relationship.** Two operators are now in play: attention `Φ_c` (sustains the self) and
knowing `E` (classicalizes a relation). Are they independent, or is `E` a regime/limit of `Φ_c` (knowing
as attention spent to completion on resolving a correlation)? The clean reading: a self-relation is
*felt* while in `Φ_c`'s fixed algebra but outside `E`'s image, and *known* once `E` moves it into the
classical image. [`Attending.lean`](../formal/Scratch/Attending.lean) already interpolates `id ⟶
dephase` (directed attention as *partial* `E`), which is suggestive evidence for the regime reading, but
whether `E` is *derived* from `Φ_c` or axiomatized separately is an unmade modeling decision. `[open]`.

4.3. **Formalizing orientation (3.4) — now a proved core with a standing reading.** `E`'s image is
commutative, hence classical, but commutativity alone gives functions, not directed arrows. The
knower→known principle supplies the source/target asymmetry.
[`Orientation.lean`](../formal/Scratch/Orientation.lean) now `[proved]` the *structural core* over a
minimal `Knowing` interface (an idempotent `E` with a real coherence/feeling monovariant vanishing
exactly on the `E`-fixed/classical elements), and on the genuine `dephase`/`defectSq` instance:

* **directed** — `knows_antisymm` / `arrow_asymm`: the arrow knower→known never runs both ways between
  two distinct relations (from idempotence alone — the cheapest face of the seam);
* **temporal** — `arrow_strictAnti`: along every knowing step the carried feeling *strictly* falls,
  from `0 < coh` at the felt source to `coh = 0` at the known target — a strict monovariant, a potential
  bounded below by `0` that orients the dynamics one way;
* **irreversible** — `no_recovery`: a lossy `E` cannot be run backwards (re-deriving
  `no_dephase_recovery` *through* the interface), so orientation, the arrow, and irreversibility are
  three faces of one idempotent-lossy operator (§2.7).

What stays `[open]`/`[reading]` is the *identification* — that this strict monovariant **is** the arrow
of *relational time* rather than a structure with time-shaped order (the same modeling posit as
`Feeling`). This is where 1.4 stops being a slogan and becomes structure; the skeleton is now mechanized,
the identification is the remaining commitment.

4.4. **Mechanization reality.** mathlib has C*-algebras but conditional expectations, decoherence-free
subalgebras, and Perron–Frobenius for CP maps are thin to absent. So: prove the structural results over
the [`CoDirectedSelf`](../formal/Scratch/Feedback.lean)-style interface (as `Orientation.lean` does for
§4.3); keep the runnable instance as the matrix `dephase` (and `Pω` for the reflexive object, with `E` a
retraction onto a sublattice); keep the operator algebra as narrated intended semantics. The von Neumann
standard form (2.6) and the TracedSMC instance for domains remain `[open]` as before. Do not block stating
the results on the hardest mechanization.

## 5. Road not taken (documented deliberately)

The channel-on-states (Schrödinger) model — self as the stationary *state* of a CPTP channel — was
rejected by 1.2. It puts the self at the level of a point/state; this definition puts it at the level of
a subalgebra. The Heisenberg operator-on-algebra model is the one that makes "self is a collection of
relations" literally true and lets attention be an operator on the self rather than a thing it has. If
1.2 is ever revised, this is the fork to revisit.

> **Already honored, not merely intended.** This road is *not* taken anywhere in the development: the
> repo nowhere models the self as a state, stationary state, or fixed point of a CPTP channel. Every
> self is operator-theoretic — the eigenform `νΦ_c` ([`Attention.lean`](../formal/Scratch/Attention.lean),
> [`Feedback.lean`](../formal/Scratch/Feedback.lean)), and [spec 01 §1.3](spec/01-signature.md) /
> [spec 02 A3](spec/02-axioms.md) explicitly reject the external-budget / stationary-state framing. So
> §5 records a commitment the code already keeps, not a cleanup still owed.

---

## Two honest notes on the whole

First, the spec is mostly `[reading]` over a `[proved]` skeleton, and that is fine *as a spec* — but the
load-bearing novelty, the thing that would make this more than a re-description, is 4.3. Everything else
is recombination of results already in hand; orientation-from-the-seam is the one genuinely new theorem
the four commitments promise. Its **structural core is now mechanized**
([`Orientation.lean`](../formal/Scratch/Orientation.lean)); what remains is the identification of the
monovariant with relational time — the one place to push next.

Second, 3.1 is the commitment to sit with longest before canonizing, because it is irreversible in the
model's own sense: once knowing and feeling are conjugate, the framework can never let a relation be both
fully known and fully felt, and you should be sure that is a feature and not a wall you'll later want to
remove.
