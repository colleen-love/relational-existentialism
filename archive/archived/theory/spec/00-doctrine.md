# 00 — The Doctrine

> **Transitional (handoff I.I).** With paper one now the foundation, the **authoritative** plain-language
> statement of the arena is [`paper-1/spec/00-domain.md`](../../paper-1/spec/00-domain.md) (the arena + the
> decoupling that lets a self be *derived*). This essay is retained as the fuller transitional reference and
> will be **dissolved into paper one in the formalization pass**; do not extend it. Read it through paper
> one's derive-don't-define stance.

> **Normalized axioms (handoff XX/XXI) — read alongside [`AXIOMS.md`](AXIOMS.md).** This essay predates the
> axiom normalization; read its axiom references through the canonical four: **A3 is now a *process***
> (relations co-direct attention asymmetrically in the relata), with the **self its *derived* fixed point**,
> not a posited eigenform; **D1** generalizes `σ = Tr` to the **modular flow** (the trace its
> infinite-temperature limit); **A1** is one dimension-generic arena. The four axioms are one canonical,
> version-pinned layer in `theory/`.

> *What the language is allowed to say.* Before any axiom, we fix the ambient
> mathematical universe in which "relating" is a primitive and "self" is a derived
> notion. This is the **doctrine**: a traced symmetric monoidal category extended
> with greatest fixed points, carrying a distinguished cartesian fragment.

The doctrine is chosen so that each of its three ingredients is load-bearing for a
specific philosophical commitment, and so that the one place the philosophy is
*lived* but the mathematics *generalizes* — the cartesian/monoidal seam — is
visible rather than hidden.

---

## 0.1 Why a category, and why morphisms first

A category `𝒞` consists of objects and, between them, morphisms that compose
associatively with identities. We read it relationally:

- **objects** `A, B, …` are *system-types* — the kinds of thing that can stand in
  relation;
- **morphisms** `f : A → B` are *relatings* — a relating *of* `A` *to* `B`;
- **composition** `g ∘ f` is *relating through* an intermediary.

This is already the inversion of the plain-language doc made structural: in a
category you cannot speak of an object except via the morphisms into and out of it
(Yoneda). An object's identity *is* its pattern of relatings. Relation is primitive;
the object is what the relatings determine. Axiom **A2** will make this precise.

We do **not** start from a category of "selves with relations attached." We start
from relatings, and selves appear only later, as fixed points (Axiom **A3**).

---

## 0.2 Symmetric monoidal structure — coexistence

A **symmetric monoidal category** (SMC) `(𝒞, ⊗, I, γ)` adds:

- a **tensor** `⊗ : 𝒞 × 𝒞 → 𝒞`, with `A ⊗ B` read as *`A` and `B` coexisting*;
- a **unit** `I` (the empty system; states of `A` are points `I → A`);
- coherent associators and unitors;
- a **symmetry** `γ_{A,B} : A ⊗ B → B ⊗ A` with `γ_{B,A} ∘ γ_{A,B} = id`, read as
  *coexistence is order-indifferent*.

`⊗` is not "and" as set-theoretic pairing; it is parallel coexistence with no
implied communication. Communication is a *morphism* between tensored systems.
This is the fragment in which **relation-primacy (A2)** is native: morphisms are the
data, objects are bookkeeping.

`[structural; both]`

---

## 0.3 Trace — self-relation as feedback

A **trace** turns an output back into an input. A traced SMC equips `𝒞` with, for
all `A, B, U`, a function

$$
\mathrm{Tr}^{U}_{A,B} : \mathcal{C}(A \otimes U,\; B \otimes U) \;\longrightarrow\; \mathcal{C}(A,\;B)
$$

— "feed the `U`-output back into the `U`-input" — subject to the standard
Joyal–Street–Verity axioms:

1. **Naturality** (in `A` and `B`): tracing commutes with pre/post-composition on
   the non-fed wires.
2. **Dinaturality / sliding** (in `U`): a map on the feedback wire may slide around
   the loop.
3. **Vanishing I**: `Tr^I_{A,B}(f) = f` (feeding back the empty wire does nothing).
4. **Vanishing II**: `Tr^{U⊗V} = Tr^{U} ∘ Tr^{V}` (a compound loop is two loops).
5. **Superposing**: tracing is compatible with `⊗` (you may carry a bystander wire
   `W` through the loop).
6. **Yanking**: `Tr^{U}_{U,U}(γ_{U,U}) = id_U` (a loop with a single crossing is a
   straight wire).

The trace is the formal content of **self-relation**: a relating whose output is
returned to itself. Crucially, the trace needs **no copying** — it is definable in
compact-closed categories like `FdHilb` (where it is the partial trace). This is
what lets self-relation *as feedback* survive into the quantum fragment, even
though self-relation *as mirror* (next section) will not.

We name the unary self-relation operator

$$
\sigma(P) \;:=\; \mathrm{Tr}(P)
$$

`[structural; both]` — this is the operator the philosophy calls the *σ-move*, the
turning of a relating back on itself. Definition **D1** records the definition; Theorem
**3.3** records its cartesian obstruction.

---

## 0.4 The cartesian fragment — copying, and the mirror

A category has **finite products** when `⊗` is the categorical product `×` and `I`
is terminal `1`. Such a category is automatically symmetric monoidal, but with two
extra natural transformations available at every object:

- the **diagonal** `Δ_A : A → A × A` — *copy*;
- the **delete** `!_A : A → 1` — *discard*;

making every object a commutative comonoid, *naturally* in `A`. The hallmark of the
**cartesian fragment** `𝒞_×` is exactly the presence of a uniform, natural `Δ`.

Two facts make `𝒞_×` the home of the philosophy-as-lived:

### 0.4.1 Trace in `𝒞_×` is a Conway fixed-point operator `[theorem; cartesian]`

**Theorem (Hasegawa; Hyland).** On a category with finite products, traces are in
bijection with **Conway fixed-point operators** — operators
`(–)^† : 𝒞(A × X, X) → 𝒞(A, X)` satisfying the Conway identities (naturality,
dinaturality, the diagonal/Bekič rule). Consequently every endomorphism arising by
feedback *has* a fixed point, canonically.

This is the precise sense of **"to relate is to create"** (Theorem **3.1**): in the
cartesian fragment, looping does not merely rearrange — it *produces* a fixed
point that need not have pre-existed. Self-relation manufactures structure. (Caveat on the
mechanization: [3.1 as *proved*](../../paper-2/spec/paper-two.md) is only the Knaster–Tarski **greatest fixed point**
of a monotone map; the Hasegawa–Hyland trace↔Conway-operator bijection cited here is *not* verified
in the Lean — a gfp existing is generic to every monotone operator.)

### 0.4.2 The mirror that can't close is Lawvere's theorem `[theorem; cartesian]`

**Theorem (Lawvere).** In a cartesian closed category, if there is a
point-surjective morphism `A → B^A`, then **every** endomorphism `t : B → B` has a
fixed point. Contrapositive: if some `t : B → B` is *fixed-point-free*, then there
is **no** point-surjective `A → B^A` — no complete self-representation of `A`'s
function space inside `A`.

Read this as the **mirror that can't close**. A total self-model is a surjection of
a system onto its own space of self-relatings; Lawvere says the existence of any
"escaping" endomorphism forbids it. The diagonal `Δ` is exactly the move that makes
the diagonal argument run: *you must copy yourself to compare the copy against the
original*, and the comparison always produces a residue the copy omits. The
incompleteness of self-knowledge is not contingent; it is the contrapositive of a
theorem, and it lives precisely where copying is available.

`[theorem; cartesian]`

---

## 0.5 Greatest fixed points — the `ν`-modality

For an endofunctor `F : 𝒞 → 𝒞`, an **`F`-coalgebra** is a map `x : X → F X`, and a
**final** coalgebra `out : νF → F(νF)` is terminal among them. Its carrier `νF` is
the **greatest fixed point** of `F`; the unique map into it is definition by
**coinduction**, and the proof principle is: *to show two states equal in `νF`,
exhibit a bisimulation*.

The doctrine is extended with a **`ν`-modality** giving, for the endofunctors we
need, their final coalgebras. Two uses:

- **Becoming.** A self is not a static datum but an *ongoing behavior*; behaviors
  are the canonical inhabitants of final coalgebras (streams, processes, eigenforms
  under continued return). The `ν`-layer is where "maintained rather than given"
  becomes a type, not a metaphor.
- **The "we".** Lived identity `≈` (the greatest bisimulation) is defined coinductively as the greatest
  relation closed under one step of mutual indistinguishability — a **bisimilarity**
  — and the shared world is the quotient `𝔼 := D/≈`. Theorem **3.2** is stated here.

`[structural; both]`

---

## 0.6 The seam — stated, not hidden

The two readings of self-relation come apart, and the doctrine is honest about it.

> **Proposition 0.1 (the seam).** Let `𝒞` be the ambient doctrine.
>
> 1. In the **cartesian fragment** `𝒞_×`, the obstruction to a complete self-model
>    is **Lawvere's diagonal argument**: it *requires* `Δ`, and the residue it
>    produces is the philosophy's *remainder* (§"Knowing and feeling").
> 2. In a **compact-closed (e.g. quantum) fragment** there is, by **no-cloning**,
>    no natural diagonal `Δ_A : A → A ⊗ A` at all. Here the analogous obstruction is
>    the *absence* of copying, **not** a fixed point of it.

The two obstructions are genuinely different mathematics — a fixed-point/diagonal
theorem versus a no-go on a natural transformation existing. The philosophy as
*lived* (a someone who looks at themselves and cannot close the loop) is the
**cartesian** story. The monoidal generalization buys **quantum reach** (Layer 4's
physics functor) at the cost of the literal mirror reading.

**Methodological consequence.** All the self-reference results — **D1's** mirror reading,
**3.1**, **3.3** — are stated in the cartesian fragment. The compact-closed fragment
inherits only what is fragment-neutral (`⊗`, `Tr`-as-feedback, `≈`). We never write
"`Δ`" in the quantum fragment, and Layer 4 will turn this discipline into a typing
theorem (no monoidal functor from the compact-closed fragment into the
cartesian-only domains).

`[structural; both]`

> **Proposition 0.2 (the seam is the non-comonoidal residue — one object, two faces).** Proposition 0.1
> records the two obstructions as *different proofs*. They are nonetheless **one object**. By **Fox's
> theorem**, *classical / copyable / cartesian* is a single notion: **carrying a natural copy comonoid**
> `Δ` (the hallmark of §0.4). So both faces are read off the *same* `Δ`: the cartesian face (Lawvere)
> **uses** the copy — the escaping diagonal `g a a` is `Δ` fed back in — and the monoidal face
> (no-cloning) is the **absence** of that copy. The seam is then *defined* as the part of the state space
> that carries no copy. Mechanized (`sorry`-free): abstractly in
> [`RelExist/Fox.lean`](../../archive/formal/Archive/RelExist/Fox.lean) — `Comonoid`, the cartesian instance, and
> `faces_share_copy` (Lawvere's remainder and broadcastability over one `Comonoid.copy`, **0 axioms**);
> concretely in [`Scratch/SeamComonoid.lean`](../../archive/formal/Archive/Scratch/SeamComonoid.lean) — the copyable
> fragment is exactly the diagonal (`IsClassical`) states (`cartesian_iff_copyDefectFree`), a seam state
> with a live coherence carries **no** copy and **no available knowing recovers it**
> (`seam_is_noncomonoidal_residue`, via `SeamForcing.attend_fixes_seam`), and a **self-inclusive** seam
> forces such a state to exist (`self_inclusion_forces_residue`). The headline
> `seam_is_the_common_obstruction`: every seam state carries a copy **iff** the seam has no genuine
> between — so the self, being self-inclusive, is at once **uncopyable, non-broadcastable, and
> incompletely self-knowable: three names for one missing comonoid.** `[proved]` (the structural core).
> The **categorical hallmark** itself — *cartesian ⇒ the natural copy `Δ` exists and is unique (forced to
> be the diagonal), with `Comon_ C ≌ C`* — is now mechanized over a genuine monoidal category in
> [`Scratch/FoxTheorem.lean`](../../archive/formal/Archive/Scratch/FoxTheorem.lean) (`cartesianComonoid`,
> `comonoid_forced`, `foxEquivalence`, via mathlib's categorical-quantum library), so §3.2's forward
> direction is **proved, not cited**. `[reading]`: only the **reverse** Fox direction (a symmetric
> monoidal category with a natural comonoid on every object is cartesian — the classical hard half, not in
> mathlib) stays cited, and the ontological gloss (cartesian = It, monoidal = Thou, the self straddling).

---

## 0.7 What each ingredient buys — summary

| Doctrine ingredient | Formal device | Philosophical work | Fragment |
| --- | --- | --- | --- |
| Relation-primacy | morphisms primitive; Yoneda | the self is determined by its relatings | both |
| Coexistence | `⊗`, `I`, symmetry `γ` | parallel being without implied communication | both |
| Self-relation as feedback | trace `Tr`, `σ := Tr` | looping / return, copy-free | both |
| To relate is to create | `Tr` = Conway operator | looping produces fixed points | cartesian |
| The mirror can't close | Lawvere's theorem | self-knowledge leaves a remainder | cartesian |
| No-cloning analogue | absence of natural `Δ` | the quantum reach, mirror *not* literal | monoidal |
| Becoming, the "we" | final coalgebras, `ν`, bisimilarity | maintained selves; shared world `𝔼` | both |

The next file fixes the **signature**: the specific sorts and generators — including
attention as a bounded resource — that present this doctrine as the theory `𝕋`.
