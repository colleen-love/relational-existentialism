# Axiom Dependency Audit

> *Which commitments does the theory **assume**, and which does it **prove**?* This
> document separates the two cleanly — a **basis** (taken, including the ambient structure
> as a first-class axiom) and the **theorems** built on it — and records, for each basis
> item, the **independence** evidence that it is not derivable from the rest. Every
> mechanized claim carries its verified `#print axioms` footprint. Bottom line: the basis
> is four items, and only **one** of them (A4) is a load-bearing wager.

---

## Two ledgers, two meanings of "axiom"

"Axiom" is overloaded here, and the audit is mostly the work of separating the two:

1. **Doctrine basis** — the commitments the theory takes as given (this page, §"The basis").
2. **Logical axioms** — Lean's foundational axioms (`propext`, `Classical.choice`,
   `Quot.sound`), what `#print axioms` reports. A result reported as depending on *no*
   axioms is fully constructive and foundation-free in Lean's sense.

These are tracked in separate columns. A doctrine *theorem* (e.g. A6's σ-side) can have an
empty *logical*-axiom footprint — "proved, and proved constructively."

---

## The basis — what the theory assumes

Four items, taken not proved. The ambient structure is listed first and explicitly: in Lean
it is a *hypothesis* (a `structure`/typeclass), not an `axiom` keyword — but it **is** an
assumption, and honesty puts it in the basis with the rest.

| | Basis item | Kind | Content |
| --- | --- | --- | --- |
| **A0** | **The ambient structure** | `structural` | A traced symmetric monoidal category with a distinguished **cartesian fragment** and a **ν-modality** (greatest fixed points / final coalgebras). The doctrine of [00](00-doctrine.md). Everything below is stated and proved *relative to A0*. |
| **A1** | **Relation primacy** | `structural` | Identity is exhausted by contextual behavior — no bare carrier under the relatings (Yoneda as a commitment). The extensionality premise. |
| **A2** | **Self-relation is feedback** | `definitional` | `σ := Tr`. A definition: it fixes the referent of self-relation and contributes **no** logical strength. |
| **A4** | **Recursion constitutes the self** | `posit` | The **selection criterion**: co-directed recursion under constitutive finiteness is what promotes a fixed point to a self. The **one discriminating wager**. |

That is the whole of what is assumed. Note what is *not* here: A3, A5, A6 — they are
theorems (next section). And note the internal structure of A4: only the *selection* is
posited; the *existence* of the fixed points it selects among is A3 + Knaster–Tarski, and
the cost-floor `2 ≤ d·λ` is a theorem (`two_le_selfCost`).

---

## The theorems — what the theory proves

Everything else is derived from the basis, and is what further results are built on. The
three commitments that are *theorems*, first:

| | Theorem | Proved from | Lean name | `#print axioms` |
| --- | --- | --- | --- | --- |
| **A3** | To relate is to create (Conway fixed points exist) | A0 (traced/cartesian) + Knaster–Tarski (Hasegawa–Hyland) | `Trace.{selfTrace_fixed, le_Tr, Tr_fixed, Tr_mono}` | `propext, Quot.sound` |
| **A5** | Observational identity `≈ := νΘ`; the shared world `𝔼 := D/≈`, coinciding with A1's `≡` | A0 (ν-modality) + A1 (identity criterion) | `We.{bisim_unfold, bisim_coind, bisim_refl, World}` | `propext, Quot.sound` |
| **A6** | Knowing (`σ`) is Lawvere-obstructed; feeling (`≈`) is whole | A0 (the cartesian fragment / a fixed-point-free endomap) | `Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}`; `KnowingFeeling.*` | **none** (σ-side); `propext, Quot.sound` (`feeling_is_whole`) |

Then the downstream theorems — the layer "from which we build more," all proved over the
basis + the three above:

| Theorem | Lean name | `#print axioms` |
| --- | --- | --- |
| A4 bridge: `loop_R(e)=e ⟺ d·λ ≤ β` | `loopR_isEigen_iff` | `propext` |
| A4 cost-floor: `2 ≤ d·λ` | `two_le_selfCost` | `propext` |
| Sparsity (Lemma 3.1): `\|Stab\| ≤ β/(d·λ)` | `stab_card_le_div` | `propext` |
| Sparsity density → 0 (ℝ) | `Real.stab_density_tendsto_zero` | `propext, Classical.choice, Quot.sound` |
| Firewall collapse / no-cloning (categorical) | `Compact.{collapse, no_cloning}` | `Quot.sound` |
| No-cloning, concrete (cloning is nonlinear) | `NoCloning.no_linear_clone` | `propext, Classical.choice, Quot.sound` |
| Matrix model: trace = partial trace | `MatrixModel.matTracedSMC` | `propext, Classical.choice, Quot.sound` |
| Decoherence retraction + copy-defect | `Decoherence.{dephase, copyDefect, classical_comm}` | `propext, Classical.choice, Quot.sound` |
| Coinductive `≈` + topological sparsity (Agda) | `RelExist.Coinductive`, `RelExist.Sparsity` | (Agda `--safe`, no postulates) |
| Free traced SMC `Cl(𝕋)` + universal functor | `Free.{clTracedSMC, functor, functor_unique}` | `Quot.sound` |

So the dependency flows one way: **A0, A1, A2, A4 ⟹ A3, A5, A6 ⟹ everything else.**

---

## Independence — what each basis item earns

A basis is honest only if no item is secretly derivable from the others. Independence is
shown the standard way: for item X, a model that satisfies the rest but **fails X**.

| Basis item | Independent because… | Witness | Status |
| --- | --- | --- | --- |
| **A4** | dropping the selection (unbounded budget, `β = ⊤`) makes `Stab = Φ` — the trivial / universal-solvent model, which satisfies A0–A2 but not A4's discrimination | `unbounded_without_budget` (Lemma 3.2) | ✅ **mechanized** (`propext`) |
| **A0** | A2, A3, A5, A6 cannot even be *stated* without the traced/ν structure — A0 is their precondition | (structural: removing A0 removes the language) | argued |
| **A1** | a non-extensional model — one with a "bare carrier," hidden state beyond behavior — satisfies A0 but violates A1 (`≡` is no longer the finest congruence) | a model where `D` carries un-observable state | argued (not yet a Lean model) |
| **A2** | a definition, not a separable assumption — "independence" does not apply; it fixes notation and adds no logical content | — | n/a (definitional) |

The one that matters — **A4** — is the one with a *mechanized* witness: the theory provably
says nothing without it (`unbounded_without_budget`), and the sparsity theorem is what it
buys. The others are a structural precondition (A0), an extensionality premise (A1), and a
naming choice (A2). This is exactly the "A4 is doing all the discriminating work" claim,
made legible.

---

## Three honest caveats

**1. A0 is an assumption, now named as one.** Listing the ambient structure as a basis
axiom is the point of this revision: a result that reports "0 logical axioms" is still
proved *over A0*, whose typeclass fields are themselves commitments. "Axiom-free" always
means "free of *logical* axioms, over the stated structure" — never "free of assumptions."

**2. A4 cannot be derived away — that is the content, not a gap.** Its independence witness
is also its justification: remove it and the theory is the empty (universal-solvent) one.
The goal was never zero posits but the **right** one.

**3. A fully self-grounding basis would contradict A6.** To derive *all* of the theory's
commitments from nothing is a complete self-model — the σ-move that `Mirror.lawvere` proves
obstructed. The theory predicts its own irreducible basis; this audit confirms it from the
outside (the basis is non-empty, necessarily).

---

## What would make the reduction end-to-end machine-checked

This audit assembles results proved across modules. Two steps would turn "basis of four,
one posit" into a single checked development:

1. **One `Doctrine` typeclass.** Bundle A0 (traced SMC + cartesian fragment + ν-modality)
   as one structure, and re-derive A3/A5/A6 *as theorems over it* in one file — so the
   `basis ⟹ theorems` arrow is checked, not cross-referenced.
2. **Independence models, mechanized.** Promote the argued rows above to Lean: the
   non-extensional model (A1), and an explicit everything-but-A4 instance (A4) beyond the
   counting witness. The A4 case is already essentially `unbounded_without_budget`.

→ Back to [02 — The Axioms](02-axioms.md) · the discriminating posit's payoff is
[03 — The Sparsity Conjecture](03-sparsity-conjecture.md).
