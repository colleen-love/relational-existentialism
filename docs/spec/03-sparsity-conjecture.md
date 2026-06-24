# 03 — The Sparsity Conjecture

> *The one place the spec reaches for a theorem.* Everything before this is
> definition, citation, or posit. Here is the candidate **result** — the claim that,
> if proved, turns "a self is an achievement of recursion" from an assertion into a
> theorem of `Cl(𝕋)`.

---

## 3.1 The claim, informally

> **Under a finite attention budget, selves are rare.**
>
> If the budget `β` is finite (and per-return cost `ε > 1`, stabilization depth
> `d ≥ 2`), then the carrier of stabilized selves `Stab_R` is **sparse** among all
> couplings: its size is bounded by a constant depending only on `(β, ε, d)`, not on
> how many relations the system has. As the system's stock of relations grows, the
> *fraction* that become selves tends to `0`.
>
> Remove the bound (`β = ⊤`) and the statement fails completely: **every** loop
> closes, every coupling stabilizes, and the theory says nothing.

This is the **expressivity/triviality dial** made into a dichotomy. Bounded budget =
discriminating theory; unbounded budget = universal solvent.

> **Two readings of "rare," and which is primary.** Since [§1.3](01-signature.md)
> recast attention as the **co-directed operator** `Φ_c` rather than a spent budget,
> the *deep* reason selves are rare is no longer a budget cap — it is **spectral /
> closure**: under co-directed feedback with gain, only a few eigenforms sit near the
> top of the spectrum and self-sustain; the rest are subdominant modes that **decay**
> under iteration (the thousand one-off encounters wash out). Equivalently, the
> sustained self `νΦ_c` is supported on the few relata that lie on self-sustaining
> loops; most do not, so most "run out." The resource-counting lemma below is then the
> **uniform, depleting special case** (§1.3.4) — still true, still the cleanest
> *quantitative* handle, but a corollary of the structure, not the source of the
> rarity. The spectral form is stated as Conjecture 3.4.

The full statement quantifies over all of `Cl(𝕋)`; that lift is the conjecture
(§3.4). But its *engine* is an elementary, fully provable counting fact. Work in the
canonical monoid `(ℝ_{≥0}, +, 0, ≤)` (so `·` is `+`, costs are additive, and
`ε(s) > 1` means a per-return cost `λ(s) := \log ε(s) > 0`).

**Setup.** Let `Φ` be a finite set of candidate couplings (the relations a system
actually has), `|Φ| = N`. Each `f ∈ Φ` has a per-return cost `λ(f) ≥ λ_min > 0` and
requires depth `d(f) ≥ d_min ≥ 2` returns to close into an eigenform. A coupling
**stabilizes within budget `β`** iff the system can fund its required returns:

$$
f \in \mathrm{Stab}_R
\quad\Longleftrightarrow\quad
d(f)\cdot \lambda(f) \ \le\ \beta .
$$

The total attention actually spent across all maintained selves cannot exceed the
budget:

$$
\sum_{f \in \mathrm{Stab}_R} d(f)\,\lambda(f) \ \le\ \beta .
$$

> **Lemma 3.1 (sparsity from a budget).** With the setup above,
> $$
> |\mathrm{Stab}_R| \ \le\ \frac{\beta}{d_{\min}\,\lambda_{\min}} .
> $$
> In particular `|Stab_R|` is bounded by a constant **independent of `N`**, so the
> density `|Stab_R| / N \le \dfrac{\beta}{d_{\min}\lambda_{\min}\,N} \to 0` as
> `N \to \infty`.

**Proof.** Each `f ∈ Stab_R` contributes at least `d_min · λ_min` to the spend
`∑_{f} d(f)λ(f)`, which is `≤ β`. Hence
`|Stab_R| · d_min · λ_min ≤ β`. Divide. ∎

> **Lemma 3.2 (collapse without a bound).** If `β = ⊤` (no finite bound), then the
> constraint `d(f)λ(f) ≤ β` is vacuous, so `Stab_R = Φ` and density `= 1`.

Together: **finite budget ⇒ vanishing density; unbounded budget ⇒ full density.**
The two lemmas are the dichotomy of §3.1, and they are *already* theorems — at the
level of the resource model. They formalize, exactly, "you cannot return to
everything, so which relations get to constitute you is rationed."

> **Mechanized.** Both lemmas are machine-checked in Lean 4, `sorry`-free.
> * Discrete (ℕ-valued) core — depends only on `propext` —
>   [`formal/RelExist/Sparsity.lean`](../../formal/RelExist/Sparsity.lean):
>   `stab_card_bound` / `stab_card_le_div` (Lemma 3.1), `stab_card_le_half` (the
>   `d ≥ 2` regime), and `unbounded_without_budget` (Lemma 3.2).
> * **ℝ-valued + density limit** (mathlib) —
>   [`formal/Scratch/SparsityReal.lean`](../../formal/Scratch/SparsityReal.lean):
>   `stab_card_le_div` (`|Stab| ≤ β/m`, a constant bound) and
>   `stab_density_tendsto_zero` — the genuine `Filter.Tendsto` proof that the
>   stabilized fraction `|Stab N| / N → 0`. This discharges the "density → 0" clause
>   of Lemma 3.1 as a theorem.

---

## 3.3 Why this is the right toy, and its honest gaps

Lemma 3.1 is deliberately the *thin* model: couplings as a finite set with additive
costs. It earns its keep by being unarguable and by isolating the mechanism (a
fixed budget divided among items each costing a positive minimum). But three gaps
separate it from a theorem about `Cl(𝕋)`:

1. **Couplings are not an unstructured set.** In `Cl(𝕋)` they compose, tensor, and
   share sub-relatings; the cost grading `c` is *lax* (sub-additive), so spends can
   overlap and the clean sum `∑ d λ` becomes an inequality over a *poset* of
   couplings. Sparsity must be re-proved with sharing allowed.
2. **"Stabilizes" is a fixed-point condition, not a threshold.** `f ∈ Stab_R` was
   defined in [A3](02-axioms.md) as `loop_R(e) = e`, not as `dλ ≤ β`. The lemma
   assumes these coincide; showing `loop_R`'s budgeted iteration *realizes* the
   threshold (that `N(s) = ⌊β/λ⌋` returns suffice and are necessary to reach the
   fixed point) is real work in the traced category.
3. **"Sparse" deserves a topological/measure form, not just counting.** For infinite
   or continuous state spaces, the right statement is `Stab_R` is **nowhere dense**
   (or measure zero) in the space of states under a natural topology, recovering
   the density statement in the finite case.

None of these is hand-waving-away-able, and naming them is the point: the lemma is
*true and small*; the conjecture is its honest generalization.

---

## 3.4 The conjecture

> **Conjecture 3.3 (sparsity of `Stab` in `Cl(𝕋)`).** Let `Cl(𝕋)` carry a cost
> grading `c` valued in a finite-`β` attention monoid with `ε > 1` and stabilization
> depth `d ≥ 2`. Then `Stab_R` is **sparse**: under the natural topology on states
> `I → D`, `Stab_R` is nowhere dense; and for any finite sub-collection of `N`
> couplings closed under the doctrine operations, `|Stab_R| / N \to 0` as `N \to ∞`,
> with the bound degrading gracefully under cost-sharing (lax `c`).
>
> Moreover (sharp dichotomy): dropping the bound (`β = ⊤`) makes `Stab_R` dense
> (Lemma 3.2 lifts), so finiteness of `β` is **necessary** for sparsity.

> **Partially mechanized (topological clause).** The "nowhere dense" half of
> Conjecture 3.3 is now machine-checked for the **final-coalgebra model** of states —
> [`agda/RelExist/Sparsity.agda`](../../agda/RelExist/Sparsity.agda) (`selves-nowhereDense`):
> under the cylinder topology on behaviours, the selves (the constant behaviours) are
> closed with empty interior, and the sharp dichotomy holds (`trivial→allSelf`: a
> trivial observation alphabet makes them dense). What remains conjectural is the
> *cost-graded* content — the lax grading `c`, cost-sharing over the poset of couplings,
> and the lift to all of `Cl(𝕋)` (step 2 of §3.5); the topological *shape* of the claim
> is no longer open.

> **Conjecture 3.4 (spectral / closure form — the structural reason).** Let attention
> be the co-directed operator `Φ_c` of [§1.3](01-signature.md) on a perspective of
> constitutive capacity `α` (no external budget). Then the set of selves — eigenforms
> of `Φ_c`, i.e. the support of `νΦ_c` — is **sparse**: it is confined to relata on
> self-sustaining loops, and under iterated co-directed feedback all subdominant modes
> decay, so the sustained selves are few relative to all couplings. The resource bound
> of Conjecture 3.3 is the **uniform, depleting special case** ([§1.3.4](01-signature.md));
> this is the general statement, and the one that makes rarity a *consequence of the
> relational dynamics* rather than of an imposed cap.
>
> (Quantitatively this is a spectral-gap statement — few eigenvalues near the spectral
> radius of the coupling — generalizing eigenvector centrality to the recurrent,
> asymmetric, saturating setting; the nonlinearity buys *multiple* attractors, i.e. the
> contingency the view wants, at the cost of Perron-style uniqueness. Hence it is
> harder than Conjecture 3.3 and stated, for now, as a horizon.)

Conjecture 3.3 is the proposition to point a proof assistant at *first* — it is where
the theory either lands in the rich-but-narrow zone (good) or the broad-but-empty zone
(fatal), and the proof attempt is rigor finding the overclaim before a referee does.
Conjecture 3.4 is the structural target it is a special case of.

---

## 3.5 Proof strategy (for mechanization)

A plausible route, in increasing difficulty:

1. **Mechanize Lemma 3.1 / 3.2 as-is.** Pure arithmetic over an ordered monoid;
   trivial in Lean/Agda/Rocq. Establishes the dichotomy at the resource layer and
   pins down the definitions. *(This is the "first discharged result."* **✅ done** —
   [`formal/RelExist/Sparsity.lean`](../../formal/RelExist/Sparsity.lean), Lean 4,
   `sorry`-free.)
2. **Replace the finite set by a graded poset of couplings.** Model sharing: cost
   over a meet-semilattice with `c` sub-additive. Re-derive the bound as
   `|Stab_R| ≤ β / (d_min λ_min)` *up to the sharing defect*, i.e. show the worst
   case (no sharing) is the set bound and sharing only helps.
3. **Connect the threshold to the fixed point.** Prove
   `loop_R(e) = e ⟺ N(e) ≥ d(e)` with `N(e) = ⌊β/λ(e)⌋` ([§1.3.3](01-signature.md)) —
   i.e. budgeted iteration reaches the eigenform iff the budget funds the depth.
   **✅ done** — [`formal/RelExist/Loop.lean`](../../formal/RelExist/Loop.lean):
   `loopR_isEigen_iff_le_fundedReturns` (the `N ≥ d` form), `loopR_isEigen_iff`
   (`d·λ ≤ β`), a non-vacuous witness (`matarN_stabilizesAt`), and the capstone
   `stab_card_le_half_of_depths`, which feeds the **derived** floor `2 ≤ d·λ` into the
   discrete bound — so the sparsity floor hypothesis is now a theorem, not a posit.
   (Done at the dynamical/resource level over `Nat`; the *traced category* proper now also
   exists — the free traced SMC `Cl(𝕋)` of [spec 04 §4.6](04-functorial-semantics.md) — so
   lifting the bound inside it is a well-posed next step rather than missing infrastructure.)
4. **Topologize.** Put the product/cylinder topology on `I → D` (states as
   behaviors in the final coalgebra), show the threshold set is closed with empty
   interior. Coinduction-friendly; Agda's `ν`-layer is the natural host for this step.
   **✅ done** — [`agda/RelExist/Sparsity.agda`](../../agda/RelExist/Sparsity.agda),
   Agda (`--safe --guardedness`): states are behaviours in the final coalgebra, the
   topology is the cylinder topology, and the selves are the *constant* behaviours.
   `nonConst-open` (the selves are **closed** — their positive complement is open) and
   `selves-emptyInterior` (every cylinder contains a non-self) give
   `selves-nowhereDense`: `Stab` is **nowhere dense**, the topological form of
   Conjecture 3.3. `trivial→allSelf` is the matching dichotomy — a trivial observation
   alphabet makes `Stab` dense (Lemma 3.2 lifts), so expressivity (`≥ 2` distinct
   observations) is *necessary* for sparsity.

Steps 1–2 are near-term and proof-assistant-ready. Step 3 is the heart. Step 4 is
the polished form. Steps 1, 3, and 4 are mechanized (Lean for 1 & 3, Agda for 4);
step 2 (cost-sharing over a graded poset) is the remaining gap.

---

## 3.6 What a positive result would and would not mean

- **Would mean.** "A self is an achievement of recursion" is a *theorem* of the
  theory, not a slogan: given finite attention, stable selves are provably rare, and
  the rarity is *caused by* the finiteness. The firewall (no monoidal functor into
  cartesian-only domains) and this sparsity result are the two places the formalism
  earns the word "rigor."
- **Would not mean.** That the world *is* this way (the theory is a lens, not a
  proof — see the view's "What it doesn't settle"); nor would it touch the three
  typed-out residues (valence, the hard problem, freedom), which [T3](theorems.md)
  predicts the formalism *cannot* reach. Proving sparsity confirms the program's
  ambition exactly to its own stated boundary — and no further, which is the point.

---

### Cross-references

- Definitions of `loop_R`, `β`, `ε`, `d`, `c`: [01 §1.3](01-signature.md).
- The selfhood predicate `Stab_R`: [02 — A3](02-axioms.md).
- The doctrine fragments the sparsity lives across: [00](00-doctrine.md).
- Mechanization targets and tooling: [formalization plan §5](../formalization-plan.md).
