# WS10 · 02 — Design: statement–gloss reconciliation and the grounded core

*Design register. This workstream converts the external review (`series-3/spec/review.md`)
into typed obligations, in the charter's §5 outcome vocabulary and under the §8.2
discipline: substitute openly, recover the canonical content inside the surrogate where
possible, state the residual obstruction precisely, and route it to the owner. Nothing
here changes the §7 criteria; several §4/§8.1 status lines change once obligations land
(REV-G, scoped in §5 below).*

## 0. Provenance and scope

The review found one recurring failure mode: **formal statements weaker than the labels
and glosses placed on them.** Seven findings, of which WS9 has since addressed one
(convergence sharpness) and the remainder are open. WS10's job is to close what is
cheaply closable, honestly reclassify what is not, and carve the one new mathematical
object the review showed the program actually needs (the atomless subcarrier). The bar
does not move; the statements move up to the bar or the labels move down to the
statements.

> **As built (`series-3/formal/ws10.lean`, sorry-free, axiom-clean).** The keystone
> **O1** is discharged: `carrier_card_ge : κ ≤ #(νPk κ).X` (unconditional in κ), with
> hypothesis-free corollaries (`ws10_no_maximal`, `ws10_no_global_observer`) and the
> concrete tuple at `κ₀ = ℵ₀` (`ws10_concrete_tuple`). Its fallout is discharged:
> **O4** (`ws10_bounded_self_model` — diagonal ∧ κ-consuming carrier-non-surjectivity),
> **O5** (`ws10_standpoint_proper` — every view misses a state), and **O6**
> (`ws10_carrier_attention_converges` — at ℵ₀, supports are finite by the carrier's own
> bound, so attention converges on a genuine carrier support). **O2** (atom / grounded
> core) is out of scope for this pass. **O3** (canonicity among weak distributive laws)
> and **O7** (WS9 attractivity / the exact bifurcation boundary) are recorded as the
> remaining program in `ws10.lean`'s trailer — not laundered into theorems.

**Review findings → obligations map:**

| Review finding | Obligation | Class expected |
|---|---|---|
| `hcard` unproved; no concrete tuple exhibited | **O1** | Discharged (cheap) |
| Atomlessness has an in-house counterexample; no (i) theorem exists | **O2** | Split: Impossibility proved (full carrier) + Discharged (grounded core) |
| "Canonicity" is uniqueness-of-a-defining-equation, not canonicity among weak laws | **O3** | At-risk of Partial (hard); immediate relabel regardless |
| Incompleteness is bare Cantor; attention/finiteness play no role | **O4** | Discharged (honest reframe + a κ-consuming strengthening via O1) |
| Criterion (vi) rests on a phantom-κ theorem and a triviality | **O5** | Discharged (carrier-linked witness + properness) |
| Dynamics never touch the carrier (`Fintype S` vs `SelfSupport`) | **O6** | Discharged at the O1 tuple (κ₀ = ℵ₀ makes supports finite) |
| WS9 residue: multiplier ≠ attractivity; the (3/8, 1/2) gap; no global uniqueness above μ⋆ | **O7** | Partial (attractivity feasible; the rest characterized open) |

## 1. What WS9 already closed, and its precise residue

WS9 discharged the review's Overreach 6(b) fully and 6(c) in the honest direction: the
band is now **necessary** (`ws9_no_unique_attention`, `ws9_no_contraction` — exact
rational multistability at μ = 3/8), non-settling is **witnessed** (`ws9_two_cycle`),
existence is **floored** (`ws9_center_fixed_all`), multistability holds on an
**interval** (`ws9_multistable_interval`, μ ∈ (0, 3/8]), and a **genuine derivative**
locates the pitchfork multiplier crossing at μ⋆ = 1/2. The summaries' previously
unsupported claim "convergence really can fail below the threshold" is now a theorem
(for uniqueness and for settling). This is §8.2 discipline done well.

Three residues, recorded so WS9's glosses do not outrun WS9's statements:

- **R1.** `ws9_bifurcation` is a statement about the *multiplier* `2(1−μ)` crossing 1.
  The prose gloss "attracting above, repelling below" is a dynamical claim about orbits
  that **no theorem currently states**. → O7a.
- **R2.** Multistability is proved on (0, 3/8]; the multiplier says the center is
  non-hyperbolically stable only above 1/2. The interval **μ ∈ (3/8, 1/2) is
  uncharacterized** in both directions. → O7b (characterized open unless the anchor
  parametrizes cheaply).
- **R3.** Above μ⋆ nothing gives coordSel **global** uniqueness (the multiplier is
  local). A Lipschitz band for `coordR` on the floored simplex would give a global band
  meeting the pitchfork only approximately; the exact meeting is the already-declared
  open bifurcation residue. → O7c.

## 2. Obligations

### O1 — Discharge `hcard` and exhibit the concrete tuple

**Finding.** Every "Discharged" that touches cardinality — `ws6_no_maximal`,
`ws6_no_global_observer`, `ws7_static_band`, `ws7_retro_validate`,
`ws7_band_and_retro` — carries `hcard : κ ≤ #(νPk κ).X` as an unproved hypothesis, and
no concrete `κ₀` is ever instantiated. The charter's "Discharged at one concrete tuple
`(κ₀, μ, Łₙ)`" and the technical summary's "proved inhabited at one concrete tuple" are
**false as stated**: what exists is a universally quantified schema.

**Target signatures.**

```lean
/-- If #X < κ then every subset of X is < κ-sized, so PkObj κ X ≃ Set X;
Lambek then gives X ≃ Set X, contradicting Cantor. -/
theorem carrier_card_ge (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X

/-- The concrete tuple, hypothesis-free: κ₀ = ℵ₀ (regular), any μ > 0, Łₙ (n ≥ 2). -/
theorem ws10_concrete_tuple (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WS7NonCollapse ℵ₀ μ A)   -- and the retro-validation conjunction at ℵ₀
```

**Strategy.** For `carrier_card_ge`: by_contra `h : #X < κ`. Then for every
`s : Set X`, `mk s ≤ mk X < κ`, so the subtype coercion `PkObj κ X → Set X` is a
bijection and `mk (PkObj κ X) = 2 ^ mk X`. `destEquiv` (Lambek) gives
`mk X = mk (PkObj κ X)`, so `mk X = 2 ^ mk X`, contradicting `Cardinal.cantor`.
Regularity of ℵ₀ is `Cardinal.isRegular_aleph0`. Then thread: keep the general
`hcard`-hypothesis forms for compatibility, add hypothesis-free corollaries
(`ws6_no_maximal'`, `ws6_no_global_observer'`, …) consuming `carrier_card_ge`, and
restate the collector at ℵ₀.

**Outcome class.** Discharged. **Failure mode.** None foreseeable; the argument is
four moves of existing WS1/WS2 API. If the subtype/Set transport fights Lean, the
fallback is an explicit injection `Set X → PkObj κ X` plus `Cardinal.mk_le_of_injective`
and the same Cantor endgame.

**Downstream effect.** The "witnessed Goldilocks point" claim becomes true; O4's
strengthening and O6's bridge become available; §8.1 status lines for WS6/WS7 lose their
silent conditionality.

### O2 — The atom, named; the grounded core, built (criterion (i))

**Finding.** The technical summary calls (i) "Discharged — automatic," but the carrier
contains `bottomState` (empty successor set): an object that decomposes into no
relations, i.e. a relational atom under the only natural reading of Commitment 1 — and
the development *uses* this state (it refutes `GeneralBranching`). No atomlessness
theorem exists anywhere. Lambek's iso does not preclude empty unfoldings.

**Design decision (the §8.2 move).** Do not defend "the full carrier is atomless"; it
is false on the honest definition. Split:

1. **Impossibility proved (full carrier).** Define the atom and prove it inhabited:

```lean
def IsRelationalAtom (u : (νPk κ).X) : Prop := ((νPk κ).str u).1 = ∅

theorem ws10_carrier_has_atom (hinf : ℵ₀ ≤ κ) :
    ∃ u : (νPk κ).X, IsRelationalAtom u    -- witness: bottomState
```

This is a *finding*, stated in the charter's own currency: the terminal carrier of a
powerset-type functor is the space of **all** bounded behaviours, grounded and
groundless alike. Totality of behaviours and atomlessness are incompatible — a small
sibling of the §4.4 fracture pattern (another global claim paying for existence).

2. **Discharged (the grounded core).** Carve the honest (i)-object: the largest
subcoalgebra of hereditarily nonempty states.

```lean
/-- Reachability along the successor relation. -/
def Reaches (u v : (νPk κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ ((νPk κ).str a).1) u v

/-- The grounded core: states all of whose reachable states have successors. -/
def Grounded (κ) : Set (νPk κ).X :=
  { u | ∀ v, Reaches u v → ((νPk κ).str v).1 ≠ ∅ }

theorem grounded_closed : ∀ u ∈ Grounded κ, ((νPk κ).str u).1 ⊆ Grounded κ
def groundedCoalg (κ) : Coalg κ                    -- carrier ↥(Grounded κ)
theorem omega_grounded (hinf) : Ω κ ∈ Grounded κ
theorem ws10_grounded_atomless :
    ∀ u : ↥(Grounded κ), ¬ IsRelationalAtom u.1    -- criterion (i), as a theorem
theorem grounded_nondegenerate (hinf) : ∃ a b : ↥(Grounded κ), a ≠ b
    -- e.g. Ω and the two-cycle solution Ω' = {Ω''}, Ω'' = {Ω'} via ws1_C2
```

**Strategy.** `grounded_closed` is definitional (a reachable-from-successor state is
reachable). `omega_grounded`: everything reachable from Ω is Ω (its successor set is
`{Ω}`), and `str Ω = {Ω} ≠ ∅`. `ws10_grounded_atomless`: `Reaches u u` by `refl`, apply
the defining property. Non-degeneracy needs a second grounded state; the solution lemma
(`ws1_C2`) supplies guarded systems whose solutions are hereditarily nonempty by
construction. Identity theory transfers: states of the core are carrier states, so
bisimilarity-as-identity is inherited (a one-line restriction lemma, not a new proof).

**The composition wrinkle (routed, not hidden).** `alg` is *not* closed on the core:
`alg ∅` has empty destructor — the empty whole is exactly the atom re-entering through
composition. The honest fix is philosophically apt: on the core, composition is the
**nonempty** bounded-powerset monad `P⁺_κ` (no object is composed of nothing). Two
sub-obligations: (a) `alg` restricted to nonempty inputs lands in the core
(`dest (alg t) = ⋃ dest x` is nonempty when `t` is and members are grounded) —
straightforward; (b) whether the Klin–Salamanca no-go and the weak-law package survive
the passage `P_κ → P⁺_κ` — **routed to a WS10-B check** (KS's diagonal uses two-element
sets and singletons only, so the port is expected verbatim; expected Discharged, but it
must be checked, not asserted).

**Outcome class.** Split as above. **Failure mode.** If `Grounded` fails closure or Ω
membership, the definition is wrong, caught at build. The genuine risk is (b); if the
P⁺ port fails, criterion (iv) on the core reclassifies to Partial with the obstruction
named.

**Charter effect.** Criterion (i)'s §7 status line becomes: *refuted for the full
carrier (with witness); discharged for the grounded core, the named (i)-object.* The
program's "single object (or small family)" clause in §7 already licenses offering the
core: this is a declared substitution in the §3.9 pattern, not a moved goalpost.

### O3 — Canonicity, the real statement

**Finding.** `ws3_weak_law_canonical` proves: the map satisfying
`str (f t) = pkJoin (map str t)` is unique. Since `str` is a bijection, that equation
*defines* f; uniqueness is `destEquiv.injective`. This is not the §6.1 [REV-B] pin
("the canonical or uniquely-forced weak law for bounded `P_κ`"), which quantifies over
**weak distributive laws** — natural transformations with the weak-law axioms — not
over maps satisfying one concrete formula. Criterion (iv)'s move to Discharged leaned
on this.

**Immediate action (unconditional, this revision).** Rename the theorem to what it is —
`ws3_weak_law_unique_realization` — keep it (it is true and mildly useful), and correct
the (iv) status line: coherence and weak-pullback preservation stand Discharged;
**canonicity reopens** as the obligation below. This is a §8.2 erratum, surfaced.

**Target signature.**

```lean
/-- A weak distributive law of P_κ over P_κ: natural, T-unit law, and the
Egli–Milner-corrected multiplication square; the F-unit law is dropped
(Garner-style weakening — dropping it is what "weak" means). -/
structure WeakDistLaw (κ) (hreg : κ.IsRegular) where
  lam        : ∀ {X : Type u}, PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)
  natural    : ∀ {X Y} (f : X → Y) 𝒮, lam (PkMap κ (PkMap κ f) 𝒮) = PkMap κ (PkMap κ f) (lam 𝒮)
  unit_T     : ∀ {X} (t : PkObj κ X), lam (pkPure hreg.aleph0_le t) = PkMap κ (pkPure hreg.aleph0_le) t
  mult_law   : (the Egli–Milner multiplication square, stated against pkJoin)

def egliMilnerLaw (hreg) : WeakDistLaw κ hreg      -- inhabitation (from WS3's alg data)

-- The fork, both branches typed:
theorem ws10_weak_law_canonical (hreg) : ∀ L : WeakDistLaw κ hreg, L.lam = (egliMilnerLaw hreg).lam
theorem ws10_weak_law_not_canonical (hreg) : ∃ L : WeakDistLaw κ hreg, L.lam ≠ (egliMilnerLaw hreg).lam
```

**Strategy.** Inhabitation first (mechanical, from WS3). For uniqueness, run the KS
element-chasing method *positively*: naturality pins `lam` on the generators
(singletons, doubletons) via the same `fst/snd/xor` fibre analysis that powered the
no-go; the question is whether unit_T + naturality + the multiplication square propagate
the pinning to all of `P_κ P_κ`. Garner's Vietoris result (weak laws of powerset-type
monads correspond to their canonical Egli–Milner data) is the literature signal that
canonicity is *true*; the mechanization cost is the unknown.

**Outcome class.** At-risk of Partial: expected trajectory is inhabitation Discharged,
uniqueness Partial with the pinned-generators fragment proved and the propagation step
as the named obstruction. Either terminal branch (canonical, or a second law exhibited)
is a §5 success. **Failure mode.** The multiplication square's correct weak form is
itself a design risk (the [REV-B] pentagon erratum shows this family of statements is
easy to mis-transcribe); the design review must check it against Garner's axioms before
execution.

### O4 — Incompleteness with content

**Finding.** `ws5_carrier_incomplete` is Cantor's theorem: no surjection from any set
onto its own powerset. The `< κ` bound, the coalgebra, and attention appear nowhere in
the proof; the advertised "(F, κ)-robustness" is structure-independence. The charter's
"finite attention is exactly the non-surjectivity that lets a self-referential system
remain consistent" is not what is proved.

**Design decision.** Two moves, both cheap once O1 lands:

1. **Reframe (editorial, unconditional).** The summaries stop presenting the diagonal
as a discovery *about* the framework and present it as what it is: a modeling
identification (self-description space = predicates over the support) under which the
classical diagonal applies. The identification is defended in the interpretation
section of the (v)-paper, where it belongs; `ws5_self_enumerates_relations` (the result
flips under the other natural identification) is cited *for* this honesty, as the file
already intends.

2. **Strengthen (the κ-consuming half).** Add the conjunct that genuinely uses the
bound, unavailable before O1:

```lean
/-- Bounded self-modelling: every observer's window both (a) fails to enumerate
its own predicates (diagonal) and (b) fails to reach the carrier (cardinality —
consumes carrier_card_ge, hence genuinely consumes κ). -/
theorem ws10_bounded_self_model (u : (νPk κ).X) :
    (¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e)
  ∧ (¬ ∃ f : SelfSupport κ u → (νPk κ).X, Function.Surjective f)
```

Conjunct (b) is `ws6_no_global_observer` with O1's `carrier_card_ge` discharged into
it — repositioned as the incompleteness result the finiteness rhetoric was pointing at:
the object strictly exceeds every observer's window, *because* windows are `< κ` and
the carrier is `≥ κ`. Now "the bound is load-bearing" is a property of the stated
theorem, not of the gloss.

**Outcome class.** Discharged. **Failure mode.** None beyond O1's.

### O5 — Criterion (vi): tie the theorems to the carrier

**Finding.** `FaithfulCarrierEmbedding` carries κ as a phantom parameter — the carrier
appears in no field — so `ws6_poles_split` is a two-line fact about any category with a
parallel pair, glossed as a carrier result. `ws6_substantive_standpoints` (distinct
successor sets give distinct membership predicates) is definitionally true.

**Target signatures.**

```lean
/-- The carrier's own parallel pair in Set: two distinct points of νP_κ, as maps
from the point. Sourced from ws2_nondegenerate — the phantom becomes real. -/
def carrierParallelPair (hinf : ℵ₀ ≤ κ) :
    Σ' (f g : PUnit → (νPk κ).X), f ≠ g

/-- FaithfulCarrierEmbedding, re-founded: the witness field is *required* to be the
image of two distinct carrier states under a functor from a carrier-containing
category (Set restricted to {PUnit, (νPk κ).X}). -/
structure FaithfulCarrierEmbedding' (κ) (C) [Category C] where …

theorem ws10_poles_split (hinf) … : (∀ x, IsZero (E.F.obj x)) → False
    -- same mechanism, now consuming the carrier's two states

/-- Properness: every standpoint is genuinely partial — its view holds on < κ
states while the carrier has ≥ κ (consumes carrier_card_ge). -/
theorem ws10_standpoint_proper (hcard-free after O1) (sp : Standpoint κ) :
    ∃ y, ¬ sp.view y
```

**Strategy.** The parallel pair is `ws2_nondegenerate` packaged as two functions from
`PUnit`; the split theorem's proof is unchanged (terminality of a zero target), but its
hypothesis now cannot be instantiated without the carrier, which is what the gloss
claimed all along. Keep the old general lemma, renamed to what it is
(`zero_image_collapses_parallel_pairs`). `ws10_standpoint_proper` upgrades the
"substantive standpoints" package: distinct (E1), non-global (E2), and now **proper**
(each view misses something) — the third leg is what makes "positioned *partial* views"
a theorem rather than a noun phrase.

**Outcome class.** Discharged. **Failure mode.** Category-theory plumbing on the
two-object full subcategory of Set; if Mathlib's `FullSubcategory` fights, fall back to
the walking-parallel-pair category with the functor defined by the two carrier states.

### O6 — The dynamics–carrier bridge

**Finding.** All convergence theorems (WS7/WS8/WS9) live on `FlooredSimplex S μ unif`
for abstract `Fintype S`; `Attn κ u` lives on `SelfSupport κ u`, which can be infinite.
No theorem connects them; "attention on the carrier converges" is comment-level.

**Design decision.** Do not generalize the dynamics to infinite support (a genuine
research project in ℓ¹ dynamics); **specialize the carrier** to the O1 tuple. At
`κ₀ = ℵ₀`, every support is finite *by the carrier's own bound*: `mk (SelfSupport ℵ₀ u)
< ℵ₀` gives `Finite`, hence a (noncomputable) `Fintype` instance — the hypothesis the
simplex needs becomes a theorem the carrier supplies. Nonemptiness of the support comes
from O2: on the grounded core, successor sets are nonempty.

**Target signature.**

```lean
noncomputable instance (u : (νPk ℵ₀).X) : Fintype (SelfSupport ℵ₀ u) :=
  (Cardinal.lt_aleph0_iff_fintype.mp ((νPk ℵ₀).str u).2).some

/-- The bridge: for every grounded state of the ℵ₀-carrier, per-state attention
dynamics (nonexpansive selection, μ ∈ (0,1]) converges to a unique fixed point
ON THAT STATE'S OWN SUPPORT — the first convergence theorem whose state space is
the carrier's. -/
theorem ws10_carrier_attention_converges
    (u : ↥(Grounded ℵ₀)) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : SelfSupport ℵ₀ u.1 → ℝ) (hn : ∀ r, 0 ≤ unif r) (hs : ∑ r, unif r = 1)
    (sel : SelectionMap (SelfSupport ℵ₀ u.1) unif)
    (sl : SelectionLipschitz _ unif sel) (hL : sl.L_R μ ≤ 1) :
    ∃! p : FlooredSimplex (SelfSupport ℵ₀ u.1) μ unif, mutT … sel p = p
```

with the WS9 stratification (multistability, two-cycle, pitchfork) restated as
*instantiable on carrier supports of size ≥ 2* wherever the grounded core provides
them.

**Outcome class.** Discharged. **Failure mode.** `Fintype` instance plumbing
(decidability noise around the noncomputable instance); mitigated by `Classical` local
instances as WS5/WS6 already do. **Note for §8.1.** This bridge is the payoff that
justifies ℵ₀ as the ratified tuple: at ℵ₀, "finite attention" stops being a slogan —
supports are finite because the carrier bound says so.

### O7 — WS9 residue

**O7a (attractivity, feasible).** Prove the dynamical content of the pitchfork's upper
side: for μ > 1/2, the center is locally attracting — `|coordIndF μ x − 1/2| ≤
q·|x − 1/2|` for some `q < 1` on a closed interval around 1/2, via the derivative bound
(`Convex.lipschitzOnWith_of_norm_deriv_le`-style MVT on the explicit derivative of the
induced 1-D map, which O7 must compute away from the center — routine calculus, the
denominator is bounded below on the interval). Local instability below 1/2 (the
repelling half) needs a reverse MVT estimate; attempt it, classify Partial if the
inverse-function packaging is disproportio