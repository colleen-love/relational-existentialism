# WS10 · 02 — Design: statement–gloss reconciliation and the graded groundless core

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
| Atomlessness has an in-house counterexample; no (i) theorem exists | **O2** | Split: Impossibility proved (atomless + plural is unsatisfiable in unlabeled `P_κ`) + Discharged (the graded groundless core, in `νW_Q`) |
| "Canonicity" is uniqueness-of-a-defining-equation, not canonicity among weak laws | **O3** | At-risk of Partial (hard); immediate relabel regardless |
| Incompleteness is bare Cantor; attention/finiteness play no role | **O4** | Discharged (honest reframe + a κ-consuming strengthening via O1) |
| Criterion (vi) rests on a phantom-κ theorem and a triviality | **O5** | Discharged (carrier-linked witness + properness) |
| Dynamics never touch the carrier (`Fintype S` vs `SelfSupport`) | **O6** | Discharged at the O1 tuple (κ₀ = ℵ₀ makes supports finite) |
| WS9 residue: multiplier ≠ attractivity; the (3/8, 1/2) gap; no global uniqueness above μ⋆ | **O7** | Partial (attractivity feasible; the rest characterized open) |
| Prose/claims drift in charter, summaries, README, spec hygiene | **O8** | Discharged (editorial; gated on O1–O6) |

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

### O2 — The atomless object, built where it can exist (criterion (i))

**Finding (review).** The technical summary calls (i) "Discharged — automatic," but the
carrier contains `bottomState` (empty successor set): a relational atom under the only
natural reading of Commitment 1, and one the development *uses* (it refutes
`GeneralBranching`). No atomlessness theorem exists anywhere.

**Finding (this design — the reason the build moves).** The two direct repairs both
collapse, by the same argument, and the collapse is a theorem worth having:

> **Lemma (no plural atomless unlabeled carrier).** In `νP_κ`, let `R x y :=`
> "x and y are hereditarily nonempty" (every reachable state has nonempty successors).
> Then `R` is an Aczel–Mendler bisimulation: take
> `ζ(x,y) := (str x) × (str y)` on the graph — it lands in `R` by closure, it is `< κ`
> (a product of two `< κ` cardinals, `κ` infinite), and `fst '' (A × B) = A` exactly
> because `B` is **nonempty** (likewise `snd`). By `bisim_eq`, any two hereditarily
> nonempty states are **equal**.

Consequences, both to be formalized:

```lean
/-- The grounded core of the unlabeled carrier is exactly {Ω}: atomless + plural
is unsatisfiable in νP_κ. Leaves are the sole source of distinguishability under
unlabeled powerset observation. -/
theorem ws10_unlabeled_atomless_collapses (hinf : ℵ₀ ≤ κ) :
    ∀ x y : (νPk κ).X, HereditarilyNonempty x → HereditarilyNonempty y → x = y

/-- Corollary: the nonempty bounded powerset functor P⁺_κ has a SUBSINGLETON
terminal coalgebra — the "forbid atoms in the functor" route is structural
collapse, the §3.8 failure mode. -/
theorem ws10_nonempty_powerset_trivial : …
```

This is an **Impossibility proved** in the §5 sense, and it is the strongest form of
the review's finding: the atom is not a blemish on `P_κ`, it is **load-bearing for
plurality**. Removing it — by carving (`Grounded`) or by functor surgery (`P⁺_κ`) —
collapses the universe to the single self-relating point `Ω`. (This subsumes and
sharpens `ws7_general_branching_false`: even the hereditarily-branching sub-universe
is trivial.) The finding is Parmenides-shaped — ungraded, groundless relation admits
exactly One — and it strengthens the §4.4 interdependence thesis: a *local* commitment
(atomlessness) also turns out to price against non-collapse, not only the global ones.

**Design decision (the build, per §6.1's shared-`F` machinery).** The charter's own
instruments say what to do when the chosen `F` cannot host a commitment: change `F`
through the ratification pipeline. Distinguishing power must come from somewhere other
than leaves — that is **grading** (§3.5), and WS4 already built the graded universe
`νW_Q` with its full identity theory. In `W_Q`, weights distinguish where leaves did:
two self-loops at distinct weights `q₁ ≠ q₂` are distinct states (immediate from
`dest`-injectivity: equal states have equal destructor weightings), and both are
atomless. So the §7 object this program offers for (i) is the **graded groundless
core**: the hereditarily-supported subcoalgebra of `νW_Q`.

```lean
/-- Nonempty-support reachability and the graded groundless core. -/
def WReaches (u v : (νWQ Q κ).X) : Prop := Relation.ReflTransGen (fun a b => b ∈ wsupp a) u v
def GradedCore (Q κ) : Set (νWQ Q κ).X := { u | ∀ v, WReaches u v → wsupp v ≠ ∅ }

theorem gradedCore_closed  : ∀ u ∈ GradedCore Q κ, wsupp u ⊆ GradedCore Q κ
theorem omegaQ_mem         : ΩQ ∈ GradedCore Q κ          -- self-loop at weight 1
theorem ws10_core_atomless : ∀ u : ↥(GradedCore Q κ), wsupp u.1 ≠ ∅   -- criterion (i)
theorem ws10_core_plural (hQ : ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ …) :
    ∃ a b : ↥(GradedCore Q κ), a ≠ b     -- self-loops at q₁ ≠ q₂; holds at Łₙ, n ≥ 1
theorem wqAlg_closed : (nonempty-support t, members in the core) → wqAlg t ∈ GradedCore
```

**Strategy.** Closure and `ΩQ`-membership are definitional/one-step, as in the
unlabeled sketch. Plurality: build the two self-loops by `Cofix.corec` from
single-state `Q`-weighted coalgebras at `q₁`, `q₂`; distinctness by computing `dest`
of each and comparing weights at the unique point — no bisimulation analysis needed.
`wqAlg` closure is where the graded setting pays: the destructor of `wqAlg t` is the
graded Egli–Milner union, whose support is the union of member supports — **nonempty**
for nonempty-support `t` with core members. The composition wrinkle that killed the
unlabeled version (the empty whole re-entering through `alg ∅`) is handled the same
way — composition on the core is the nonempty-support restriction of the graded monad
— but here the restriction costs nothing, because the core is not a singleton.
Identity theory ((ii)) transfers from `wq_bisim_eq` by restriction; (iii) is the
single-sortedness of `νW_Q`, unchanged.

**Verification duty (not assumed).** The distinct-weight self-loops argument must be
checked against WS4's exact graded-bisimulation definition, and the plurality witness
must be re-derived if `wq_bisim_eq`'s statement differs from the Aczel–Mendler shape.
Whether the KS no-go and the weak-law package survive the nonempty-support restriction
of the graded monad is **routed to WS10-B** (the diagonal uses singletons and
doubletons, all nonempty-support; expected verbatim, to be checked not asserted).

**Outcome class.** Split: Impossibility proved (the collapse lemma + the `P⁺_κ`
corollary) **and** Discharged (the graded core as the (i)-object, with plurality at
`Łₙ`). **Failure mode.** If the graded core also collapses — i.e. if graded
bisimulation ignores weights in a way that revives the product argument — that is a
finding of the first importance (grading insufficient for groundless plurality) and
lands as a second Impossibility, routed to a functor with still more distinguishing
power (labeled/polynomial observation). No branch of this fork is a walk-back of (i);
every branch is a theorem about where the object lives.

**Charter effect.** Criterion (i)'s status becomes: *unsatisfiable jointly with (vii)
in unlabeled `P_κ` (Impossibility proved — a §5/§7 success); discharged on the graded
groundless core, the object the program offers.* This is the §3.9 pattern executed
end-to-end — the literal target is unrealizable *for a proved reason*, the canonical
content is recovered inside the declared surrogate, and the residual (the WS10-B port)
is routed. It also upgrades the program's interdependence result: **grading (§3.5) is
promoted from criterion-(iv) machinery to criterion-(i) necessity** — the collector
tuple already carries `Łₙ`, and this is the theorem that says why it had to.

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
from O2: on the graded groundless core, supports are nonempty by the core's defining
property (on the unlabeled `νP_ℵ₀` carrier the bridge instead carries an explicit
nonempty-support hypothesis — after O2's collapse lemma, hereditary nonemptiness is
not available there as a plural source).

**Target signature.**

```lean
noncomputable instance (u : (νPk ℵ₀).X) : Fintype (SelfSupport ℵ₀ u) :=
  (Cardinal.lt_aleph0_iff_fintype.mp ((νPk ℵ₀).str u).2).some

/-- The bridge: for every grounded state of the ℵ₀-carrier, per-state attention
dynamics (nonexpansive selection, μ ∈ (0,1]) converges to a unique fixed point
ON THAT STATE'S OWN SUPPORT — the first convergence theorem whose state space is
the carrier's. -/
theorem ws10_carrier_attention_converges
    (u : ↥(GradedCore (Luk n) ℵ₀)) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : ↥(wsupp u.1) → ℝ) (hn : ∀ r, 0 ≤ unif r) (hs : ∑ r, unif r = 1)
    (sel : SelectionMap ↥(wsupp u.1) unif)
    (sl : SelectionLipschitz _ unif sel) (hL : sl.L_R μ ≤ 1) :
    ∃! p : FlooredSimplex ↥(wsupp u.1) μ unif, mutT … sel p = p

-- plus the unlabeled variant on (νPk ℵ₀).X with an explicit nonempty-support
-- hypothesis, so the WS5 Attn story is bridged on both carriers.
```

with the WS9 stratification (multistability, two-cycle, pitchfork) restated as
*instantiable on carrier supports of size ≥ 2* wherever the core provides them.

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
inverse-function packaging is disproportionate. **Until O7a lands, the WS9 prose
"attracting above, repelling below" is softened to "multiplier crossing" wherever it
appears (O8).**

**O7b (the (3/8, 1/2) gap).** Attempt the parametrized anchor: replace the fixed
`x = 3/4` with `x(μ)` chosen so `G(x(μ)) ≥ 0` holds up to μ < 1/2 (on paper the
off-center roots persist to exactly 1/2; the algebra is a solvable quadratic in `x` for
each μ, so exact rational anchors may exist on a subdivision). If the subdivision gets
ugly, stop and record the gap as characterized-open with the paper computation cited.

**O7c (global band above μ⋆).** Compute `coordR`'s sup-metric Lipschitz constant on the
floored simplex by the WS8 `linR` method (denominator bounded below by the floor). This
yields a global-uniqueness band `μ > μ⁺` with `μ⁺ > 1/2`; the strip `(1/2, μ⁺]` between
local attractivity and global uniqueness is the honest residual, folded into the
declared open bifurcation surface.

**Outcome class.** Partial by design; every sub-item terminates in a theorem or a
characterized-open stamp. Bundle named `ws10_pitchfork_dynamics`, not
`ws9_bifurcation_resolved`.

### O8 — Prose, charter, and hygiene reconciliation (gated on O1–O7)

All §8.2-style errata, batched as **REV-G**:

1. **Charter §4/§8.1 status lines.** (i): jointly-unsatisfiable-with-(vii) in unlabeled
   `P_κ` (Impossibility proved) + discharged on the graded groundless core (O2), with
   grading recorded as (i)-necessary, not only (iv)-machinery. (iv): canonicity reopened, `unique_realization` erratum recorded (O3). (v):
   reframed + `ws10_bounded_self_model` recorded (O4). (vi): properness added (O5).
   (vii): WS9 + O7 statuses; "attracting/repelling" language conditioned on O7a.
   Collector: concrete tuple ratified at ℵ₀, `hcard` discharged (O1).
2. **Summaries.** "Proved inhabited at one concrete tuple" becomes true — keep it only
   after O1 merges. "Atomlessness is automatic" is replaced by the collapse finding and the graded
   build: the atom is load-bearing for plurality in unlabeled observation, and the
   (i)-object lives in the graded universe. The
   trade-off thesis is scoped: *"you cannot have both"* → *"you cannot have both in a
   set-sized, Mathlib-mechanized carrier; a class-based mechanization (algebraic set
   theory / categories of classes) is a road not taken, not a road proved closed."*
3. **README.** Handled separately (already drafted alongside this design): drop
   "one primitive, one axiom" (it describes the Series 2 axiom ledger, not the Series 3
   artifact), scope the existence trade-off as above, cite Series 3 not Spec 2.0.
4. **Spec hygiene.** Strip the session-transcript preamble from `spec/ws8/00-holes.md`
   (keep the assessment content); fix `ws8/04-design-md` → `04-design.md` and
   `ws7/02-design` → `02-design.md`; normalize ws1's `N-name.md` numbering to the
   `0N-name.md` convention used everywhere else.
5. **Methods disclosure.** The papers' methodology sections state that the blind-review
   layer is same-model review (Claude reviewing Claude) and that `review.md` is an
   external-session audit; independence claims are scoped accordingly. The
   reproducibility footnote pins commit hash + clean-build log per the technical
   summary's own §2 requirement.

## 3. Dependency order

```
O1 (hcard + ℵ₀ tuple)  ──┬──> O4 (bounded self-model)
                         ├──> O5 (standpoint properness)
                         └──> O6 (carrier bridge)   <── O2 (graded core: nonempty supports)
O2 (collapse lemma + graded core) ──> WS10-B (nonempty-support graded-monad port) ──> (iv)-on-core status
O3 (canonicity)  — independent; immediate relabel unconditional
O7 (WS9 residue) — independent of O1–O6
O8 (REV-G)       — last, consumes all statuses
```

Critical path: **O1 → O6** (cheapest, highest status impact) in the first execution
pass, with O2 alongside; O3 and O7a in the second pass; O7b/c opportunistic; O8 closes.

## 4. Success criteria and failure modes (formal)

- **Success.** `lake build` compiles WS10 sorry-free; `#print axioms` on
  `carrier_card_ge`, `ws10_concrete_tuple`, `ws10_unlabeled_atomless_collapses`,
  `ws10_core_atomless`, `ws10_core_plural`, `ws10_bounded_self_model`, `ws10_poles_split`,
  `ws10_standpoint_proper`, `ws10_carrier_attention_converges` reports only
  `[propext, Classical.choice, Quot.sound]`; O3 terminates in a proof, a counterexample
  law, or a Partial with the propagation obstruction typed; REV-G lands with every
  status line matching a theorem name.
- **Failure that would matter.** `carrier_card_ge` failing would falsify the review's
  own claim and reinstate `hcard` as genuinely open — surfaced, not masked. The
  graded core collapsing (the O2 failure fork) would be a first-importance finding —
  grading insufficient for groundless plurality — landing as a second Impossibility
  and routing to a richer observation functor; surfaced, not laundered. There is no route by which a false WS10 claim compiles.

## 5. Charter impact statement

REV-G changes **no** §§0–7 target or criteria text. It changes: §4 and §8.1 status
lines (per O8.1), the §6.1 ratification list (`hcard` discharged; the concrete tuple
ratified at ℵ₀; the canonicity pin reopened with its erratum; the P⁺ port pinned), and
adds §8.2 errata 5–7 (the unlabeled atomless-collapse finding and the graded-core
substitution; canonicity relabel; concrete-tuple
correction). The program's one-line discipline is unchanged and is this workstream's
entire content: **never relabel the shortfall as the goal — and never let the label
outrun the theorem.**
