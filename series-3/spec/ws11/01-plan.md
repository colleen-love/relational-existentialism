# Series 3 Reconciliation Plan — Absorbing the WS10 Review

*A plan to address the findings of `spec/ws10/02-project-review.md` (the second external audit, "R2") and the follow-up evaluation ("R3"), in the charter's own §8.2 discipline: prove the honest theorem, prove the impossibility, or route the residual — never move the §7 bar.*

**Governing constraint (from the sponsor):** stay aligned with the charter. Every item below is phrased as *find the object or prove it cannot exist*. No §0–§7 target or criteria text changes. All status movement happens through a new charter revision (REV-H) plus new workstreams, exactly as REV-G did for the first audit.

**Finding index used throughout:**
R2-1 ledger staleness · R2-2 downward-only identity · R2-3 rigidity / semantic God's-eye / one-step scope · R2-4 trivial-or-strawman discharges ((vi) positive half, poles-split, bare-Cantor incompleteness, sup-lifting preservation) · R2-5 dynamics decoupled from the coalgebra · R2-6 single-object fragmentation (νP_κ vs νW_Q, #Q for infinite quantales) · R2-7 smaller items (solution-lemma overselling, AxiomCheck coverage, duplicated O3 note, ledger-heavy charter).
R3-1 unabsorbed R2 (no REV-H) · R3-2 WS7NonCollapse tag-fields / inert `A` in the "hypothesis-free tuple" · R3-3 dynamics-family conflation ("bands and counterexamples meet at the pitchfork") · R3-4 "fully characterized" self-contradiction in the technical summary · R3-5 `#print axioms` prints but asserts nothing; no CI, no committed build log, no pinned hash · R3-6 doc/process staleness (AxiomCheck header "WS1–WS8", protocols.md blind-phase contradiction) · R3-7 no human expert review of the KS port and the Garner framing · R3-8 §3.6 "exactly the non-surjectivity" causal claim unsupported by the theorem.

---

## Phase 0 — Ledger and hygiene (REV-H, cheap and first)

Everything here is documentation, build machinery, or refactoring — no new mathematics — and it should land before any new workstream so the ledger is current while the real work runs.

**0.1 Charter REV-H (R2-1, R3-1).** Register the R2 audit the way REV-G registered R1: convert each R2 finding into either (a) a typed obligation routed to ws11.1–ws11.5 below, (b) an honest status annotation on an existing criterion line, or (c) a declared scope note. Specifically:

- Criterion (iv) status line gains the annotation: *on any carrier satisfying (ii), identity is downward-determined by terminality; the bidirectional-constitution content currently proved is the existence of a composition algebra with part-reflection, not a co-constitution of identity. The identity-level question is ws11.1's obligation, with both outcomes admissible.*
- Criterion (iii) status line gains: *currently discharged under the successor-state reading; the strong reading (binary relations are themselves elements) is ws11.3's obligation.*
- §3.7 status lines gain the depth-1 scope note (all no-maximal / no-observer / standpoint theorems quantify over one-step supports; hereditary forms are ws11.2's obligation), and the honest external-totality note: the carrier itself exists as a completed set; "no everything" is currently proved only internally.
- §3.6 gains a REV-H erratum on the "finite attention is *exactly* the non-surjectivity" clause (R3-8): the diagonal half is structure-independent (`ws5_carrier_incomplete` consumes no bound; `ws5_self_enumerates_relations` shows the flip under the other encoding); the κ-consuming half is `ws10_bounded_self_model(b)`. The word "exactly" is withdrawn as an erratum, not a criteria change — (v)'s bar is untouched.
- §3.9's "working form of AFA" is annotated: the solution lemma recovers flat/guarded systems only (R2-7).
- Record that the R2 review itself, like R1, is Claude-generated (independence limitation carried forward).

**0.2 Asserting axiom check (R3-5).** Replace every bare `#print axioms foo` in `AxiomCheck.lean` with a `#guard_msgs` (or equivalent) block asserting the output is exactly `[propext, Classical.choice, Quot.sound]` (choice-free where claimed). A wrong axiom list must be a *build failure*, not something a human has to read. Update the header from "(WS1–WS8)" to the full sweep (R3-6).

**0.3 CI and reproducibility (R3-5).** Add a GitHub Actions workflow: `lake exe cache get && lake build`, on every push, with the build log uploaded as an artifact. Pin the commit hash and toolchain in both summaries' verification sections. This converts "confirmed passing on the author's build" into a public, re-runnable fact — the cheapest possible upgrade for a project whose brand is machine-checking.

**0.4 Bundle refactor (R3-2).** Split `WS7NonCollapse` into `WS7Proved` (only proof-bearing fields: `hinf`, `hcard`, `richness_witness`, `no_maximal`, `weak_pb`, `plurality`, `q_small`) and `WS7Status` (the tag fields `richness_general`, `carrier_category`, `dynamics`). Drop or meaningfully instantiate the inert `A : Set ℝ`. Restate `ws10_concrete_tuple` against `WS7Proved` so "hypothesis-free concrete tuple" names a record containing only theorems; the status record travels alongside, explicitly labeled bookkeeping. Rename nothing else — the anti-laundering naming discipline is preserved, just made structurally enforceable.

**0.5 Doc fixes (R3-6, R2-7).** protocols.md blind-phase table vs prose contradiction (phase 2 is either blind or against-charter — pick one and say it once); deduplicate the O3 paragraph in ws10.lean's closing note; clean `spec/ws8/00-holes.md` transcript remnants if still present.

**Exit criterion for Phase 0:** REV-H merged; CI green with asserted axiom check; summaries not yet rewritten (that is Phase 4, after the mathematics moves).

---

## ws11.1 — Bidirectional identity: find it or prove it cannot exist (R2-2)

The centerpiece, and the sponsor's named example. The charter's Commitment 4 says an object is *fixed jointly* by what it contains and what contains it. R2's observation is that terminality makes this impossible *as an identity thesis* on νP_κ. ws11.1 turns that observation into theorems in both directions.

**Obligation A — the impossibility, on the built carrier.** Prove that on any coalgebra satisfying criterion (ii) (bisimulation = identity), identity is fully downward-determined, so upward relations can contribute nothing to individuation:

```
theorem ws11.1_downward_determined {κ} :
    ∀ x y : (νPk κ).X, (νPk κ).str x = (νPk κ).str y → x = y
-- immediate from `lambek`; stated for the record, then generalized:
theorem ws11.1_ii_forces_downward (C : Coalg κ) (h : BisimEqualsEq C) :
    DownwardDetermined C
```

The second form is the real content: it is a theorem *schema*, not a fact about one carrier — **criterion (ii) and bidirectional identity-constitution are jointly unsatisfiable.** This is the same shape as WS10's O2 (atomless + plural), and it should be reported the same way: an interdependence Impossibility, a §5/§7 success, extending §4.4's fracture analysis with a fifth fracture.

**Obligation B — the positive object, where it can live.** Exhibit a concrete finite coalgebra `C` with two states `x ≠ y` that are bisimilar (equal unfoldings up to bisimulation) but distinguished by their containers, and prove the joint determination:

```
theorem ws11.1_bidirectional_witness :
    ∃ (C : Coalg κ) (x y : C.X), x ≠ y ∧ Bisim C x y ∧ UpView C x ≠ UpView C y
theorem ws11.1_joint_determination (C := witness) :
    ∀ x y, ((C.str x = C.str y) ∧ (UpView C x = UpView C y)) → x = y
```

where `UpView C x := {z | x ∈ (C.str z).1}`. This shows bidirectional identity is *coherent* — it exists — at the proved price of criterion (ii). The finding, phrased in charter vocabulary: *(ii) and (iv)-as-identity trade off exactly; the built carrier buys (ii) and therefore realizes (iv) only as composition structure (the weak law), never as co-constitution of identity.* Both outcomes are §7-admissible: the bar is unchanged, the object offered against it is now honestly located.

**Failure conditions (pre-registered per protocol):** Obligation A failing would mean exhibiting a (ii)-satisfying carrier with non-downward-determined identity — believed impossible (Lambek); if the schema resists formalization at full generality, the fallback is the νP_κ instance plus a prose-level generality note, declared as Partial. Obligation B failing would mean no finite witness exists — false on paper (two distinct states over a one-point unfolding with different in-edges suffice), so a failure here indicates a definition error, not a mathematical obstruction.

**Effort:** small-to-medium. A is near-free; B is a finite construction plus a `decide`-friendly proof. One protocol cycle.

---

## ws11.2 — Hereditary scope: no-maximal and no-observer beyond depth 1 (R2-3)

All current §3.7 theorems quantify over immediate successor sets. ws11.2 either proves the hereditary forms or proves them unprovable at the chosen κ — locate or refute, per §8.2.

**Obligation A — reachable-set bound.** Using `Reaches` (already defined in ws10):

```
theorem ws11.2_reachable_card_le {κ} (hreg : κ.IsRegular) (x : (νPk κ).X) :
    Cardinal.mk {y // Reaches x y} ≤ κ
```

Proof sketch: the reachable set is the union over finite depths of iterated `< κ` successor sets; regularity bounds each stage and the ω-union. At κ = ℵ₀ this gives ≤ ℵ₀ (countable), not < ℵ₀ — stated honestly.

**Obligation B — strict carrier gap (the keystone, mirroring O1).** `carrier_card_ge` gives κ ≤ #X; the hereditary no-maximal needs *strict* excess over the reachable bound:

```
theorem ws11.2_carrier_card_gt : Cardinal.aleph0 < Cardinal.mk (νPk Cardinal.aleph0.{0}).X
```

Strategy: inject `2^ℕ` into the carrier (e.g., an injective family of non-bisimilar infinite trees indexed by binary sequences, built by corecursion/solution lemma; strong extensionality separates them). This is the one genuinely new proof of the workstream — the same role `carrier_card_ge` played in WS10. **Pre-registered failure condition:** if the injection resists mechanization, the honest outcome is Partial with the hereditary theorems stated conditionally on `hgt : κ < #X` — a typed hypothesis in the O1 style, *visibly* carried, never silent.

**Obligation C — the hereditary theorems.** Given A + B:

```
theorem ws11.2_no_hereditary_maximal (u) : ¬ ∀ v, Reaches u v
theorem ws11.2_no_hereditary_observer (obs) :
    ¬ ∃ f : {y // Reaches obs y} → (νPk κ₀).X, Function.Surjective f
```

with the standpoint-properness analogue. These are what the §3.7 rhetoric ("cannot totalize", "no view from nowhere") actually asserts; the depth-1 versions become corollaries, and the summaries' scope note (Phase 0.1) is then *deleted* rather than softened.

**Obligation D — external totality, stated honestly.** The carrier-as-completed-set point cannot be theorem-ed away; it can be sharpened: prove no state's hereditary unfolding is isomorphic to the whole carrier (follows from C), and record in REV-H that "no everything" holds *internally* — the external set-hood of νP_κ is a cost of §3.9, now explicitly priced in the §4.4 fracture analysis rather than left implicit. Rigidity (`endo_eq_id`) is likewise registered as a *finding* — the terminal carrier has absolute individuation — with the positioned-identity reading routed to the graded carrier (ws11.4).

**Effort:** medium; B is the risk. One cycle, possibly two if B splits off.

---

## ws11.3 — Reified relations: upgrade criterion (iii) from the deflated reading (R2-4, R2-7-adjacent)

R2 is right that in a powerset coalgebra edges have no identity, so "relations are objects" currently means only "successors are states." But the carrier has the resources to do better, and no functor change is needed: **Lambek's bijectivity means every `< κ` subset of the carrier is the unfolding of exactly one state.** So Kuratowski pairing is *constructible inside νP_κ*:

```
noncomputable def mkState (s : PkObj κ (νPk κ).X) : (νPk κ).X := (lambek …).invFun s
noncomputable def pair (x y) : (νPk κ).X := mkState {mkState {x}, mkState {x,y}}
theorem ws11.3_pair_inj : Function.Injective2 (pair (κ := κ))
noncomputable def reify (R : Set ((νPk κ).X × (νPk κ).X)) (h : #R < κ) : (νPk κ).X
theorem ws11.3_reify_faithful : ∀ R S h₁ h₂, reify R h₁ = reify S h₂ ↔ R = S
theorem ws11.3_reify_element : -- the reified relation is itself a state whose
                             -- members (the pairs) are states: iterable reification
```

`pair_inj` follows from strong extensionality (`bisim_eq`) exactly as in ZF; `reify` sends a `< κ` binary relation to the state whose successors are its pairs. This discharges the *strong* reading of criterion (iii): binary relations between objects are themselves objects, free to enter further relations (Commitment 2's "reification is total and iterated" — prove one iteration lemma: relations *between reified relations* exist too). **Pre-registered failure condition:** if Kuratowski injectivity fails on the carrier (it should not — the carrier is strongly extensional), that itself would be a striking impossibility to report; a genuine risk is only mechanization cost around `noncomputable` inverse plumbing.

This is the plan's best effort-to-payoff ratio: it converts an R2 "deflation" criticism into a genuine strengthening of a criterion, with no carrier change and no charter change.

**Effort:** small-to-medium. One cycle.

---

## ws11.4 — The graded groundless core and the weak-law package on νW_Q (R2-6, WS10-B, O3)

The largest workstream: everything the fragmentation criticism names. The positive criterion-(i) object was deported to νW_Q by O2; nothing else has followed it there. ws11.4 makes νW_Q a real second home rather than a forwarding address.

**Obligation A — the graded core (positive (i)).** Define the hereditarily-supported subcoalgebra of νW_Q (every reachable state has nonempty weighted support) and prove it is atomless *and* plural:

```
theorem ws11.4_graded_core_atomless : ∀ x ∈ GradedCore, (support (str x)).Nonempty
theorem ws11.4_graded_core_plural  : ∃ x y ∈ GradedCore, x ≠ y
```

Plurality witness per the O2 diagnosis: two self-loops at distinct weights (q₁ ≠ q₂ in Łₙ, n ≥ 2) — distinguishable by *how much* they relate, with no leaf anywhere. This is the theorem the whole REV-G reclassification promised; until it exists, "the positive (i)-object lives in the graded carrier" is a routing slip, not a result.

**Obligation B — transport the structural package.** Re-establish on νW_Q (or its core) what the criticism notes was never moved: the KS no-go for the graded functor (or prove the graded strict law *does* exist — either outcome is reportable), the graded Egli–Milner weak law restricted to the core (check closure of the core under `wqAlg`), and graded standpoints (the (vi) pair, weighted). **Pre-registered failure conditions:** the core may fail closure under composition (report the precise obstruction; Partial); the graded KS port may need the step-16 reduction first — if so, step-16 is pulled into scope here rather than left "WS4-local."

**Obligation C — canonicity among weak distributive laws (O3, R2-4).** Define the class honestly and settle inhabitation + uniqueness:

```
structure WeakDistLaw (κ) where
  law        : ∀ X, PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)  -- as pointed nat. transf.
  natural    : …
  unit_laws  : …
  weak_mult  : …   -- the corrected Egli–Milner multiplication square
theorem ws11.4_weak_law_unique : ∀ L L' : WeakDistLaw κ, L = L'   -- or a counterexample
```

Garner's Vietoris result signals truth; the mechanization is the deliverable. **Both outcomes admissible:** uniqueness discharges (iv)'s reopened canonicity; a second inhabitant would be a finding (the weak law is a *choice*, to be declared). Under no circumstances is `ws3_weak_law_canonical` re-cited for this — that theorem stays labeled a unique-realization statement.

**Obligation D — infinite quantale ratification (R2-6).** Exhibit one countably infinite quantale (e.g., the dyadic rationals in [0,1] under ⊗) with `#Q ≤ κ₀` proved, so grading is ratified beyond the finite Łₙ; state the `#Q = 𝔠` case as the typed obligation it is (requires κ > 𝔠 or truncation — a genuine band constraint, recorded, not solved).

**Effort:** large; the long pole. Two to three protocol cycles (A+B, then C, then D). ws11.1–ws11.3 do not depend on it and should not wait for it.

---

## ws11.5 — Constitutive attention: couple the dynamics to the carrier (R2-5, R3-3)

R2's charge is that attention is weight-drift over a static support — "feed the attended, starve the unattended" never *constitutes* anything. ws11.5 builds the missing bridge using machinery that already exists, then repairs the dynamics-family conflation.

**Obligation A — the self-model map.** Lambek's inverse again: an attention vector on a state's support, μ-floored, selects a nonempty `< κ` sub-support — which *is* a state:

```
noncomputable def selfModel (u : (νPk κ₀).X) (w : FlooredSimplex (SelfSupport κ₀ u) μ unif)
    (θ : ℝ) : (νPk κ₀).X   -- mkState of the θ-attended sub-support
theorem ws11.5_self_model_proper : selfModel u w θ ≠ u ∨ … -- the self-model misses states
                                                          -- (via ws10_standpoint_proper)
theorem ws11.5_omega_fixed : selfModel Ω w θ = Ω            -- Ω is a self-model fixed point
```

This makes "the self-model is a proper, positioned part of the object" (Commitment 5) a theorem about *states*, not a gloss on weight vectors — attention output re-enters the ontology. Iterating `selfModel` gives dynamics on the carrier itself; even one non-trivial theorem about the iterate (e.g., reachable-set monotonicity, or existence of non-Ω fixed points at suitable θ) would be the first genuinely constitutive dynamics result. **Pre-registered failure conditions:** the θ-threshold selection may not interact well with the simplex flow (report the mismatch precisely); fixed-point structure of the iterate may be intractable at this Mathlib pin (declare Partial with the typed statement).

**Obligation B — the sliver and the family honesty (R3-3).** For the coordination family: close `μ ∈ (3/8, 1/2)` in at least one direction (multistability persists up to the pitchfork, or uniqueness begins earlier), or prove the boundary has no closed form in a stated sense and register it. For the *linear* family, add the necessity side (a multistability or non-uniqueness witness below its band), so that "sufficient band + necessary counterexample" holds *within* at least one family rather than across two. Until then, all prose must attribute bands and counterexamples per-family (Phase 4).

**Obligation C — selection-dominated regime.** The philosophically loaded regime (small μ, selection dominates, collapse threatens) currently has only counterexamples. Add one positive theorem there if available — e.g., non-collapse of the ω-limit set away from vertices under the μ-floor (`ws5_no_delta` extended to the orbit, not just fixed points) — or register the impossibility shape. Modest scope; the point is that the interesting regime gets at least one theorem, not that it gets solved.

**Effort:** medium (A) + medium (B) + small (C). One to two cycles.

---

## Phase 4 — Summaries, positioning, and the human loop

Run after ws11.1–ws11.3 land (ws11.4/ws11.5 can trail): rewrite both summaries against the post-REV-H ledger. Specific corrections owed regardless of new results: delete "attention dynamics fully characterized" in favor of "characterized for the exhibited families, with the per-family gaps stated" (R3-4); rewrite the plain summary's tipping-point sentence to name the family (R3-3); rewrite "the one concrete just-right setting … exhibited outright" against the refactored `WS7Proved` (R3-2); add the depth-1 scope sentence if ws11.2-B fails, delete it if ws11.2 lands; present the fracture count honestly (the ws11.1 trade-off would be the fifth). The plain summary should also carry one sentence a lay reader currently never gets: *most of the informative results are theorems about what this framework cannot do, and the positive constitution increasingly lives in the graded carrier, where much is still unbuilt.*

Finally (R3-7): recruit at least one human reviewer with coalgebra/category-theory expertise, scoped to two questions the model-only loop cannot settle — is the Klin–Salamanca port faithful to the published no-go, and is the ws11.4-C `WeakDistLaw` definition the class Garner's result actually speaks to? Disclose the review chain's provenance in the README alongside the existing Claude-reviewing-Claude note.

---

## Sequencing and dependency summary

```
Phase 0 (REV-H, CI, asserting AxiomCheck, bundle refactor)   ── first, ~days
   ├── ws11.1 bidirectional identity  (independent, small)      ┐
   ├── ws11.2 hereditary scope        (independent; B is risk)  ├─ parallelizable
   ├── ws11.3 reified relations       (independent, small)      ┘
   ├── ws11.4 graded core + canonicity (large; the long pole)
   └── ws11.5 constitutive attention  (A independent; B/C after WS9 familiarity)
Phase 4 (summaries rewrite, REV-I, human review)              ── after ws11.1–13
```

Every workstream runs the existing seven-phase protocol, with Phase-1 conceptualize output pre-registering the failure conditions written above, so no result can be reframed after the fact — the same guard that made REV-G possible. The plan adds no new criteria, removes none, and touches no §0–§7 text: it either builds the objects the charter always asked for (ws11.3, ws11.4-A, ws11.5-A), proves sharply that they cannot exist where they were first sought (ws11.1-A, possibly ws11.2), or makes the ledger and machinery say exactly what the Lean proves (Phase 0, Phase 4).
