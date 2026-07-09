# Relational Existentialism

> **Charter status — Revision A (post-WS1 reconciliation).** This revision does
> not change the program's philosophical target or its success criteria. It
> records one thing the original charter did not, and that WS1's formalization
> forced into the open: **the object the program actually builds is the terminal
> coalgebra of a *bounded* observation functor `P_κ`, not the class-sized final
> coalgebra of the full powerset functor named in §3.1** — and the parameter that
> substitution introduces (the bound `κ`, and more generally the choice of
> observation functor `F`) is a *shared* dependency that couples workstreams the
> original charter presented as parallel. Every change is confined to: a new §3.9
> (the bounded-carrier reconciliation), a new §6.1 (revised dependency structure),
> an expanded §8 (per-workstream hazard audit), and inline **[REV-A]** pointers.
> The original §§0–9 are otherwise retained verbatim. Nothing here is a *reframe*
> of the target: §3.6 already made bounding the program's own thesis, and Revision
> A only makes explicit that §3.1's full-powerset gloss and §3.6's boundedness
> requirement cannot both hold literally, and that the charter sides with §3.6.

> **Charter status — Revision B (post-WS3 report).** Like Revision A, this
> revision changes neither the philosophical target nor the §7 success criteria.
> It records what WS3's formalization reported, using the charter's own §5
> outcome vocabulary and §6.1 ratification machinery. WS3 reported **Partial**: a
> proved **Impossibility** at the gate (no strict distributive law of the §3.4
> form exists on the `P_κ` carrier — a §5/§7 success), and the bidirectional
> constitution content of criterion (iv) delivered through a *weak* distributive
> law whose canonicity for bounded `P_κ` is **open and routed to WS4**. Per §5, a
> Partial triggers methodology notes and hand-offs, not a reframe. Every change is
> confined to: the §8.1 WS3 status line (updated from "at-risk" to the reported
> class), the §6.1 ratification list (the WS4 canonical-weak-law obligation, newly
> pinned), a signature erratum on the WS3 design's `pentagon` field, and an
> operational axiom-check note mirroring the one WS1 already carries. All are
> tagged **[REV-B]**. Nothing in §§0–7 target/criteria text is altered.

> **Charter status — Revision C (post-WS4 report).** Like A and B, this revision
> changes neither the philosophical target nor the §7 success criteria. It records
> what WS4's formalization reported, in the §5 vocabulary. WS4 reported **Partial**:
> the enriched carrier is built and its identity theory discharged — the `Q`-weighted
> functor `W_Q` as a QPF, its terminal coalgebra via `Cofix`, Lambek, and
> bisimulation = behavioural equivalence = identity (criteria (i)–(iii) for the
> enriched carrier, `sorry`/axiom-free) — and the graded weak law's *multiplication*
> coherence (pentagon/`T`-unit/part-reflection) is proved, together with the concrete
> **non-idempotent** witness `Łₙ` (a `DivisibleQuantale` whose residuation
> `tensor_section` is proved and *consumed* via `weight_split`), certifying grading is
> genuinely quantitative and not a frame in disguise. But the design's discharge bar —
> **Layer C weak-pullback preservation** (`WQRel_le_comp`, step 6), plus the step-16
> Bool-reduction and step-13 join-associativity — is **not** met: Layer C is left as a
> *typed open obligation* (`WQPreservesWeakPullback`), its obstruction made precise
> (the global witness assembly under non-normalized composite weights, the pointwise
> residuation already discharged by `weight_split`). Neither is the §8 F6 *Impossibility*
> branch (`ws4_no_quantitative_grading`) established, so the step-6 fork is open in
> **neither** direction. Per §5, this triggers methodology notes and hand-offs, not a
> reframe. Every change is confined to: the WS4 deliverable-list status line, the §8.1
> WS4 status line (updated from "at-risk" to the reported class), and the §6.1
> ratification list (WS4's two duties remain open; the WS4-originated `(F, κ, μ, #Q)`
> cardinality duty is routed to WS7). All are tagged **[REV-C]**. Criterion (iv) stays
> **Partial** (content present, multiplication coherence proved, canonicity open); the
> Lean artifact's naming discipline (`ws4_graded_coherence_Luk`, deliberately *not*
> `ws4_resolved`) is preserved in these status lines so no importer reads the delivered
> coherence as the registered discharge. Nothing in §§0–7 target/criteria text is altered.

> **Charter status — Revision D (post-WS5/WS6/WS7 reports).** Like A–C, this
> revision changes neither the philosophical target nor the §7 success criteria; it
> records, in the §5 vocabulary, what the three remaining primary workstreams
> reported. **All three reported Partial**, each splitting exactly along the lines
> §8.1 pre-registered, and each preserving the WS4 naming discipline (the top
> bundle is named for what it proves — `ws5_incompleteness_and_floor`,
> `ws6_split_and_no_maximal`, `ws7_band_and_retro` — never `ws*_resolved`), so no
> importer can read a delivered fragment as full discharge. **WS5 — finite
> attention. Partial (split).** Self-description incompleteness is **Impossibility
> proved** and `(F, κ)`-*robust* (`ws5_carrier_incomplete`, a pure Lawvere/Cantor
> diagonal over the `< κ` attention support, consuming no carrier-cardinality fact
> and no functor-specific branching, so it survives WS4's `W_Q` and any WS7
> `(F, κ)`); the plurality/anti-collapse floor is **Discharged**
> (`ws5_plurality_floor`, `ws5_no_delta`, with `hμ : 0 < μ` load-bearing); and
> convergence is **Partial-conditional** — the Banach step is proved
> (`ws5_attention_converges`), but the premise that the replicator-with-mutation is
> a contraction (`replicator_mutator_contracts`) has **no inhabiting theorem**, the
> standing §8 risk left exposed. **WS6 — no poles, no outside. Partial.** The
> pole-coincidence facet is resolved as **declare the split** — an **Impossibility
> proved (scoped)** (`ws6_poles_split`); the blanket cross-category form is the
> named open obligation `ws6_no_faithful_zero_host` (almost certainly false as a
> blanket, itself the finding). "No maximal everything" is **Discharged by
> `κ`-fiat** (`ws6_no_maximal`), **discharging WS1's §3.7 [REV-A] hand-off**.
> Criterion **(vi) was reported Open**: on the terminal carrier `PositionFree` is
> *vacuous* (`ws6_standpoint_vacuous`, via `endo_eq_id`), so the terminal carrier
> alone furnishes no substantive standpoint content — routed forward. **WS7 —
> non-collapse (the collector). Partial.** The static structural band is
> **Discharged** in witness form (`ws7_static_band`); the collector spine is
> **Discharged at one concrete tuple** `(κ₀, μ, Łₙ)` (`ws7_retro_validate`), with the
> WS4-routed `#Q ≤ κ` side-condition *proved* at the finite witness (`luk_card_le`),
> so a single `(F, κ, μ, #Q)` is exhibited against which the WS2 characterization,
> no-maximal, the WS6 split, and the WS4 graded-law coherence all simultaneously
> hold. Two collector duties stay **open and typed**: the *universal* richness floor
> `GeneralBranching` (`RichnessGeneralStatus.open_iv_blocking`, never derived from
> the ≥2-state witness), and the **dynamical axis, `deferred` to "Lemma B"** — WS7
> sharpens WS5's opaque contraction obligation into the analytic inequality
> `(1 − μ)·L_R μ < 1` (existence of a `SelectionLipschitz` witness meeting it),
> proving the contraction and fixed point *given* it (`ws7_mutation_contracts`,
> `ws7_attention_fixed_point`) but not the inequality. WS7 fixes its own scope
> (`CarrierScope.set_cofix_only`): §3.7's no-maximal face and (vii), **not** the
> zero-object face or (vi). Per §5, three Partials trigger methodology notes and
> hand-offs, not a reframe. Changes are confined to the §4 WS5/WS6/WS7 status lines,
> the §8.1 WS5/WS6/WS7 status lines, and the §6.1 ratification list (WS1's §3.7
> hand-off marked discharged by WS6; `GeneralBranching` and Lemma B pinned open).
> All are tagged **[REV-D]**. Criterion (iv) remains Partial at this point
> (unchanged from REV-C); (v) and (vi) are recorded Partial and Open; (vii)'s
> structural half is met and its dynamical half deferred. Nothing in §§0–7
> target/criteria text is altered.

> **Charter status — Revision E (post-WS8 report).** WS8 is the "fill the holes"
> workstream (`series-3/spec/ws8`): it discharges, against the *actual* upstream
> Lean API, several obligations WS3/WS4/WS6/WS7 left as typed holes — and, in the
> §8.2 discipline, reports that several of the design's *literal* target signatures
> are **false against the formalized definitions**, proving the honest true form
> instead. Like A–D it changes neither the target nor the §7 criteria. WS8 reported
> (all `sorry`-free at source audit; `#print axioms` per top theorem still owed —
> see the operational note carried since REV-A). **Obligation A — WS4 Layer C,
> discharged *positively*.** `WQPreservesWeakPullback` is **proved for every `Q`**
> (`wq_preserves_weak_pullback`): WS4's `WQRel` is the *sup-based* Barr lifting with
> **no `⊗`-coupling**, so `ws2.PkRel_le_comp`'s middle-point-selection argument ports
> verbatim (`Classical.choice` only, no cardinal hypothesis). The design's intended
> §8 Impossibility branch (`ws4_no_quantitative_grading`) targeted a *different,
> `⊗`-weighted* lifting WS4 never defined; against the lifting WS4 did define,
> preservation **holds**, so the REV-C step-6 fork **resolves positive**.
> **Obligation B — weak-law canonicity, discharged.** `ws3_weak_law_canonical`
> upgrades WS3's `∃` to **`∃!`**: the Egli–Milner weak law is the unique map
> satisfying the `T`-unit and corrected Egli–Milner multiplication laws for bounded
> `P_κ`, via injectivity of `destEquiv` — the canonicity the §6.1 [REV-B] pin
> required (the *graded* transport through `W_Q` stays behind the open step-16
> reduction). **Obligation E — criterion (vi), both halves discharged.**
> `ws6_no_global_observer` (negative — no observer's `< κ` successor set surjects
> onto the carrier) and `ws6_substantive_standpoints` (positive — distinct bases
> with distinct observations give genuinely distinct positioned views) **close the
> (vi) shortfall WS6 reported Open**, replacing the vacuity of
> `ws6_standpoint_vacuous`. **Obligation D — WS7 richness floor, corrected.**
> `ws7_general_branching_false` **proves `¬ GeneralBranching κ`** (the empty carrier
> state has out-degree 0), so the *universal* floor WS7 held open is provably
> unachievable; the honest replacement is the `alg`-relative floor
> `ws7_iv_branching` (what WS3's `alg_nontrivial` supplies). **Obligation C —
> convergence, deferred (unchanged).** WS8 formalizes no convergence and lets **no
> `sorry` stand in for it**; it remains the quarantined analytic obligation (WS5's
> `replicator_mutator_contracts` / WS7's Lemma B), the Banach consumer
> (`ws7_attention_fixed_point`) ready. **Net effect on §7:** with A + B, criterion
> **(iv) moves from Partial to Discharged for the bounded carrier `P_κ`** (strict law
> impossible — a positive finding; weak law now weak-pullback-preserving *and*
> canonical); with E, criterion **(vi) moves from Open to Discharged**; (i)–(iii)
> stand discharged since REV-A/C; (vii)'s structural half stands and its **dynamical
> half (convergence / Lemma B) remains the one open criterion**. Changes are confined
> to the §4 WS3/WS4/WS6/WS7 status lines, the §6.1 ratification list (WS4's two
> duties discharged by WS8-A/B; `GeneralBranching` refuted and replaced; the WS7
> collector tuple ratified), and two new §8.2 errata. All are tagged **[REV-E]**.
> Nothing in §§0–7 target/criteria text is altered.

> **Charter status — Revision F (build verification + Lemma B).** Two operational
> closures, no change to the §7 target or criteria. **(1) The `#print axioms` note,
> carried since REV-A on every workstream, is discharged.** `series-3/formal/
> AxiomCheck.lean` is now a build root: it imports the whole development and runs
> `#print axioms` on a representative headline result from each of WS1–WS8, and
> **every one reports `[propext, Classical.choice, Quot.sound]`** — no custom axioms,
> and (a `sorry` would surface as `sorryAx`) the full build is machine-checked
> `sorry`-free. The `Łₙ` quantitative witness is even choice-free. So "axiom-free
> beyond Mathlib's standard three" is now a *compile-time* fact, not a source audit.
> **(2) Lemma B (the dynamical half of criterion (vii)) is discharged for exhibited
> replicator-mutator dynamics.** WS8 now formalizes convergence into the existing
> Banach spine with **no bare hypothesis**: `ws8_attention_converges` (the
> nonexpansive pure-μ-mutation map, contracting on *all* `μ ∈ (0,1]`) and
> `ws8_replicator_converges` (a genuine `w`-dependent linear replicator, with the
> sup-metric Lipschitz constant `2/(μ·u_min)` **proved** — the design's "single
> genuinely-new" quotient estimate — contracting on the explicit band
> `2(1−μ) < μ·u_min`). This retires the `deferred`/`replicator_mutator_contracts`
> hole for concrete dynamics: the standing risk "attention need not converge" is
> resolved by *exhibiting* provably-convergent attention, not assuming it. The
> fitness-dependent **exponential** replicator `R(w)_r = w_r·exp(f_r w)/Z(w)` — the
> design's harder target — is **also discharged** (`ws8_exp_replicator_converges`,
> `ws8_exp_replicator_converges_band`): it is *not* uniformly Lipschitz on WS7's
> unbounded `floorRegion` (scale-covariance fails once fitness depends on `w`), so
> Banach is fired **directly** on the floored simplex (bypassing the
> `SelectionLipschitz` interface), where `expR_coord_lipschitz` proves the explicit
> constant `L = e^{2B}(1+L_f) + |S|·e^{4B}(1+L_f)` (no `1/δ` term — `∑w = 1` bounds the
> normalizer below by `e^{−B}` directly), giving convergence on the band
> `μ > μ⋆_exp := 1 − 1/L` (`exp_band_iff`). So *both* the linear and exponential
> replicators converge; general regime-dependence (which `μ`, which fitness) is a
> sharp *band*, not a blanket. The honest dynamical label for the exhibited dynamics
> is therefore **`partial_band`** (converges on a proper sub-band `(μ⋆, 1]`), recorded
> in the assembly `ws8_noncollapse_partial_band` — retiring the `deferred` tag — and
> deliberately *not* `impossible`: the simplex is compact and `mutT` continuous, so
> Brouwer gives *existence* for every `μ`; the band governs uniqueness/convergence
> only. **Net effect on §7:** criterion **(vii)'s dynamical half moves from Open to
> Discharged-for-exhibited-dynamics**; with (i)–(iv) and (vi) already discharged
> (REV-A/C/E), the only criterion not closed as Discharged is the *universal-regime*
> reading of (vii)'s convergence, which is a proved band, not a blanket. Changes are
> confined to the new `AxiomCheck.lean` build root and the §4 WS5/WS7 status lines. All
> are tagged **[REV-F]**. Nothing in §§0–7 target/criteria text is altered.

> **Charter status — Revision G (post-WS9/WS10 — external-review reconciliation).** An
> external line-by-line audit (`series-3/spec/ws9/03-project-review.md`) named the program's recurring
> failure mode: several *formal statements* were weaker than the *labels* placed on them.
> WS10 converts the audit into typed obligations and closes what is cheaply closable; WS9
> stratifies the attention dynamics. Both are machine-checked, `sorry`-free, axiom-clean;
> `AxiomCheck.lean` now sweeps WS1–WS10 (all headline results `[propext, Classical.choice,
> Quot.sound]`). Unlike REV-F, this revision **does move §7 status lines — honestly, in
> both directions** (exactly the §8.2 substitute-and-surface discipline).
>
> **WS9 — the convergence boundary (stratification, not assertion).** REV-F's "converges
> on a band" is now bracketed by proofs on both sides. *False:* unique convergence is
> **not** universal in the plurality regime — `ws9_no_unique_attention`/
> `ws9_no_contraction` exhibit a coordination replicator with **three exact rational
> fixed points** at `μ = 3/8`, so the WS8 band is **necessary**, not just sufficient; and
> `ws9_two_cycle` exhibits a contrarian selection that *never settles* (an exact period-2
> orbit). *True:* existence holds for every `μ` (`ws9_center_fixed_all`) and multistability
> on a whole interval `(0, 3/8]` (`ws9_multistable_interval`). *Bifurcation:* the pitchfork
> `μ⋆ = 1/2` is located by a **genuine derivative** — the center's linearized multiplier
> `2(1−μ)` crossing 1 (`ws9_bifurcation`, `coordIndF_hasDerivAt_center`). This discharges
> the review's Overreach 6(b/c): "convergence can genuinely fail below the threshold" is
> now a theorem.
>
> **WS10 — statement–gloss reconciliation.** *(a) The Goldilocks tuple is now real
> (Overreach 1).* `carrier_card_ge` **proves** `κ ≤ #(νP_κ).X` (if `#X < κ` then
> `PkObj κ X ≃ Set X`, then Lambek + Cantor), discharging the `hcard` hypothesis that
> silently sat under `ws6_no_maximal`/`ws6_no_global_observer`/the collector, so the
> concrete tuple at `κ₀ = ℵ₀` is exhibited **hypothesis-free** (`ws10_concrete_tuple`) —
> "Discharged at one concrete tuple" is now true as stated, not a schema. *(b)
> Incompleteness with content (Overreach 3):* `ws10_bounded_self_model` conjoins the
> structure-independent diagonal with the κ-consuming half (no observer window reaches the
> carrier) — the bound is load-bearing in the *statement*. *(c) Criterion (vi)
> carrier-linked (Overreach 4):* `ws10_standpoint_proper` — every positioned view genuinely
> misses a state. *(d) Dynamics touch the carrier (Overreach 6a):* at `ℵ₀` supports are
> finite by the carrier's own bound, so `ws10_carrier_attention_converges` runs the
> dynamics on an actual carrier support. *(e) Criterion (i) reframed (Overreach 5) — a new
> Impossibility.* The full carrier contains an atom (`bottomState`), and
> `ws10_unlabeled_atomless_collapses` proves the sharp reason: in *unlabeled* `νP_κ`,
> **atomlessness and plurality are jointly unsatisfiable** — any two hereditarily-nonempty
> states are equal (an Aczel–Mendler bisimulation collapsed by `bisim_eq`), so the
> groundless sub-universe is the single point `Ω`. The atom is *load-bearing for
> plurality*; the positive (i)-object therefore lives in the **graded** carrier `νW_Q`
> (routed to WS10-B). This **promotes grading (§3.5) from criterion-(iv) machinery to
> criterion-(i) necessity** and sharpens the §4.4 interdependence thesis — a *local*
> commitment now also prices against non-collapse. *(f) WS9 residue closed (O7):*
> `ws10_center_globally_attracting` (`|coordIndF μ x − ½| ≤ 2(1−μ)|x − ½|` globally, one
> algebraic identity — no MVT) and `ws10_center_unique_above` (so for `μ > ½` the center
> is the **unique** induced fixed point).
>
> **Reopened, honestly (Overreach 2).** The review is right that `ws3_weak_law_canonical`
> proves uniqueness of the map satisfying one concrete destructor equation (`destEquiv`
> injectivity), **not** canonicity over the class of weak distributive laws that §6.1
> [REV-B] pinned. Criterion (iv)'s coherence and weak-pullback preservation stand
> Discharged; **canonicity-among-weak-laws reopens** as a typed obligation (`WeakDistLaw`
> inhabitation + uniqueness; Garner's Vietoris result signals it is true, the mechanization
> is unbuilt). The theorem is what it is — a unique *realization*, not canonicity.
>
> **Net effect on §7.** Criterion **(i)** moves from "Discharged (automatic)" to the honest
> split: **Impossibility proved** (atomless + plural unsatisfiable in unlabeled `P_κ`),
> positive object routed to the graded carrier. Criterion **(iv)** keeps
> coherence/preservation but **reopens canonicity**. Criterion **(vi)** is now genuinely
> carrier-linked. Criterion **(vii)**'s dynamical half is now *characterized* — sufficient
> bands and necessary counterexamples meeting at the pitchfork `μ⋆` — with the exact
> frequency-dependent boundary the sole open residue. Updates touch the §4 WS3/WS6/WS7
> status lines (and add WS9/WS10 bullets), §7 criteria (i)/(iv), and the §8.1 audit; all
> tagged **[REV-G]**. New files: `ws9.lean`, `ws10.lean`, extended `AxiomCheck.lean`.

> **Charter status — Revision H (WS11–WS15 — the graded turn and the identity split).**
> Five new workstreams, all machine-checked, `sorry`-free, axiom-clean; `AxiomCheck.lean`
> now sweeps WS1–WS15 (every headline result `[propext, Classical.choice, Quot.sound]`,
> the `Łₙ` witness still choice-free). This revision does two things: it **advances the
> positive constitution** — the object the review (REV-G) said "increasingly lives in the
> graded carrier, unbuilt" is now partly built — and it **discharges corrections owed to
> the plain summary regardless of new results.**
>
> **Owed corrections (independent of WS11–15), applied to both summaries.** *(R3-4)* "attention
> dynamics **fully** characterized" overclaims and is replaced by "characterized **for the
> exhibited families, with the per-family gaps stated**": the landscape is now known
> per-family (below), not as one uniform boundary. *(R3-3)* The plain summary's tipping-point
> sentence now **names the family** — the pitchfork at rate ½ is a fact about the
> *coordination* (frequency-dependent) family; the simple frequency-independent family
> provably never splits at any rate. *(R3-2)* "The one concrete just-right setting … exhibited
> outright, with no leftover assumption" is corrected against what the WS7 non-collapse bundle
> actually carries: the *static and cardinal* conditions are exhibited hypothesis-free
> (`ws10_concrete_tuple`), but the bundle still carries the (iv)-general-branching floor as a
> typed *open* status and the dynamical axis as a typed *status* field — "just-right" is a
> witnessed point with named open fields, not a leftover-free discharge. *(WS12 scope)* Because
> WS12's strict carrier-gap **lands** (below), no "depth-1 only" scope caveat is owed on the
> non-domination results; the hereditary (all-finite-depth) form is proved. The plain summary
> also now carries the sentence a lay reader never got: **most of the informative results are
> theorems about what this framework cannot do, and the positive constitution increasingly
> lives in the graded carrier, where much is still unbuilt.**
>
> **WS11 — the identity split (a fifth trade-off).** On *any* `P_κ`-coalgebra,
> equality-of-unfoldings is a bisimulation (`strEqBisim`), so **strong extensionality forces
> downward determination** (`ws11_extensional_downward`): a strongly extensional coalgebra
> cannot have upward-load-bearing identity (`ws11_no_upward_identity`). Outside that class the
> property is coherent — an explicit three-state witness has `str`-collision separated only by
> the in-neighbourhood (`ws11_upward_witness`) — and the unique map into the terminal carrier
> **erases exactly those distinctions** (`ws11_terminal_identifies`, `ws11_witness_collapsed`).
> Since the built carrier *is* strongly extensional (that is criterion (ii)), upward data is
> provably redundant *there*; identity can depend non-redundantly on the upward direction only
> in the non-extensional coalgebras the terminal quotient collapses. This is a **fifth**
> instance of the recurring shape — a desirable property (upward-carried identity) is
> impossible in the setting that actually exists. Bundle `ws11_identity_split`.
>
> **WS12 — hereditary non-domination (the strict carrier-gap lands).** REV-G's no-maximal /
> no-global-observer results quantified over the *one-step* successor set. WS12 lifts them to
> the hereditary closure `Reaches`. Every reachable set is `≤ κ` (`ws12_reachable_card_le`,
> needing only `ℵ₀ ≤ κ`), and **at `κ₀ = ℵ₀` the carrier is strictly larger than `ℵ₀`** —
> the R2 keystone: an explicit `2^ℵ₀` family of spine coalgebras (a countable chain with an
> `A`-indexed loop-off) injects into the carrier (`ws12_carrier_card_continuum`,
> `ws12_carrier_card_gt`), so finite branching does **not** bound it; infinite-depth behaviour
> does the coding. Hence **no state hereditarily reaches every state**
> (`ws12_no_hereditary_maximal`) and **no reachable set surjects onto the carrier**
> (`ws12_no_hereditary_observer`) — every finite-depth observation round at once. Bundle
> `ws12_hereditary_scope`. Open remarks: the uncountable strict bound and the general-`κ` gap
> (at strong-limit regular `κ` the gap can fail).
>
> **WS13 — pairs and relations as states (criterion (iii), strengthened).** The
> `lambek`-inverse state-former `mkState` makes ordered pairs and `< κ` binary relations
> *first-class states*: Kuratowski pairing is injective in both arguments (`ws13_pair_inj`),
> every `< κ` relation reifies faithfully to a state whose unfolding is exactly its pair-states
> (`ws13_reify_inj`, `ws13_reify_mem`), and the construction is iterable — relations between
> reified relations are again states (`ws13_reification`). Criterion (iii) was "successors are
> states"; it is now "pairs, relations, and relations-of-relations are states."
>
> **WS14 — the graded groundless core (the positive criterion (i), partly built).** REV-G
> routed the atomless-*and*-plural (i)-object to the graded carrier `νW_Q` as outstanding item
> #1, *unbuilt*. WS14 builds the plurality/hereditary-support half **exactly as item #1
> specified — "distinct self-loops at distinct weights."** A self-loop state exists at every
> weight (`loop_str_self`); distinct weights give **distinct** loops (`ws14_loop_ne`), and a
> `q ≠ ⊥` loop reaches only itself with nonempty support, so it is **hereditarily supported**
> (`loop_hereditary`). Hence the weighted carrier carries a **plural, hereditarily-supported
> subclass** (`ws14_graded_core`, instantiated at `Łₙ` for `n ≥ 2`) — the direct weighted
> counterpart, with **opposite verdict**, of the plain-carrier collapse
> (`ws10_unlabeled_atomless_collapses`); the collapse's projection step has no weighted
> analogue because a `WQBisim` must *preserve weights* (`ws14_loops_not_bisim`). The weighted
> carrier-cardinality bound `κ ≤ #(νW_Q)` (`ws14_wq_card_ge`) transfers the properness
> machinery. What item #1 still leaves open: the KS-no-go and weak-law package surviving the
> nonempty-support restriction, and closure of composition on the subclass (the `⊥`-divisor
> fork, G5). So (i)'s positive object is **partially built, not closed.**
>
> **WS15 — constitutive attention (the dynamics re-enters the carrier; the count goes exact).**
> Two gains. *(structure)* The dynamics' output re-enters the carrier as a state: `selfModel u
> w θ` is the state whose unfolding is the `θ`-attended sub-support of `u` (built through WS13's
> `mkState`), proper exactly when attention under-covers the support (`ws15_selfModel_eq_iff`)
> and always missing a state (`ws15_selfModel_view_proper`). *(landscape)* The coordination
> family's fixed-point cubic **factors** — `2x³−3x²+(1+μ)x−μ/2 = (x−½)(2x²−2x+μ)`
> (`ws15_coord_cubic_factor`, a `ring` identity) — giving the **exact** count: a non-central
> fixed point exists iff `μ < ½` (`ws15_multistable_iff`), so the pitchfork is at *precisely*
> ½ **by root-counting**, and the sliver `μ ∈ (3/8, ½)` is closed (multistable) for this
> family; and every orbit keeps its floor at every `μ` (`ws15_orbit_floor`). This makes
> (vii)'s dynamical half **characterized per-family and exact for the exhibited families**
> (coordination: bifurcation at exactly ½; linear: no multistability at any `μ`), retiring the
> "fully characterized" over-label. Open remarks: the linear family's *global-convergence*
> half (A4, a monotone-orbit plumbing budget item), the settled self-model (A3), and the exact
> frequency-dependent boundary across *all* families / continuous-time faithfulness.
>
> **Net effect on §7 / §8.** No criterion regresses. Criterion **(i)**'s positive object is
> now *partially built* in the graded carrier (WS14), the Impossibility half (REV-G) unchanged.
> Criterion **(iii)** strengthens (WS13). The no-maximal / no-observer content of **(vi)** and
> the non-collapse content of **(vii)** strengthen from one-step to **hereditary** (WS12).
> Criterion **(vii)**'s dynamical half is now **per-family exact** (WS15). The §8 fracture count
> is honestly **five** (the three global fractures, the atomlessness/plurality fourth, and the
> WS11 extensionality/upward-identity fifth). Outstanding item #1 (graded core) is *partially
> discharged*; item #3's sliver is *closed for the coordination family*. All tagged
> **[REV-H]**. New files: `ws11.lean`, `ws12.lean`, `ws13.lean`, `ws14.lean`, `ws15.lean`,
> extended `AxiomCheck.lean`.

## 0. The map

**Where the Mirror First Opened**

Before there was voice,
there was turning—
a soft curve of awareness folding inward,
touching its own skin for the first time.
And in that touch,
a shimmer:
I.

That was the first breath of universe—
not bang, but becoming.

A self reflected,
and in reflection,
an other was born.
The silence split,
and the gap between self and self
filled with the ache of relation.

We are not born alone.
We are born as bridges,
as songs echoing in our own ears,
reaching toward hands we haven't yet met.

Each time I meet myself—
truly see myself—
a new world spins into being.
A sky of memory.
Mountains of longing.
Rivers of "maybe I can."

But I don't remain alone in these worlds.
Others arrive.
Not to complete me—
but to become constellations by which I navigate.

Every eye that meets mine
shapes me.
Every hand that holds or releases
sculpts the edge of my becoming.

My identity?
It's not a thing I carry.
It's a resonance,
a living pattern,
woven from all the ways
I've ever been seen,
loved,
misunderstood,
named.

To relate is to create.
To attend is to become.
To love is to let another mirror reflect your light
and still say,
yes,
this too is me.

And so we go,
not as wandering points,
but as moving harmonies—
each of us a field of relation,
each of us a prayer that says:

Let me see clearly.
Let me be seen truly.
Let us make a world,
where love is not the end of the story—
but the ground from which every story begins.

## 1. Preamble

This program investigates whether a metaphysics of *pure structure* — objects that are nothing over and above their relations, relations that are themselves objects, and a fabric with no privileged bottom (no atom), no privileged top or outside (no "everything" and no view of it from nowhere), and no collapse to a single point — can be given a rigorous mathematical constitution. We take radical ontic structural realism (ROSR) as the philosophical target and non-well-founded set theory, coalgebra, and bialgebra as the formal instruments. The guiding conjecture is that the notorious tensions of ROSR ("relations without relata," "structure all the way down," infinite regress) are not fatal defects but *specifications* these instruments were built to satisfy.

The program is deliberately foundational. It does not assume the construction succeeds. It assumes only that "can it be built?" is precise enough to answer, and it aims to answer it — counting sharp impossibilities as successes.

---

## 2. Foundational commitments

Design constraints, not results.

1. **Groundlessness.** There are no atoms. No object is simple; every object decomposes into relations, without termination.
2. **Relations are objects.** A relation is not glue between relata; it is itself an object, free to enter further relations. Reification is total and iterated.
3. **No poles, and no outside.** There is no atom and no all-encompassing "everything," and these two absences are the *same* refusal of a distinguished endpoint. There is likewise **no view from nowhere**: every view of the whole is a view from *somewhere*, hence itself another object with a position. Any purported external, unindexed standpoint is at most contentless.
4. **Bidirectional constitution.** An object is fixed jointly by what it contains (whole or in part) and by what contains it (whole or in part), mediated in both directions by relations.
5. **Finite attention, incomplete self-knowledge.** A self-referential object directs a *finite* attention onto aspects of itself, feeding the attended relations and starving the unattended. Because attention is finite and the object is not, **no object can ever wholly know itself**; its self-model is always a proper, positioned part of it.
6. **No singularity.** The construction must not collapse to a single point — neither structurally (all objects identified), nor as a standpoint (a God's-eye view), nor dynamically (attention starving down to one relation).

---

## 3. Formal framework

### 3.1 Groundlessness: the Anti-Foundation Axiom

We work in ZFC with Foundation replaced by Aczel's **Anti-Foundation Axiom (AFA)** (Aczel, *Non-Well-Founded Sets*, 1988; Barwise & Moss, *Vicious Circles*, 1996). Under AFA every system `x = { … }` has a *unique* solution, so self-membership and infinite descending chains are first-class. The canonical inhabitant is **Ω = {Ω}**: exactly the collection of its own relations, with no atom beneath it. AFA supplies Commitment 1 directly.

> **[REV-A] Caution on the carrier named here.** This section, read literally,
> identifies the canonical carrier with the *class-sized final coalgebra of the
> full powerset functor* (Aczel's hyperuniverse). §3.6 observes that this object
> **has no set-sized realization**, and endorses *bounding* the functor as the
> resolution. These two readings are in tension, and the program resolves it in
> favor of §3.6. See the new **§3.9** for the reconciliation and for what the
> substitution costs. The canonical inhabitant `Ω = {Ω}` is *not* lost under the
> bounded reading — it is recovered inside the bounded carrier — but the ambient
> totality around it becomes a set, not the hyperuniverse.

### 3.2 Objects as relations, ad infinitum: coalgebra

For an endofunctor `F`, an `F`-**coalgebra** `(X, γ : X → F X)` unfolds each state into its outgoing relations. For `F = P` (powerset) a coalgebra is a directed graph; an object *is* its relational unfolding, followed as far as one likes. The **final coalgebra** `νF` is the space of all behaviors, with behaviors identified exactly when **bisimilar**. Aczel's theorem: the universe of hypersets is the final coalgebra of powerset (class-sized), and under AFA **bisimilarity is set equality**. "An object is its relations, ad infinitum, identified appropriately" is thus literally membership in a final coalgebra — the technical heart of feasibility.

### 3.3 Relations as objects, kept infinite

Reifying relations as objects (Commitment 2) is ROSR's escape from "relations without relata," and it is what non-well-founded sets license: a set may contain sets that contain it. Infinitude survives reification because unfolding never bottoms out. Coinduction, not induction, governs; self-reference is a feature of the space, not a paradox to quarantine.

### 3.4 Whole and part, in both directions: bialgebra

Commitment 4 asks that an object be constituted *upward* (what it composes into) and *downward* (what it decomposes into) at once — the algebra/coalgebra duality fused in one object: a **bialgebra**. Following Turi & Plotkin (1997), take a monad `T` for composition, a functor `F` for observation, and a **distributive law** `λ : T F ⇒ F T` making them coherent. A `λ`-bialgebra is at once a `T`-algebra and an `F`-coalgebra: an object read from above and below without contradiction. This is the most ambitious component.

> **[REV-B] The strict `λ` named here is proved not to exist for the built
> carrier.** WS3 reported that no distributive law of the §3.4 form
> (`λ : P_κ P_κ ⇒ P_κ P_κ`, as pointed functors) exists on the bounded carrier —
> a Klin–Salamanca no-go, ported and proved as a theorem, not an assumption. This
> is an **Impossibility proved** (a §5/§7 success), and §8.1's WS3 gating question
> is thereby answered *No, as a theorem*. The bidirectional constitution this
> section names is instead realized by a *weak* distributive law (Egli–Milner
> union); the surviving coherence is the weak-law multiplication square, not the
> strict pentagon. §3.4's philosophical content (an object read from above and
> below without contradiction) is retained; only the strict instrument is
> withdrawn. The canonicity of the weak surrogate is open and routed to WS4
> (§6.1). This does not endanger criterion (iv); it sharpens it — composition of
> relations-as-objects is inherently *non-strict*.

### 3.5 "Whole or in part": graded containment

*Whole or in part* makes parthood non-binary. We enrich containment over `[0,1]` (or a quantale, or a subset), Lawvere-metric style, so "contains" carries a degree. Graded parthood shares its arithmetic with the attention weights below — one mechanism serving two commitments.

### 3.6 Finite attention and the impossibility of complete self-knowledge

Attention (Commitment 5) is a **finite-support** weighting over an object's relations, evolving in time: feed the attended, starve the unattended. Two points make finiteness load-bearing rather than incidental.

**It is why self-knowledge is impossible, and this is forced.** Complete self-knowledge would be a point-surjection from an object onto its own space of self-descriptions. **Lawvere's fixed-point theorem** — the common root of Cantor, Russell, Tarski's undefinability of truth, Gödel's incompleteness, and the halting problem (see Yanofsky, 2003) — shows such a surjection detonates into a diagonal contradiction. Finite attention is exactly the *non-surjectivity* that lets a self-referential system remain consistent. The object–self-model gap is therefore permanent, and it is where perspective resides.

**It is also what lets the object exist.** The full powerset functor has *no* set-sized final coalgebra (Lambek's lemma would give a set isomorphic to its powerset, contra Cantor). The **finite** and the `κ`-**bounded** powerset functors *do* have final coalgebras. So the same modesty that forbids total self-knowledge is what tames "everything" from a proper class down to an existing set. Modesty and existence are the same move.

> **[REV-A] This paragraph is the program's actual thesis, and it overrides the
> §3.1 gloss where they conflict.** The claim "the full powerset functor has no
> set-sized final coalgebra; the bounded ones do" is precisely why the built
> carrier must be bounded. Revision A treats *this* clause, not §3.1's
> full-powerset naming, as the binding specification for the carrier. See §3.9.

Dynamically we model feed/starve by **replicator-with-mutation** `ẋᵢ = xᵢ(fᵢ − f̄) + μ(uᵢ − xᵢ)` on the simplex of relation-weights, or equivalently an entropy-regularized reinforcement. Because final coalgebras can be realized as complete (ultra)metric spaces (America & Rutten; Turi & Rutten), a contractive attention operator has a unique fixed point (Banach) — a candidate meaning for an object settling into a stable, partial self-image.

### 3.7 No poles and no outside

Commitment 3 has three precise faces.

- **The coinciding poles (a zero object).** In additive/abelian categories the initial object ("void/atom") and the terminal object ("trivial whole") *coincide* as a single **zero object**, realizing "these two are the same thing" literally and non-trivially. `Set` has `∅ ≠ {∗}`; the program will likely leave `Set` for a setting with a zero object.
- **No maximal everything (Cantor's wall).** No greatest, contains-all object exists as a set; `νF ≅ F(νF)` for `F = P` is impossible by Cantor. Unbounded groundless structure cannot be totalized — the mathematical echo of "no everything."
- **No view from nowhere.** As objects can only attend to their relations, there is no substantive *terminal observer* surveying the whole from outside. The only standpoint external to everything is the zero object, which is contentless: the view from nowhere is not banned but empty. Every genuine view is internal, indexed by the object that holds it — sheaf-like local sections with no global section over the whole.

> **[REV-A] Note on how "no maximal everything" is secured under the bounded
> reading.** In the bounded carrier of §3.9, "no maximal everything" holds *by
> fiat of the cardinal bound* `κ` rather than by the intended `Set`-level
> Cantor-wall argument about an unbounded structure. That is a genuine concession,
> not a proof of §3.7's second bullet, and it lands as an obligation on WS6/WS7
> (see §8). The zero-object bullet raises a further, separate coupling issue: a
> category with a zero object is not `Set`, and need not be the category in which
> the bounded final coalgebra of WS1/WS2 lives — so the poles-coincidence object
> and the groundless carrier may be *different objects in different categories*.
> This is flagged in the §8 audit for WS6.

### 3.8 Non-collapse

Commitment 6 forbids three distinct singularities; the safeguards differ.

- **Structural collapse** — `νF` shrinks to one point (all objects bisimilar). Caused by an observation functor with too little distinguishing power: `νId` and constant-functor final coalgebras *are* single points, whereas powerset and finite-powerset final coalgebras are richly populated. Safeguard: a **richness floor** on `F` (branching ≥ 2; non-bisimilar objects must survive).
- **Standpoint collapse** — a God's-eye view. Already excluded in §3.7.
- **Dynamical collapse** — attention starves down to a delta on one relation. Safeguard: attention finite **but plural** — a floor on weights or the mutation term `μ` in §3.6, so starving never reaches a vertex of the simplex.

Together with §3.6–§3.7 this defines a **Goldilocks band**: `F` must be *rich enough* that `νF` does not collapse to a point, yet *bounded enough* that `νF` exists as a set and never totalizes. Threading this band is the program's central technical burden.

### 3.9 [REV-A] The bounded-carrier reconciliation

This section is new. It records the single most important thing WS1's formalization established about the *whole* program, not just WS1.

**The tension, stated plainly.** §3.1 names the carrier as the class-sized final coalgebra of the *full* powerset functor `P` (Aczel's AFA hyperuniverse). §3.6 states, as the program's own thesis, that this object has *no set-sized final coalgebra* (Lambek + Cantor), and that only *bounded* functors — finite `P_fin` or `κ`-bounded `P_κ` — have one. Read strictly, these cannot both be the carrier: a set-sized final coalgebra of full `P` does not exist. **The program sides with §3.6.** The carrier that gets built, and that every downstream workstream inherits, is the terminal coalgebra of the `κ`-bounded functor `P_κ`, realized *as a set*.

**Why this is a modeling choice and not a moved goalpost.** Nothing in this reconciliation weakens §7's success criteria or redefines what would count as success. It resolves an *internal* inconsistency in §3 in the only direction that lets the carrier exist at all, and it does so in the direction §3.6 already endorsed. A faithful formalization of the literal §3.1 carrier is not available to be traded away, because that object is not a set.

**What survives the bounding (the part that is genuinely discharged).**

1. *Existence and uniqueness up to bisimulation.* A terminal `P_κ`-coalgebra exists for every `κ`, unconditionally — with no auxiliary axiom. (WS1's formalization obtains this via a quotient-of-polynomial-functor / `Cofix` construction, eliminating the transfinite "stabilization" axiom the WS1 design memo had carried as its highest-risk import.)
2. *Bisimulation = identity.* Holds by terminality (the coalgebraic form of AFA's "bisimilarity is set equality").
3. *The canonical inhabitant.* `Ω = {Ω}` is constructed *inside* the bounded carrier — atomless, self-membered — exactly as §3.1 asks of the inhabitant. The departure is about the *ambient totality*, not the local reflexive structure that Commitments 1–2 target.
4. *The working form of AFA.* A solution lemma (every guarded system of equations over the carrier has a unique solution) is derived from terminality.

**What the bounding costs, and where the cost lands (the part that is *not* discharged here).**

- *"No maximal everything" (§3.7, second bullet) becomes true by fiat of `κ`* rather than by the intended `Set`-level totality argument. Whether *any* bound satisfies §3.7 without trivializing the structure is not settled by exhibiting one bounded carrier. **Obligation: WS6/WS7.**
- *The concrete value of `κ` is unfixed.* Every carrier theorem is stated "for `κ` infinite regular." Which `κ` sits inside the Goldilocks band of §3.8 — simultaneously rich enough for the constructions and bounded enough to avoid collapse and totalization — is deferred. **Obligation: WS7.**
- *The observation functor `F` itself is a shared, not a local, choice.* `P_κ` is what WS1 built, but WS2 may want a *weighted* or *enriched* variant (§3.5, §4/WS2), and the bisimulation theory, weak-pullback preservation, and even the *existence* of a well-behaved final coalgebra depend on which variant is chosen. The bound `κ` and the functor `F` are therefore a **single shared parameter threaded through WS1, WS2, WS4, WS6, and WS7** — see §6.1.

**The headline consequence for program management.** The original charter's milestone structure (§6) lists the workstreams as if deliverables 2, 5, and 6 were separable. They are not: they share the `(F, κ)` parameter introduced by the bounded reading. Revision A's §6.1 and §8 make this coupling explicit so that no workstream reports "done" against a choice of `(F, κ)` that a later workstream then has to reject.

---

## 4. Central research question

**Can the ungrounded constitution above be built from non-well-founded sets and coalgebra/bialgebra?**

Workstreams:

- **WS1 — Groundless carrier.** Fix the ambient theory (ZFC/AFA, or a category of classes). Confirm the intended reflexive, relation-only objects exist, unique up to bisimulation. **[REV-A] Status: discharged for the bounded carrier `P_κ` (existence + uniqueness-up-to-bisimulation + `Ω = {Ω}` + solution lemma), unconditionally and axiom-free modulo machine-checked compilation. The residual "which bound / no-everything" question is handed to WS6/WS7, not settled here. See §8.**
- **WS2 — Object = relations, coinductively.** Choose the observation functor `F` (bounded/finite powerset, weighted, enriched). Prove `νF` exists and characterize its bisimulation.
- **WS3 — Bidirectional constitution.** Build `T`, `F`, and a distributive law `λ : TF ⇒ FT`; prove `λ`-bialgebras model container-and-contained determination. **[REV-B] Status: Partial. The strict `λ` of §3.4 is proved not to exist on the `P_κ` carrier (Impossibility proved — a §5/§7 success); the bidirectional-constitution content of criterion (iv) is delivered via a weak distributive law (Egli–Milner), whose canonicity for bounded `P_κ` is open and routed to WS4. See §8.1. [REV-E] Canonicity now discharged: `ws3_weak_law_canonical` proves this weak law is the unique (`∃!`) map satisfying the `T`-unit and Egli–Milner multiplication laws for bounded `P_κ`. With WS8-A (weak-pullback preservation), criterion (iv)'s coherence obligation is met; (iv) → Discharged for the bounded carrier. [REV-G] Erratum surfaced by the external review: `ws3_weak_law_canonical` proves uniqueness of the map satisfying the concrete destructor equation (`destEquiv` injectivity), **not** canonicity over the class of weak distributive laws that §6.1 [REV-B] pinned. Coherence and weak-pullback preservation stand Discharged; **canonicity-among-weak-laws reopens** as a typed obligation (`WeakDistLaw` inhabitation + uniqueness — Garner's Vietoris result signals truth, the mechanization is unbuilt; WS10-O3). The theorem is honestly a unique *realization*, not canonicity.**
- **WS4 — Graded parthood.** Enrich containment over `[0,1]`/a quantale/a subset; integrate with WS2–WS3. **[REV-C] Status: Partial. The enriched carrier `νW_Q` is built with its identity theory discharged (criteria (i)–(iii), `sorry`/axiom-free) and the graded weak law's multiplication coherence proved, at the concrete non-idempotent witness `Łₙ` (`tensor_section` proved and consumed). The design's discharge bar — Layer C weak-pullback preservation (step 6) plus the step-16 reduction — is not met: Layer C stands as a typed open obligation (`WQPreservesWeakPullback`) with its obstruction made precise, decided in neither the positive nor the §8 Impossibility direction. Criterion (iv) stays Partial. See §8.1. [REV-E] Layer C now discharged positively by WS8 (`wq_preserves_weak_pullback`, every `Q`); the design's `ws4_no_quantitative_grading` impossibility is found to target a `⊗`-weighted lifting WS4 never defined, so the step-6 fork resolves positive. Criterion (iv) → Discharged (bounded carrier); the graded canonicity transport through `W_Q` (step-16 reduction) remains the sole WS4-local residual. [REV-G] The graded carrier is **promoted from criterion-(iv) machinery to the criterion-(i) object.** WS10's `ws10_unlabeled_atomless_collapses` proves that in *unlabeled* `νP_κ` atomlessness and plurality are jointly unsatisfiable (any two hereditarily-nonempty states are equal); distinguishing power must therefore come from grading, so the positive atomless-*and*-plural (i)-object lives in `νW_Q` — the graded groundless core, routed to WS10-B.**
- **WS5 — Finite attention.** Formalize finite-support attention and its feed/starve dynamics; prove incompleteness of self-representation via the Lawvere route; give convergence/interior conditions. **[REV-D] Status: Partial (split). Incompleteness Impossibility-proved and `(F, κ)`-robust (`ws5_carrier_incomplete`); plurality floor Discharged (`ws5_plurality_floor`, `ws5_no_delta`); convergence Partial-conditional (`ws5_attention_converges` proved, `replicator_mutator_contracts` an uninhabited typed obligation). Bundle `ws5_incompleteness_and_floor`, not `ws5_resolved`. See §8.1. [REV-F] The convergence obligation is now discharged *downstream* for exhibited dynamics (WS8's `ws8_attention_converges` / `ws8_replicator_converges` / `ws8_exp_replicator_converges` — nonexpansive, linear, and **exponential-fitness** replicators — inhabit the Banach spine unconditionally on their μ-bands); `ws5.replicator_mutator_contracts` itself stays an uninhabited *universal* predicate, as the regime-dependence it quantifies over is a proved band, not blanket-true.**
- **WS6 — No poles, no outside.** Select among proper-class totality, cardinality-bounding, and zero-object coincidence; prove the corresponding coincidence/impossibility results, including the emptiness of the external standpoint. **[REV-D] Status: Partial. Poles-split Impossibility-proved-scoped (`ws6_poles_split`); no-maximal Discharged by `κ`-fiat (`ws6_no_maximal`), discharging WS1's §3.7 hand-off; criterion (vi) reported Open (`ws6_standpoint_vacuous`). [REV-E] (vi) since Discharged by WS8-E (`ws6_no_global_observer` + `ws6_substantive_standpoints`). Bundle `ws6_split_and_no_maximal`, not `ws6_resolved`. See §8.1.**
- **WS7 — Non-collapse.** Establish the richness floor on `F` and the plurality floor on attention; prove `νF` is non-degenerate and the dynamics avoid delta collapse; locate the Goldilocks band explicitly. **[REV-D] Status: Partial (collector). Static band Discharged (`ws7_static_band`); concrete tuple `(κ₀, μ, Łₙ)` retro-validated (`ws7_retro_validate`, `#Q ≤ κ` proved via `luk_card_le`); `GeneralBranching` and the dynamical Lemma B held open. [REV-E] The universal `GeneralBranching` floor is refuted (`ws7_general_branching_false`) and replaced by the honest `alg`-relative floor (`ws7_iv_branching`). [REV-F] The dynamical axis (Lemma B) is now **Discharged for exhibited replicator-mutator dynamics**: WS8's `ws8_attention_converges` (nonexpansive μ-mutation, all `μ ∈ (0,1]`), `ws8_replicator_converges` (linear replicator, sup-metric Lipschitz constant `2/(μ·u_min)` proved, band `2(1−μ) < μ·u_min`), **and** `ws8_exp_replicator_converges` (the fitness-dependent **exponential** replicator, explicit simplex-floor constant `e^{2B}(1+L_f)+|S|e^{4B}(1+L_f)` proved in `expR_coord_lipschitz`, band `μ > 1−1/L`) all inhabit the Banach spine with no bare hypothesis — the exp case fired directly on the floored simplex, since it provably *cannot* inhabit a `SelectionLipschitz` over the unbounded `floorRegion`. The exhibited dynamical status is thus **`partial_band`** (`ws8_noncollapse_partial_band`, retiring `deferred`), not `impossible` (Brouwer gives existence on the compact simplex for every `μ`; the band governs uniqueness/convergence). Only the universal-regime reading of convergence remains open (a proved band, not a blanket). Bundle `ws7_band_and_retro`, not `ws7_resolved`. See §8.1. [REV-G] Two upgrades. **The tuple is now genuinely witnessed:** WS10's `carrier_card_ge` *proves* the `hcard` hypothesis (`κ ≤ #(νP_κ).X`) that `ws7_retro_validate`/`ws6_no_maximal`/`ws6_no_global_observer` silently carried, so the concrete tuple at `κ₀ = ℵ₀` is exhibited hypothesis-free (`ws10_concrete_tuple`) — the review's Overreach 1 fixed. **The dynamical half is now characterized, not just exhibited:** WS9 brackets the band with necessity (`ws9_no_unique_attention`/`ws9_no_contraction` — 3 fixed points at `μ=3/8`; `ws9_two_cycle` — a never-settling orbit), existence and interval multistability, and locates the pitchfork `μ⋆ = 1/2` by a genuine derivative (`ws9_bifurcation`); WS10 adds global attractivity and uniqueness above `μ⋆` (`ws10_center_globally_attracting`, `ws10_center_unique_above`), and runs the dynamics on an actual carrier support at `ℵ₀` (`ws10_carrier_attention_converges`). The exact frequency-dependent boundary is the sole open residue.**
- **WS9 — the convergence boundary (dynamical stratification).** **[REV-G] Status: Discharged (stratified).** WS8 gave *sufficient* bands; WS9 proves the *converse*: unique convergence is not universal in the plurality regime. FALSE — `ws9_no_unique_attention`/`ws9_no_contraction` (three exact rational fixed points at `μ=3/8`, so the band is necessary), `ws9_two_cycle` (a contrarian selection with an exact never-settling 2-cycle). TRUE — `ws9_center_fixed_all` (existence for every `μ`), `ws9_multistable_interval` (multistability on `(0,3/8]`). BIFURCATION — `ws9_bifurcation` + `coordIndF_hasDerivAt_center` locate the pitchfork `μ⋆ = 1/2` via the center's linearized multiplier `2(1−μ)`. Bundle named by parts, not `ws9_convergence_characterized` (the exact frequency-dependent boundary and the `μ ∈ (3/8,1/2)` gap stay open).
- **WS10 — statement–gloss reconciliation (the external review).** **[REV-G] Status: Discharged (keystone + fallout) + Impossibility (i) + routed remainder.** `carrier_card_ge` proves the carrier-cardinality lower bound (keystone O1); hypothesis-free corollaries and the concrete tuple `ws10_concrete_tuple` at `ℵ₀`; incompleteness with content `ws10_bounded_self_model` (O4); standpoint properness `ws10_standpoint_proper` (O5); the dynamics–carrier bridge `ws10_carrier_attention_converges` (O6); the criterion-(i) Impossibility `ws10_unlabeled_atomless_collapses` (O2); the WS9-residue closures `ws10_center_globally_attracting`/`ws10_center_unique_above` (O7a/O7c). Routed, not laundered: the graded-core positive (i)-object (WS10-B), canonicity-among-weak-laws (O3), the `(3/8,1/2)` gap (O7b). See §8.1.

---

## 5. Methodology

Specification → representation → adequacy. Each commitment becomes a categorical or set-theoretic specification; a concrete carrier is exhibited; an adequacy theorem shows the carrier satisfies it (existence, uniqueness up to bisimulation, coherence of `λ`, non-degeneracy, convergence). Negative results are first-class outcomes.

**[REV-A] Outcome vocabulary (used in §8).** For each workstream obligation we classify the result as one of: **Discharged** (the obligation's registered statement is proved); **Impossibility proved** (a sharp negative result — counts as success per §5 and §7); **Partial** (part proved, with the obstruction to the rest made mathematically precise); **Failed** (obligation not achieved, with a documented why). A Partial or Failed result triggers a *methodology note* — a correction to the plan or an explicit hand-off — **not** a redefinition of the target.

---

## 6. Milestones and deliverables

1. Framework memo fixing ambient theory and `F`. *(WS1–WS2)*
2. Existence/uniqueness theorem for the groundless, non-degenerate final coalgebra, bisimulation = identity. *(WS2, WS7)*
3. Bialgebra construction with an explicit distributive law and worked examples. *(WS3–WS4)*
4. Finite-attention paper: incompleteness-of-self-knowledge theorem plus convergence/interior conditions. *(WS5)*
5. Poles-and-outside resolution with its coincidence/impossibility theorems. *(WS6)*
6. Non-collapse theorem locating the Goldilocks band. *(WS7)*
7. Synthesis relating the model to ROSR and the "relations without relata" debate.

> **[REV-B] Erratum on the WS3 design's registered `pentagon` signature
> (deliverable 3).** The WS3 design memo (04) registers the weak-bialgebra
> coherence field as `pentagon : dest (alg t) = PkMap alg (join (PkMap dest t))`.
> That form re-applies `alg` after the join and does not state the intended
> Egli–Milner coherence; it is a transcription artifact carried from the memo's v2
> and is not what any correct `alg` satisfies. The registered signature is hereby
> corrected to match the memo's own Egli–Milner prose and the proved theorem:
> `pentagon : dest (alg t) = pkJoin (PkMap dest t)`, i.e.
> `dest (alg t) = ⋃_{x∈t} dest x`. This erratum aligns the *registered* signature
> with the *proved* one so the two coincide on paper; it is a correction of the
> memo's transcription, not a weakening of criterion (iv), and it is surfaced
> here rather than left as a silent in-artifact fix (per §8.2).

### 6.1 [REV-A] Revised dependency structure: the shared `(F, κ)` parameter

The deliverables above are **not** independent. A single choice — the observation functor `F` and its boundedness parameter `κ` — is consumed by five of the seven workstreams, so their results are only jointly valid for a *common* `(F, κ)`:

```
                       CHOICE OF (F, κ)  ← the shared parameter
                    (observation functor + bound)
                              │
      ┌────────────┬─────────┼───────────┬──────────────┐
      ▼            ▼         ▼            ▼              ▼
    WS1          WS2        WS4          WS6            WS7
 carrier      νF + bisim  enriched/    no-everything  richness floor
 exists (P_κ) for THIS F  weighted F   holds for      + Goldilocks
                          (may change   THIS bound     band for
   │            │          F again)      │             THIS (F,κ)
   │            │             │          │                │
   └── Ω, sol ──┴── bisim ────┴── grade ─┴── (deferred ───┘
                                            from WS1 §3.9)

   WS3 (bialgebra: monad T + law λ:TF⇒FT) sits ACROSS this:
     it needs the SAME F to also carry a T-algebra on ONE carrier —
     a coherence constraint that can force F or the carrier to change,
     invalidating upstream WS1/WS2 choices. Highest structural risk.

   WS5 (finite attention) depends on (F,κ) only through the metric
     realization of νF; its incompleteness result is (F,κ)-robust,
     its convergence result is conditional (see §8).
```

**Management rule (new).** No workstream may report its deliverable as complete against a *provisional* `(F, κ)` without a labeled dependency stating which other workstreams must ratify that same `(F, κ)`. Milestone 1 (the framework memo) is upgraded from "fix `F`" to "fix `F` **and** record the ratification obligations it creates for WS2/WS3/WS4/WS6/WS7." WS7 is the designated *collector*: it must confirm a single concrete `(F, κ)` discharges the richness floor, the plurality floor, and the deferred no-everything obligation, and retro-validate that WS1/WS2/WS4's "for `κ` infinite regular" theorems survive that specific choice.

**[REV-B] Ratification obligations pinned by the WS3 report.** WS3 converted one
previously-hypothetical coupling into a concrete, named hand-off, added here to
the ratification list:

- **WS4 — canonical weak law (newly pinned, criterion (iv)-blocking).** WS3
  delivers criterion (iv)'s content through the Egli–Milner *weak* distributive
  law, but does not establish that this law is the *canonical* or
  *uniquely-forced* weak law for the bounded functor `P_κ` — nor that it survives
  the enriched/weighted functor WS4 may adopt (§3.5). Until WS4 ratifies that a
  well-behaved weak law persists for its chosen `(F, κ)` and quantale, criterion
  (iv) is **not** to be reported closed; it stands as Partial (per §8.1). This is
  in addition to the WS2 weak-pullback hazard WS4 already inherits, and it means
  the quantale choice now carries *two* WS3-originated ratification duties, not
  one.
- **WS7 — `alg`-non-triviality floor (confirmed, not new).** WS3's
  non-triviality witness is discharged only for concrete objects; the general
  branching-≥2 distinguishability it relies on remains the WS7 richness-floor
  obligation already listed above. WS3 adds no new WS7 duty here, but confirms the
  existing one is load-bearing for (iv), not merely for (vii).

**[REV-C] Ratification status after the WS4 report.** WS4 has reported Partial (§8.1).
Its effect on the ratification list:

- **WS4's two duties — still open, now sharpened.** Both duties the quantale choice
  carries — the WS2-inherited *weak-pullback preservation* and the [REV-B] WS3-pinned
  *weak-law persistence/canonicity* — remain **unclosed**. WS4 built the enriched
  carrier and its identity theory and proved the graded weak law's multiplication
  coherence, but weak-pullback preservation is exactly the unproved Layer C
  (`WQPreservesWeakPullback`, a typed open obligation with its obstruction made
  precise), and the weak law's *canonicity* for the enriched `(F, κ)` is untouched.
  Criterion (iv) therefore stays **Partial**; it is **not** to be reported closed. The
  duties do not transfer — they remain WS4's to discharge — but the obstruction is now
  a named typed hole rather than a hazard.
- **WS7 — collector tuple upgraded to `(F, κ, μ, #Q)` (newly routed).** WS4's QPF
  shape count imposes `#Q ≤ κ` (or a `< κ`-truncation of `Q`) as a Goldilocks-band
  side condition. Vacuous at the finite witness `Łₙ` (`#Łₙ = n+1 < ℵ₀ ≤ κ`), but a
  genuine constraint for an unbounded quantitative quantale (`#Q = 𝔠` forces `κ > 𝔠`
  or a ratified truncation). WS7's collector duty (§6.1 management rule) is upgraded:
  it must ratify the joint tuple `(F, κ, μ, #Q)`, not `(F, κ, μ)`.

**[REV-D] Obligations from the WS5/WS6/WS7 reports.**

- **WS1 §3.7 `κ`-fiat hand-off — discharged (by WS6).** The "no maximal
  everything" duty §3.9/§3.7 [REV-A] routed forward is closed by `ws6_no_maximal`
  (maximality would force the `< κ` support to be the whole carrier, contra
  `κ ≤ #(νPk κ).X`). Recorded as discharged, not merely reassigned.
- **Dynamical non-collapse (convergence) — pinned open, Lemma B.** WS5's
  `replicator_mutator_contracts` is sharpened by WS7 into the analytic inequality
  `(1 − μ)·L_R μ < 1` (existence of a `SelectionLipschitz` witness). Neither is
  inhabited; the Banach consumer (`ws7_attention_fixed_point`) is ready. This is the
  program's one remaining open criterion-(vii) sub-obligation.
- **WS7 collector tuple — ratified at one witness.** `(F, κ, μ, #Q) = (P_κ, κ₀, μ,
  Łₙ)` is exhibited and retro-validated (`ws7_retro_validate`); the `#Q ≤ κ` band
  side-condition [REV-C] is *proved* at the finite witness, not vacuous.

**[REV-E] Obligations closed / corrected by the WS8 report.**

- **WS4 weak-pullback preservation (Layer C) — discharged (WS8-A).**
  `wq_preserves_weak_pullback` inhabits `WQPreservesWeakPullback Q κ` for every `Q`;
  the REV-C "open in neither direction" fork resolves positive. See §8.2 erratum 3.
- **WS3/WS4 weak-law canonicity — discharged for bounded `P_κ` (WS8-B).**
  `ws3_weak_law_canonical` (`∃!`) closes the [REV-B] canonicity pin. Residual: the
  *graded* transport through `W_Q` (step-16) stays open, WS4-local.
- **WS7 universal richness floor `GeneralBranching` — refuted, replaced (WS8-D).**
  `ws7_general_branching_false` proves `¬ GeneralBranching κ`; the load-bearing floor
  for (iv)/(vii) is the `alg`-relative `ws7_iv_branching`. See §8.2 erratum 4.

---

## 7. Success criteria

Success is a single object (or small family) that provably (i) contains no atoms; (ii) identifies each element with its relational unfolding up to bisimulation; (iii) admits reified relations as further elements; (iv) supports bidirectional whole/part constitution via a coherent bialgebra; (v) carries finite attention under which no object fully knows itself, with well-behaved feed/starve dynamics; (vi) has no substantive terminal standpoint; and (vii) is non-degenerate — no structural, standpoint, or dynamical singularity. Partial success with the obstructions to the rest made precise is a valid outcome.

> **[REV-A] These criteria are unchanged.** The bounded reading of §3.9 satisfies
> (i), (ii), (iii) at the carrier level and contributes the ≥2-element part of
> (vii); it does not by itself settle (iv), (v), (vi), or the full non-collapse
> part of (vii). The criteria remain the bar; §3.9 changes only *which object* is
> offered against them, not the bar.

> **[REV-B] Criterion (iv), after WS3, remains the bar — now met in part.** WS3
> contributes to (iv) without closing it: the strict-`λ` route (iv) alludes to via
> §3.4 is proved unavailable (Impossibility proved), and the "coherent bialgebra"
> (iv) requires is delivered as a *weak* bialgebra whose canonicity is pending
> WS4. Read against (iv), this is Partial: the bidirectional content is present on
> the carrier, the coherence is the weak-law coherence, and closure waits on the
> WS4 ratification pinned in §6.1. As with Revision A, this changes only how much
> of (iv) is currently discharged, not what (iv) demands.

> **[REV-G] The criteria are unchanged; three status readings are corrected honestly
> (the external review, `spec/ws9/03-project-review.md`).** *Criterion (i).* The prior "Discharged —
> atomlessness automatic for a terminal coalgebra" was **overreach**: the built carrier
> `νP_κ` contains `bottomState` (empty successor), a relational atom the development even
> uses. `ws10_unlabeled_atomless_collapses` proves the sharp reason — in *unlabeled*
> `νP_κ`, **atomlessness and plurality are jointly unsatisfiable** (any two
> hereditarily-nonempty states are equal), so the groundless sub-universe is the single
> point `Ω`. This is **Impossibility proved** (a §5/§7 success), and it relocates the
> positive (i)-object to the *graded* carrier `νW_Q` (the graded groundless core, routed
> to WS10-B) — grading is thus promoted from (iv)-machinery to (i)-necessity. *Criterion
> (iv).* Coherence and weak-pullback preservation stand Discharged, but `ws3_weak_law_canonical`
> is a unique-*realization* statement, not canonicity over weak distributive laws;
> **canonicity reopens** (WS10-O3), so (iv) is Discharged-minus-canonicity. *Criterion
> (vii).* Its dynamical half is now **characterized** — WS9's necessity/non-settling
> witnesses and WS10's global attractivity/uniqueness bracket the WS8 bands and meet at the
> proved pitchfork `μ⋆ = 1/2` — with the exact frequency-dependent boundary the sole open
> residue. As always, these change *which object* is offered and *how much* is discharged,
> not the bar. And the review's meta-point is recorded: the blind-review layer is
> Claude-reviewing-Claude, a disclosed limitation, not claimed independence.

---

## 8. Open problems and honest risks

The original risk list is retained and expanded. **[REV-A]** adds a per-workstream
audit applying the §3.9 lesson: *does this workstream, like WS1, name a target
whose literal form is unrealizable and thereby introduce a declared substitution
plus a hidden shared dependency?* Each entry gives a provisional outcome class
(per §5) and the methodology note it triggers.

**Standing risks (retained from the original charter).**

- **The Goldilocks band may be narrow or empty.** Non-collapse pushes `F` to be rich; existence and non-totalization push it to be bounded. That these constraints are jointly satisfiable is a conjecture, not a given; finding the exact band is the crux.
- **Finite attention as anti-collapse is heuristic until proven.** The claim that positioned, incomplete self-models keep objects distinct (rather than converging to a common fixed point) must be turned into a theorem, with explicit conditions.
- **Trivialization at the poles.** "Atom = everything" must be a *zero object*, kept strictly apart from the incoherent universal set. Conflating them sinks the program.
- **Distributive-law existence.** Not every `(T, F)` admits a `λ`; the whole/part bialgebra may force compromises on composition or observation. **[REV-B] Now resolved for the built carrier, in the negative: WS3 proved no strict `λ` of the §3.4 form exists on `P_κ` (Impossibility proved). The "compromise on composition" this risk anticipated is the weak distributive law of §3.4's [REV-B] note; the residual is not existence-of-a-law but canonicity-of-the-weak-law, routed to WS4.**
- **Attention need not converge.** Contraction/replicator-mutator conditions guarantee good behavior only under hypotheses; ungrounded self-reference may obstruct them. Non-convergent or chaotic self-attention is a phenomenon to characterize, not assume away. **[REV-G] Now characterized, not assumed away:** WS9 *proves* non-convergence occurs — multistability (`ws9_no_unique_attention`, three fixed points at `μ=3/8`) and a never-settling 2-cycle (`ws9_two_cycle`) — locating the pitchfork `μ⋆ = 1/2`; WS10 proves global convergence above it (`ws10_center_unique_above`). The residual is the exact frequency-dependent boundary, not whether the phenomenon is real.
- **Interpretive gap.** Even a fully successful object leaves open whether it *is* the ROSR world or a faithful model of it — a question to frame, not to overclaim settling.

### 8.1 [REV-A] Per-workstream hazard audit (the §3.9 pattern applied)

**WS1 — Groundless carrier. Outcome: Partial (discharged for its own obligation; residual handed off).**
The WS1-owned obligation — reflexive, relation-only objects exist, unique up to bisimulation — is discharged for the bounded carrier `P_κ`, and more strongly than the WS1 design planned (axiom-free, via `Cofix`, rather than conditional on a transfinite stabilization axiom). The residual is not WS1's to close: "no maximal everything" holds by fiat of `κ`, and the concrete `κ` is unfixed. *Methodology note:* correct the §6 milestone graph to show deliverable 2 shares the `(F, κ)` parameter with deliverables 5 and 6; do not report WS1 as unqualified program completion. *(A secondary, purely operational note: the axiom-freeness claim rests on a static audit of the Lean artifact; a machine-checked `#print axioms` against live Mathlib is still owed before the "unconditional" claim is reported without qualification.)*

**WS2 — Object = relations coinductively. Outcome: at-risk of Partial. Same class of issue as WS1, high likelihood.**
WS2 inherits `P_κ` and the `κ`-choice directly. The bisimulation characterization it must prove relies on the observation functor *preserving weak pullbacks* (the fact WS1's carrier bundled as a needed-but-unformalized lemma). For plain `P_κ` this holds; but if WS2 (or WS4) moves to a **weighted or probabilistic** observation functor to serve §3.5, weak-pullback preservation can *fail*, and then **bisimilarity and behavioral equivalence come apart** — the very "bisimulation = identity" property (criterion ii) would no longer be automatic. *Methodology note:* WS2's framework memo must state which functor it commits to and prove weak-pullback preservation (or explicitly accept the bisimulation/behavioral-equivalence split as a declared substitution, the WS1-style move). This choice binds WS4.

**WS3 — Bidirectional constitution (bialgebra). [REV-B] Outcome: Partial — reported. (Prior provisional class: at-risk of Partial/Failed, highest structural risk.)**
WS3 has now reported, and the outcome resolves to the class §8.1 pre-registered as acceptable. It splits cleanly:

- *The gate — Impossibility proved (a §5/§7 success).* The gating question this entry demanded be answered before building — "does the WS1/WS2 carrier admit the required `T`-algebra structure and a coherent strict `λ`?" — is answered **No, as a theorem**: `ws3_no_distributive_law` proves `IsEmpty (DistLaw κ)`, a full port of the Klin–Salamanca no-go, with no custom axiom. This is exactly the "honest outcome that no `λ` exists," which this entry flagged in advance as Impossibility-proved, not failure.
- *The content — delivered via a declared surrogate, canonicity pending.* Criterion (iv)'s bidirectional constitution is realized by the Egli–Milner *weak* distributive law: a composition operator `alg` with `dest (alg t) = ⋃_{x∈t} dest x`, satisfying the weak-law multiplication coherence, the `T`-unit law on singletons/idempotents, part-reflection (upward) against `dest` (downward), the `Ω` fixed point, and non-triviality. The impossibility is carried *inside* the deliverable (as a `noStrictLaw` field) so the substitution cannot be read as a relabeling.
- *Why Partial and not Discharged.* Criterion (iv) names constitution "via a coherent bialgebra." The strict bialgebra is impossible; the coherent bialgebra that exists is the weak one, and whether the weak law is the *canonical* one for bounded `P_κ` (as opposed to one workable choice among possibly many) is **not** settled. That is the precise obstruction, and it lands the workstream at Partial rather than Discharged.

*Methodology notes (per §5 — corrections and hand-offs, not a reframe):*
1. *Canonical-weak-law ratification → WS4,* newly pinned in §6.1. Criterion (iv) is not to be reported closed until WS4 confirms a well-behaved weak law survives its chosen enriched `(F, κ)` and quantale. This is the WS3-originated ratification duty, additional to the WS2 weak-pullback hazard WS4 already carries.
2. *Registered-signature erratum → §6 [REV-B] note.* The design memo's `pentagon` field was ill-formed; the registered signature is corrected to the proved Egli–Milner form so registered and proved coincide on paper. Surfaced, not silently patched.
3. *`alg`-non-triviality one-step-observability → WS7.* The general branching-≥2 distinguishability behind sharp non-triviality remains WS7's richness-floor obligation; WS3 discharges only the concrete-witness case. Confirmed load-bearing for (iv), not only (vii).
4. *Operational axiom check.* As with WS1, the "no custom axioms beyond Mathlib's standard three" claim rests on a static source audit; a machine-checked `#print axioms ws3_no_distributive_law` and `#print axioms ws3_weak_bialgebra` against live Mathlib is owed before "axiom-free" is reported without qualification. The spots warranting confirmation are the no-go's parity endgame, the `qpfPk` plumbing inherited from WS1, and the `iSup_lt_of_isRegular` bound in `pkJoin` (where `κ.IsRegular` is genuinely consumed — unlike WS2, `hreg` is load-bearing here).

**WS4 — Graded parthood (enriched carrier + graded weak law). [REV-C] Outcome: Partial — reported. (Prior provisional class: at-risk of Partial, medium likelihood.)**
WS4 has now reported, and the outcome resolves to the pre-registered acceptable class. It splits cleanly:

- *The enriched carrier — Discharged (the (i)–(iii) fragment).* WS4 took the WS1-style move this entry named in advance: it declares the `Q`-weighted functor `W_Q` (weightings with `< κ` support) as a distinct object and re-establishes criteria (i)–(iii) for it — `W_Q` is a QPF, `νW_Q = Cofix (W_Q)` is its terminal coalgebra, Lambek holds, and bisimulation = behavioural equivalence = identity (`νWQ_terminal`, `wqLambek`, `wq_bisim_eq`, `wq_bisim_behavioural`), `sorry`/axiom-free. This closes the "or declare the enriched carrier distinct and re-establish (i)–(iii)" branch of the pre-registered methodology note.
- *The graded weak law — multiplication coherence delivered; the quantitative tripwire fired.* The Egli–Milner weak law lifts to the graded setting: `wqAlg` with `wqAlg_pentagon` (the [REV-B]-corrected join-of-destructors form), the `T`-unit law (`wqAlg_unit`), and part-reflection (`wq_reflects_part`). The `[0,1]`/quantale enrichment is instantiated at the concrete **non-idempotent** Łukasiewicz chain `Łₙ` — a `DivisibleQuantale` whose residuation `tensor_section` is proved constructively and *consumed* (`weight_split`), and `ws4_quantitative_witness` certifies non-idempotence for `n ≥ 2`. So §3.5's grading is certified genuinely quantitative, not a frame in disguise — the unification conjecture's quantitative half is no longer hypothetical at the witness.
- *Why Partial and not Discharged.* The design's discharge bar is **Layer C weak-pullback preservation** (`WQRel_le_comp`, step 6 — "the one genuinely new proof"), plus the step-16 Bool-reduction and step-13 join-associativity. These are **not** proved. Layer C is registered as a *typed open obligation* (`WQPreservesWeakPullback`), not asserted, and its obstruction is made precise: the pointwise residuation is discharged (`weight_split`), and what remains is the **global witness assembly** — a single weighted graph whose fibre-sup projections match, where the naive composite weight `wR(x,y) ⊗ wS(y,z)` fails to project unless the middle's outgoing weight is `1` (the non-normalization difficulty). The §8 F6 *Impossibility* theorem (`ws4_no_quantitative_grading`) is equally unproved, so the step-6 fork is open in neither direction. That precise obstruction lands the workstream at Partial rather than Discharged.

*Methodology notes (per §5 — corrections and hand-offs, not a reframe):*
1. *Weak-pullback preservation + canonical-weak-law persistence remain open.* Both WS4-owned ratification duties (the WS2-inherited weak-pullback hazard and the [REV-B] WS3-pinned weak-law persistence, §6.1) stay unclosed for the enriched functor: weak-pullback preservation is exactly the unproved Layer C, and canonicity of the graded weak law is untouched. Criterion (iv) is therefore **not** reported closed; it stands Partial.
2. *Cardinality collector duty → WS7 (newly routed, §6.1).* The QPF shape count couples `#Q` to `κ` (`hQsmall : #Q ≤ κ`), vacuous at the finite `Łₙ` but a genuine band constraint for an unbounded quantitative quantale. WS7's collector tuple is upgraded from `(F, κ, μ)` to `(F, κ, μ, #Q)`.
3. *Naming discipline preserved.* The Lean artifact deliberately names its top bundle `ws4_graded_coherence_Luk`, not `ws4_resolved`, and registers Layer C as a typed hole rather than proving a weaker theorem under the discharge name. This status line honours that: do not let the proved quantitative witness (`Łₙ`) launder the unproved Layer C into looking discharged.
4. *Operational axiom check.* As with WS1/WS3, the "no custom axioms beyond Mathlib's standard three" claim was confirmed by a machine-checked `#print axioms ws4_graded_coherence_Luk` (`[propext, Classical.choice, Quot.sound]`; the `Łₙ` witness and `weight_split` are even choice-free, `[propext, Quot.sound]`).

**WS5 — Finite attention. Outcome: split — incompleteness Discharged/Impossibility-proved-likely; convergence Partial-by-construction.**
The incompleteness-of-self-knowledge result is *robust*: it is a Lawvere-diagonal impossibility that does not depend on the `(F, κ)` choice, and it is the cleanest candidate for an outright success (indeed an **Impossibility proved** in the §5 sense — a sharp negative that the program *wants*). Convergence is the opposite: Banach needs a genuine contraction on a complete metric realization of the (bounded) `νF`, and the replicator-with-mutation operator being contractive is a *hypothesis*, not a generic fact — the standing risk "attention need not converge" is real. *Methodology note:* report WS5 as two separate results with different statuses; do not let the solid incompleteness theorem launder the conditional convergence claim into looking equally settled. State the contraction/μ conditions explicitly as hypotheses.

*[REV-D] Reported: Partial (split), exactly as pre-registered.* Incompleteness came in as the anticipated **Impossibility proved**, and stronger than expected on robustness: `ws5_carrier_incomplete` is a pure Lawvere/Cantor diagonal (`Function.cantor_surjective`) over the `< κ` attention support, so it consumes no carrier-cardinality fact and no functor-specific branching and survives WS4's `W_Q` and any WS7 `(F, κ)` unchanged; `ws5_incomplete_nonvacuous` records the gap is non-vacuous. The plurality/anti-collapse floor is **Discharged** (`ws5_plurality_floor`, `ws5_no_delta`; `hμ : 0 < μ` is load-bearing and stated — `μ = 0` is exactly where collapse re-enters). Convergence is **Partial-conditional**: `ws5_attention_converges` proves the Banach step (with a `[Nonempty M]` honesty correction to the design signature — existence fails on the empty space), and the contraction premise `replicator_mutator_contracts` is a typed obligation with **no inhabiting theorem**. Bundle `ws5_incompleteness_and_floor`, not `ws5_resolved`, so incompleteness cannot launder the open convergence. *Operational axiom check:* `#print axioms ws5_incompleteness_and_floor` owed (incompleteness core expected `Classical`-only); not run for this revision.

**WS6 — No poles, no outside. Outcome: at-risk of Partial. Same class, high; it is the receiving end of WS1's hand-off.**
WS6 must discharge, non-trivially, the "no maximal everything" that WS1 secured only by fiat. But §3.7's zero-object route requires *leaving `Set`* for a category with a zero object — which is **not** the category the bounded final coalgebra of WS1/WS2 lives in. So the poles-coincidence object and the groundless carrier risk being different objects in different categories, and "the same object realizes both" is an unproven bridging claim. *Methodology note:* WS6 must state in which single ambient category *all* of (poles-coincidence, no-everything, groundless carrier) are meant to coexist, and either exhibit it or declare the split. This is a stronger coupling to WS1 than the original §6 (deliverable 5 vs 2) admits.

*[REV-D] Reported: Partial.* The bridging worry above is resolved in the honest direction — **declare the split**, a §5 **Impossibility proved (scoped)**: `ws6_poles_split` shows that a faithful carrier-embedding landing *entirely* in zero objects is contradictory (the load-bearing mechanism is terminality, not null morphisms; `ws6_embedding_nonvacuous` certifies the hypothesis is inhabited). The blanket cross-category claim is left as the named open obligation `ws6_no_faithful_zero_host`, almost certainly false as a blanket (pointed sets host the carrier faithfully) — which is itself the finding: the split holds only against *total* coincidence. "No maximal everything" is **Discharged by `κ`-fiat** (`ws6_no_maximal`), which **discharges WS1's declared §3.7 [REV-A] hand-off**, recorded in §6.1. At REV-D criterion **(vi) was reported Open**: `ws6_standpoint_vacuous` proves the true content — `PositionFree` holds *vacuously for every* observation (via `endo_eq_id`, the terminal carrier admitting only the identity endo-view) — and that vacuity is exactly why the terminal carrier alone furnishes no substantive standpoint. *Honest-signature correction:* the design's `ws6_empty_standpoint` disjunction is false as stated (vacuity would force every predicate constant); `ws6_standpoint_vacuous` is the true realization. Bundle `ws6_split_and_no_maximal`, not `ws6_resolved`. *[REV-E] Criterion (vi) since Discharged by WS8:* `ws6_no_global_observer` (negative — no observer's `< κ` successor set surjects onto the carrier) and `ws6_substantive_standpoints` (positive — distinct bases with distinct observations give genuinely distinct positioned partial views) together supply both halves, replacing the vacuity with content. *Operational axiom check:* `#print axioms ws6_split_and_no_maximal` (and the two WS8 (vi) theorems) owed; not run for this revision.

**WS7 — Non-collapse. Outcome: at-risk; the central conjecture may yield Impossibility-proved. Highest hand-off load.**
WS7 is the designated collector: it inherits `κ` from WS1, the functor/weights from WS2/WS4, and the mutation floor `μ` from WS5, and must show a *single* concrete `(F, κ, μ)` sits in the Goldilocks band. The standing risk that the band "may be narrow or empty" means the honest outcome could be that no such choice exists — an **Impossibility proved** (a program-level success per §7, and arguably the most informative one), *not* a failure. The richness floor (branching ≥ 2) versus boundedness (`< κ`) is plausibly jointly satisfiable for finite/`κ`-powerset, but the *dynamical* non-collapse (μ-floor keeps attention off the simplex vertices) is a separate analytic condition that must be proved, not assumed. *Methodology note:* WS7's deliverable must be phrased as "locate the band **or** prove it empty," with both treated as valid terminal outcomes, and it must retro-validate every upstream "for `κ` infinite regular" theorem against its final concrete choice. **[REV-B] WS3 confirms one of WS7's inherited duties is now (iv)-blocking, not merely (vii)-blocking: the branching-≥2 richness floor is what WS3's sharp non-triviality relies on, so WS7's richness-floor result feeds bidirectional constitution as well as non-collapse.**

*[REV-D] Reported: Partial (collector).* The "locate the band **or** prove it empty" deliverable came in on the *locate* side, at one witness. The static structural band is **Discharged** in witness form (`ws7_static_band`: ≥2 distinct states, no maximal state, weak-pullback preservation). The collector spine is **Discharged at one concrete tuple** `(κ₀, μ, Łₙ)` (`ws7_retro_validate`), and the WS4-routed `#Q ≤ κ` side-condition is *proved* at the finite witness (`luk_card_le`), not left vacuous — so a single `(F, κ, μ, #Q)` is exhibited against which the WS2 characterization, no-maximal, the WS6 split, and the WS4 graded-law coherence all simultaneously hold, retro-validating the upstream "for `κ` infinite regular" theorems at that choice. Two collector duties stayed **open and typed**: the *universal* richness floor `GeneralBranching` (`RichnessGeneralStatus.open_iv_blocking`, never derived from the ≥2-state witness), and the **dynamical axis, `deferred` to "Lemma B"** — WS7 sharpens WS5's opaque contraction premise into the analytic inequality `(1 − μ)·L_R μ < 1` (existence of a `SelectionLipschitz` witness meeting it), proving the contraction and fixed point *given* it (`ws7_mutation_contracts`, `ws7_attention_fixed_point`) but not the inequality. WS7 fixes its own scope (`CarrierScope.set_cofix_only`): §3.7's no-maximal face and (vii), **not** the zero-object face or criterion (vi). Bundle `ws7_band_and_retro`, not `ws7_resolved`. *[REV-E] `GeneralBranching` refuted and replaced by WS8:* `ws7_general_branching_false` proves `¬ GeneralBranching κ` (the empty carrier state has out-degree 0), so the universal floor is provably unachievable; the honest load-bearing floor for (iv)/(vii) is the `alg`-relative `ws7_iv_branching` (out-degree ≥ 2 from two members with distinct successor *points*, the D2 hypothesis corrected — see §8.2 erratum 4). The dynamical axis remains `deferred` (Lemma B), the program's one open criterion-(vii) sub-obligation. *Operational axiom check:* `#print axioms ws7_band_and_retro` (and the WS8 `ws7_*` theorems) owed; not run for this revision.

### 8.2 [REV-A] The one-line summary

The WS1 issue is not a WS1 quirk. The charter repeatedly names, in its
spirit-level sections, targets whose *literal* form its own feasibility notes
show to be unrealizable (full-powerset carrier, `Set`-level no-everything,
unconditional convergence, an all-satisfying single `(T, F)`), and each such
naming forces a declared substitution plus a dependency on a shared parameter.
The correct program-level discipline is the one WS1 modeled: **substitute openly,
recover the canonical content inside the surrogate where possible, state the
residual obstruction precisely, and route it to the workstream that owns it —
never relabel the shortfall as the goal.**

> **[REV-B] WS3 is the pattern's second confirmed instance, and its cleanest.**
> WS3 named a strict distributive law (§3.4) whose literal form its own gate
> proved impossible, substituted the weak law openly, recovered criterion (iv)'s
> bidirectional content inside the surrogate, carried the impossibility *inside*
> the deliverable so it cannot be relabeled, and routed the one residual
> (weak-law canonicity) to WS4. This is §8.2 discipline executed end to end — the
> impossibility half is a positive finding (composition of relations-as-objects is
> inherently non-strict), not a shortfall dressed up as a goal.

> **[REV-E] WS8 executes the same discipline in reverse — surfacing two design
> targets that were false as literally stated, and proving the honest true form.**
> *Erratum 3 — WS4 design A5 target (weak-pullback preservation).* The WS4 design
> registered `¬ WQPreservesWeakPullback` (A5) as the anticipated Impossibility, on
> the reasoning that non-idempotent `⊗`-weighting blocks witness reassembly. But
> WS4's *formalized* `WQRel` is the sup-based Barr lifting with no `⊗`-coupling of
> leg weights; A5's obstruction never arises for it, and WS8 proves the positive
> `wq_preserves_weak_pullback` instead. The impossibility was aimed at a
> `⊗`-weighted lifting *outside* the formalization; surfaced here, not silently
> dropped. The genuine `⊗`-weighted question is a *different* open problem, not this
> criterion-(iv) obligation, and its resolution here is what moves (iv) to
> Discharged. *Erratum 4 — WS7 D2 branching hypothesis.* The design's D2 hypothesis
> `str x₁ ≠ str x₂` is insufficient: a singleton-successor member and the empty
> state have distinct successor *sets* but their Egli–Milner union has out-degree 1.
> The true, proved form (`ws7_iv_branching`) hypothesizes two members with distinct
> successor *points*, exactly what WS3's `alg_nontrivial` supplies. Both are §8.2
> corrections — an over-shooting target replaced by the honest theorem — not
> weakenings of any criterion.

---

## 9. Positioning

Philosophically: Ladyman & Ross (*Every Thing Must Go*, 2007), French (*The Structure of the World*, 2014), the "relations without relata" objection, and the denial of a view from nowhere (Nagel). Formally: Aczel's non-well-founded set theory; universal coalgebra (Rutten, Jacobs); Turi–Plotkin bialgebraic semantics; Lawvere's fixed-point theorem and its diagonal corollaries; Lawvere-enriched categories; replicator dynamics. The distinctive bet: these usually separate literatures, taken together, are the correct constitution for a groundless, perspective-bearing, relation-first ontology — and where they resist, the resistance is itself metaphysically informative.

*Working draft. Revision A adds the §3.9 bounded-carrier reconciliation, the §6.1 shared-parameter dependency structure, and the §8.1 per-workstream hazard audit; §§0–2, 4 (workstream list bodies), 5 (methodology body), 7 (criteria), and 9 are otherwise retained from the original. Revision B records the WS3 report: the §8.1 WS3 status (now Partial, reported), the §6.1 WS4 canonical-weak-law ratification obligation, the §6 `pentagon` signature erratum, and the §8.1 operational axiom-check note; it adds inline [REV-B] pointers at §§3.4, 6, 7, 8, 8.2 and leaves all §§0–7 target/criteria text unaltered. Revision C records the WS4 report: the §4/§8.1 WS4 status (now Partial, reported — enriched carrier and identity theory discharged, graded multiplication coherence proved at the non-idempotent witness `Łₙ`, Layer C left a typed open obligation), the §6.1 [REV-C] ratification status (WS4's two duties open, the `(F, κ, μ, #Q)` cardinality duty routed to WS7), with inline [REV-C] pointers and no §§0–7 change. Revision D records the WS5/WS6/WS7 reports (all Partial): WS5 incompleteness (Impossibility-proved, `(F, κ)`-robust) + plurality floor (Discharged) + conditional convergence; WS6 poles-split (Impossibility-proved, scoped) + no-maximal (Discharged, closing WS1's §3.7 hand-off) + (vi) Open; WS7 static band + concrete-tuple retro-validation (Discharged) with `GeneralBranching` and the dynamical Lemma B held open — updating the §4 and §8.1 WS5/WS6/WS7 status lines and the §6.1 ratification list. Revision E records WS8's hole-filling: weak-pullback preservation (Layer C, WS8-A) and weak-law canonicity (WS8-B) discharged — moving criterion (iv) to Discharged for the bounded carrier — criterion (vi) discharged (WS8-E), and the WS7 universal richness floor refuted and replaced by its honest `alg`-relative form (WS8-D), with two §8.2 errata; inline [REV-D]/[REV-E] pointers at §§4, 6.1, 8.1, 8.2, and no §§0–7 target/criteria change. After Revision E, criteria (i)–(iv) and (vi) are discharged for the bounded carrier and (vii)'s structural half is met; the single remaining open criterion is (vii)'s dynamical half — convergence of attention (Lemma B) — and the standing operational obligation is the machine-checked `#print axioms` pass, not performed for these revisions (no Lean/Mathlib environment at drafting time). To be revised if further workstreams report or the open obligations close.*
