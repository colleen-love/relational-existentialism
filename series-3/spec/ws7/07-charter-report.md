Now I can map the verified WS7 artifact back to the charter's WS7 obligation and success criteria, using the §5 outcome vocabulary.

## What the charter asks of WS7

WS7's obligation is triple. From §4: "Establish the richness floor on `F` and the plurality floor on attention; prove `νF` is non-degenerate and the dynamics avoid delta collapse; locate the Goldilocks band explicitly." From §6.1 and [REV-C], WS7 is additionally the **designated collector**: it must "confirm a single concrete `(F, κ, μ, #Q)` discharges the richness floor, the plurality floor, and the deferred no-everything obligation, and retro-validate that WS1/WS2/WS4's 'for κ infinite regular' theorems survive that specific choice." And §8.1's WS7 audit pre-registers the crucial framing: the deliverable must be phrased as "locate the band **or** prove it empty," with dynamical non-collapse being "a separate analytic condition that must be proved, not assumed."

So WS7 has, in effect, four distinct sub-obligations, and the charter has already told us how to grade each.

## Sub-obligation by sub-obligation

**Static non-collapse — the richness and no-maximal floors.** `ws7_static_band` proves the ≥2-branching witness, no-maximal-element, and weak-pullback preservation, all from ratified upstream theorems. This is the (vii) structural floor and the §3.7 no-maximal face. **Discharged** — but only in the *witness* form. This matters because of the next item.

**The (iv)-blocking richness floor.** [REV-B]'s §6.1 hand-off and §8.1 WS7 note make this precise: WS3's sharp non-triviality depends on general branching-≥2 distinguishability, so this floor "is now (iv)-blocking, not merely (vii)-blocking." The artifact holds `GeneralBranching` open as `RichnessGeneralStatus.open_iv_blocking`, with no constructor deriving it from the witness. This is **not discharged**, and correctly so — it is a named, typed open obligation. Because it is (iv)-blocking, criterion (iv) cannot be closed from the WS7 side either.

**The collector / retro-validation duty.** `ws7_retro_validate` ratifies the `(F, κ, μ, #Q)` tuple at one concrete `(κ₀, μ, Łₙ)`, with WS2's characterization, no-maximal, WS6's split, and WS4's graded coherence all surviving, and `#Q ≤ κ₀` proved via `luk_card_le`. This substantially meets the [REV-C] collector upgrade. The one gap I found in the artifact verification — that `#Q` is *carried and re-exported* rather than *consumed* by the coherence, because ws4's actual `GradedWeakLawCoherence` never exposed the hook — is a signature drift below the charter level. At the charter's granularity, the collector duty asks WS7 to *ratify that the tuple discharges the upstream theorems at one concrete choice*, and that is done. So the collector duty is **Discharged at the charter's bar**, with a methodology note owed on the `#Q`-consumption drift.

**Dynamical non-collapse — the Goldilocks band and convergence.** This is the crux the charter flagged as WS7's highest risk. The artifact proves the full Banach scaffold — invariance (B0), the Lipschitz bound, the contraction lemma, and the fixed-point theorem via `ws5_attention_converges` — but the existence of a `SelectionLipschitz` with `(1−μ)·L_R μ < 1` (Lemma B, the actual contraction) has no inhabitant. The `DynamicalStatus` for the assembly is `deferred`. This is precisely the charter's standing risk "attention need not converge," and §8.1 explicitly required this analytic condition "be proved, not assumed." It is neither proved nor proved-empty. So dynamical non-collapse is **not discharged**, and the band is **neither located nor proved empty** — it is deferred.

## Workstream-level classification

**Outcome: Partial**, with the obstruction to the rest made precise.

This is the honest classification and it matches the artifact's own top-line and the charter's pre-registration. The reasoning:

WS7 is *not* Discharged, because the workstream obligation as written requires locating the Goldilocks band (or proving it empty), and the dynamical axis — the one genuinely analytic component — rests on an uninhabited contraction premise. The band is not located.

WS7 is *not* Impossibility-proved, which would also have been a §5/§7 success. The charter explicitly held this open as a legitimate terminal outcome: "the honest outcome could be that no such choice exists." But the artifact does not prove the band empty either — `DynamicalStatus.impossible` is a nameable shape that is not inhabited, and `ws4_no_quantitative_grading`-style negative results are absent. The fork is open in neither direction, so this is not the sharp-negative success.

WS7 is *not* Failed, because the obstruction is made mathematically precise rather than merely conceded. Lemma B is isolated to a single typed, uninhabited premise; the entire Banach reduction around it is proved, so what remains is exactly the analytic contraction fact and nothing more. The (iv)-blocking richness floor and the zero-object/(vi) face are likewise carried as explicit typed status fields, not silently dropped. This is the signature of Partial, not Failed.

So WS7 lands at **Partial** on three fronts that the charter itself anticipated: the dynamical band (deferred to Lemma B), the (iv)-blocking general-branching floor (open, and blocking criterion (iv) from the WS7 side), and the zero-object/(vi) face (explicitly out of scope, owned by WS6). The static band and the collector retro-validation are the discharged core within that Partial.

## Methodology notes triggered (per §5 — corrections and hand-offs, not a reframe)

First, the dynamical non-collapse claim must be reported as *conditional*, exactly as WS5's convergence was. The artifact's naming discipline enforces this structurally — the bundle is `ws7_band_and_retro`, not `ws7_resolved`, and `dynamics := deferred` — so the discharged static band cannot launder the open convergence. This is the WS5 discipline transplanted correctly. The residual is a genuine analytic obligation (the replicator-mutator's contraction on the floored simplex), and it should be stated with its `(1−μ)·L_R μ < 1` condition explicit, not assumed away.

Second, criterion (iv) still cannot be reported closed, and now for a WS7-side reason in addition to the WS4-side one. [REV-B] pinned that the branching-≥2 floor is (iv)-blocking; the artifact confirms WS7 does not discharge `GeneralBranching`. So criterion (iv)'s closure waits on *both* WS4's canonical-weak-law/Layer-C duties *and* WS7's general-branching floor. This should be recorded on the §6.1 ratification list as a live WS7-owned (iv)-blocking item, not folded into the discharged static band.

Third, a new note the charter revisions have not yet recorded: the `#Q ≤ κ` collector side-condition is, in the actual Lean, a *carried* premise rather than one *consumed* by WS4's graded coherence, because ws4's `GradedWeakLawCoherence` was never given the `hQsmall` hook the [REV-C] routing assumed. The charter-level collector duty ("ratify the joint tuple") is met, but fully discharging the [REV-C] intent — that `#Q ≤ κ` be load-bearing inside the coherence, not merely visible alongside it — remains a small owed item routed jointly to WS4 (expose the hook) and WS7 (feed rather than re-export it). This is a §8.2-style "surface the drift, do not silently patch" note, consistent with the discipline the charter applied to the WS3 `pentagon` erratum.

Fourth, the ambient-category scope: the artifact records `CarrierScope.set_cofix_only`, correctly declining to speak to the zero-object face or criterion (vi). This aligns with §8.1's WS6 audit (the poles-coincidence object may live in a different category than the Set/Cofix carrier) and keeps that coupling owned by WS6. No reframe — just an honest scope boundary that prevents the collector's retro-validation from being over-read as ratifying a single-category coincidence the charter lists as open.

None of these is a redefinition of WS7's target. The bar remains "locate the band or prove it empty"; the artifact reaches neither yet, isolates the single analytic obstruction that stands between the current state and the positive resolution, and routes the two collector-level residuals to their owners. That is Partial executed to the §8.2 standard.
