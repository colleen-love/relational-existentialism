I'll verify the WS7 artifact (document 8) against its design (document 1), checking whether it's `sorry`-free and whether it proves the registered signatures or weakened variants.

## `sorry`-freedom

The file contains no `sorry` tokens. Every declaration terminates in a genuine proof term or tactic block. The header's axiom claim (`propext`/`Classical.choice`/`Quot.sound` only) is consistent with the imports (ws1–ws6 are all axiom-free by their own accounting) and nothing in ws7 introduces a custom `axiom`. So: **`sorry`-free and axiom-free**, as claimed. The substantive question is whether the *signatures proved* match the *registered* ones.

## Signature-by-signature check against the design

**C1 static band (`ws7_static_band`).** Matches design §3 verbatim: `RichnessWitness ∧ no-maximal ∧ weak-pullback`, assembled from `ws2_nondegenerate`, `ws6_no_maximal`, `ws2_weak_pullback`. The types line up with the upstream deliverables. **Discharged, registered form.**

**C5 retro-validation (`ws7_retro_validate`).** Here is the first real divergence, and the file admits it in its honesty note (1). The design's C5 (fix 4) requires the `#Q` premise to be *consumed by the coherence*: `GradedWeakLawCoherence (Luk n) κ₀ hreg hQsmall` — coherence "now consumes hQsmall." The actual ws4 `GradedWeakLawCoherence`/`ws4_graded_law_coherence` do **not** take `hQsmall` (confirm in document 5: the structure's parameters are `(Q) [GoodQuantale Q] (κ) (hreg)` with no `#Q` field). So ws7 threads `hQsmall` as a recorded premise and re-exports it as a trailing conjunct `∧ Cardinal.mk (Luk n) ≤ κ₀` rather than feeding it into coherence.

This is weaker than the registered signature in a specific, honest way: the design wanted `#Q ≤ κ` to be load-bearing inside the coherence proof; here it is load-bearing nowhere (it is proved via `luk_card_le` and then merely carried). The "no longer silent on `#Q`" goal is met at the level of *typed visibility* but not at the level of *consumption*. The `example` discharge the design shows (proving `hQsmall` for `Łₙ`) is present as `luk_card_le`, correctly proved. So C5 is **Partial against the registered signature**: the tuple is validated and `#Q` is a typed, discharged premise, but the coupling into coherence that the design registered is absent because the upstream API never exposed it.

**Richness split (fix 5).** `RichnessWitness` is discharged (`ws2_nondegenerate`); `GeneralBranching` is defined and held open via `RichnessGeneralStatus.open_iv_blocking`, with no constructor bridging witness→general. This matches the design exactly. One caveat worth flagging: the design's `GeneralBranching` uses `¬ Bisim x y` (behavioural distinguishability); ws7 replaces this with `x ≠ y` (honesty note 3), justified because "on the terminal carrier bisimilarity is identity." That justification is sound (it's `ws2_bisim_behavioural`), so the substitution is faithful, not a weakening. Since the field is held *open* either way, nothing rests on it. **Correctly held open, as registered.**

**Ambient-category scope (fix 6).** `CarrierScope.set_cofix_only` with `SingleCategoryBridge := ws6_no_faithful_zero_host` for the reserved `unified_category` case. Matches the design. **Registered form.**

**Dynamical axis (C3).** The design's `DynamicalStatus` is a four-constructor inductive; ws7 adds a fifth, `deferred`, and the assembly uses `deferred`. This is honest but is a *change* to the registered type — the design listed four shapes (`discharged`/`impossible`/`partial` interval-or-disconnected); ws7 has `discharged`/`impossible`/`partial_band`/`deferred`. The Banach machinery (`mutationStep_maps_into` B0, `mutation_lipschitz` A, `ws7_mutation_contracts`, `ws7_attention_fixed_point`) is all genuinely proved, resting on `ws5_attention_converges`. Lemma B — existence of a `SelectionLipschitz` with `(1−μ)·L_R μ < 1` — has no inhabitant, exactly as registered as open. **The convergence theorem is discharged conditionally; the class is `deferred`.**

**Assembly (`ws7_band_and_retro`).** Named per §8.2 discipline (not `ws7_resolved`), carries all status fields as typed values. The bundle is genuinely inhabited. Note the structure gained a third index `(A : Set ℝ)` versus the design's `WS7NonCollapse κ μ` — a faithful adaptation (the band has to live somewhere), not a strengthening.

## Two things to check that the prose glosses

First, in `ws7_band_and_retro` the `dynamics` field is set to `DynamicalStatus.deferred` unconditionally, and `μ` enters only through `plurality := hμ`. Nothing in the assembly ever calls `ws7_attention_fixed_point` — the dynamical spine section is proved but *not wired into the deliverable*. That is consistent with "class deferred," but it means the bundle's `dynamics` field would typecheck with `deferred` regardless of whether any dynamical lemma were proved. The dynamical proofs are real, but the deliverable does not depend on them. This is honest given the `deferred` label, though it slightly undercuts the claim that the section is load-bearing for the bundle.

Second, `ws7_retro_validate` and `ws7_band_and_retro` fix `κ₀ : Cardinal.{0}` (honesty note 4), because `Luk n : Type 0`. The design's C5 was stated over `κ₀ : Cardinal.{u}`. This is a universe restriction of the registered signature — minor, forced by the concrete witness, and disclosed.

## Outcome classification

**Partial**, with the obstruction made precise — and this is the *correct and honestly-labeled* outcome, matching the artifact's own top-line ("class deferred to Lemma B").

The precise accounting:

The **static band (C1)** is Discharged at its registered signature. The **retro-validation (C5)** is Discharged as a proposition but against a *weakened* signature relative to the design: `#Q ≤ κ` is a carried-and-re-exported premise, not a premise consumed by the coherence, because ws4's actual `GradedWeakLawCoherence` never exposed the `hQsmall` hook the design assumed. This is a genuine gap between registered and proved signature, correctly surfaced in honesty note (1) rather than hidden. The **richness-general floor (iv-blocking)** and the **zero-object/(vi) face** are held open as typed status fields, exactly as registered — these are not failures but registered open obligations. The **dynamical axis** rests on the one genuinely open analytic obligation (Lemma B: the contraction premise), with the Banach reduction fully proved around it.

So no field is laundered, the naming discipline holds, and the single mathematical obstruction (Lemma B's contraction) is isolated to a typed, uninhabited premise. The one thing that keeps this from being a clean "Discharged for the collector duties" is the C5 signature drift on `#Q`: the design registered `#Q` as *consumed*, the artifact delivers it as *carried*. That is a methodology-note item, not a reframe.

**Methodology note (triggered by the C5 signature drift):** the design v3's fix 4 was specified against an idealized upstream in which `ws4_graded_law_coherence` threads `hQsmall`. The actual ws4 does not. The correct response — which the artifact takes — is to carry `hQsmall` as a typed, proved, re-exported premise and *say so*, rather than to silently drop it or to rename the coherence as if it consumed the shape count. The residual obligation this leaves is real: to fully discharge C5's registered signature, ws4's `GradedWeakLawCoherence` would need to actually take and use `hQsmall` (e.g. in the QPF shape-count bound for `WQP`), and ws7 would then feed rather than re-export it. Until then, "retro-validated at `κ₀`" provably includes `#Q ≤ κ` as a *stated* premise, which is the design's anti-over-read goal, but not as a *consumed* one, which was its stronger registered claim.
