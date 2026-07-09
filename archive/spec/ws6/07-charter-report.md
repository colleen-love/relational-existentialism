# WS6 mapped to the charter

## What the charter assigns WS6

Reading §4 (WS6 line), §3.7, §6 deliverable 5, and the §8.1 audit together, WS6 owns:

- the poles-coincidence facet (§3.7 bullet 1 — zero object / "atom = everything" kept apart from the incoherent universal set, the §8 standing risk);
- the receiving end of WS1's "no maximal everything" hand-off (§3.7 bullet 2, secured only by `κ`-fiat under the bounded reading, §3.9 / §8.1);
- and — centrally — criterion **(vi)**, "no substantive terminal standpoint" (§3.7 bullet 3, "no view from nowhere"; §7 (vi)).

The §8.1 audit pre-registers the acceptable shape sharply: WS6 must "state in which single ambient category *all* of (poles-coincidence, no-everything, groundless carrier) are meant to coexist, and either exhibit it or declare the split." Two authorized terminal shapes: exhibit the single host, or declare the split.

## Where the verified artifact lands against each

The formalization (ws6.lean) delivers, `sorry`-free and axiom-free modulo a live `#print axioms`:

`ws6_poles_split` — a genuine impossibility on the correct mechanism (terminality via `eq_of_tgt`, not null morphisms), certified non-vacuous by `ws6_embedding_nonvacuous`. This takes the charter's **"declare the split"** option and proves the "atom = everything" conflation fatal. It is scoped to total coincidence (`coincide`), with the broader cross-category claim held as the uninhabited `ws6_no_faithful_zero_host`.

`ws6_no_maximal` — discharges WS1's `κ`-fiat hand-off exactly as §3.9 / §8.1 route it. Not a new obligation, and not `(F,κ)`-independent (inherited).

`ws6_standpoint_vacuous` — the honest residual for criterion (vi). The design's registered F3 signature (`ws6_empty_standpoint`, the disjunction) is *false* on the ≥2-element carrier, and the artifact refuses it, proving the true vacuity statement instead. This means **criterion (vi) — the core WS6 criterion — is not delivered.** The terminal carrier admits only the identity endo-view (`endo_eq_id`), so there is no substantive standpoint to constrain; the content of (vi) ("local sections, no global section," §3.7 bullet 3) requires non-terminal spans the terminal carrier does not furnish.

`ws6_relative_bottom` — the bottom pole, Partial-by-construction; the "everything" pole is the split.

## Workstream-level outcome classification

**WS6 overall: Partial**, with the obstruction to the rest made precise — matching (indeed slightly under-running) the class §8.1 pre-registered.

Breaking it into the charter's §5 vocabulary:

The poles-coincidence facet is an **Impossibility proved** (scoped) — a §5/§7 success. It resolves the §8 "atom = everything" standing risk as a declared split, which is one of the two shapes §8.1 authorized. The scoping to total coincidence is honest: the blanket cross-category statement is stated, flagged as almost certainly false (pointed sets host the carrier faithfully), and left uninhabited rather than claimed.

The WS1 hand-off ("no maximal everything") is **Discharged**, by `κ`-fiat — but this is discharge of WS1's declared debt under §3.9, not an independent proof of §3.7 bullet 2, and it inherits the `(F,κ)` coupling routed to WS7.

Criterion (vi) is **Failed against its registered target** / equivalently **Open**: the workstream's own core criterion is not achieved, and the reason is documented — the registered F3 proposition was mathematically defective (refutable), and the true statement is vacuous. This is the dominant residual and is what pulls the whole workstream to Partial rather than to a clean split-success.

So WS6 does **not** reach Discharged (its core criterion (vi) is not met), and it is not a pure Impossibility-proved success either (the impossibility resolves only the poles-coincidence hazard, not (vi)). It sits at **Partial**: one facet impossibility-proved, one hand-off discharged, one facet Partial-by-construction, and the central criterion Open with a precisely routed obstruction.

## Methodology notes (triggered by the Partial — corrections and hand-offs, not a reframe)

Three notes, in §8.2 discipline:

**1. Criterion (vi) is Open; route it, do not launder it.** The substantive "no view from nowhere" content requires a **site/sheaf layer over the category of `P_κ`-coalgebras** — local sections indexed by non-terminal objects, with the claim to prove being *no global section over the terminal object*. This is a WS6 residual coupling to WS2's coalgebra-category choice and to WS7's `(F,κ)` ratification. It must be reported Open, with this obstruction attached; the assembly `WS6NoPoles` correctly omits any `standpoint_substantive` field and the top theorem is named `ws6_split_and_no_maximal`, not `ws6_resolved`, so the discipline is already structurally enforced — preserve that in the status line. This is the WS4 `ws4_graded_coherence_Luk` / WS5 `ws5_incompleteness_and_floor` naming discipline transplanted, and it should be honoured: the genuine F4 impossibility must not be read up into (vi) closure.

**2. Registered-signature erratum → surface it, as WS3's `pentagon` was.** The WS6 design memo's `ws6_empty_standpoint` disjunction is false-as-stated, exactly parallel to the WS3 `pentagon` transcription artifact and the WS5 `Nonempty` omission. The registered signature should be corrected on paper to the proved `ws6_standpoint_vacuous`, surfaced here rather than silently patched in-artifact (§8.2). This is a correction of the memo, not a weakening of (vi) — (vi) was never carried by the disjunction's content; the disjunction merely over-shot vacuity into an untruth.

**3. The `κ`-fiat coupling and the cross-category bridge → WS7 collector.** `ws6_no_maximal`'s `hcard` is inherited `(F,κ)`-coupling, part of the pre-existing WS1 obligation, and belongs in WS7's `(F, κ, μ, #Q)` ratification. Separately, `ws6_no_faithful_zero_host` is a precise, uninhabited object handed forward for WS7 to ratify or refute against the final `(F,κ)` — the honest cross-category finding is that §3.7's "different objects in different categories" is confirmed *as a split*, not as blanket non-embeddability.

The §8.1 pre-registered class for WS6 was "at-risk of Partial, high; the receiving end of WS1's hand-off." The reported outcome confirms that prediction: **Partial**, split cleanly, with the poles hazard resolved as a scoped impossibility, the WS1 debt discharged by fiat, and the workstream's core criterion (vi) Open with its obstruction made mathematically precise and routed — no shortfall relabeled as the goal.
