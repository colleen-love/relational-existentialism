# Program Review 3-1 — closure ledger

Per-finding dispositions under the protocol's series-repair phase. Repairs are additive theorems and prose corrections; no landed proof was weakened. All five series rebuild green after repair, axiom-clean, gate green.

## Serious

- **P3R1-S1 (3.3, the winding is word-level) — relabeled, with the obstruction recorded as theorems.** The reviewer's facts are now in the artifact: `transport_swap` (the map is symmetric in its last two arguments), `stepSign_swap` (the two presentations carry opposite signs), and `ws2_winding_orientation` (the flipped word runs identically from every state with winding `-1` against `1`). The ws2 header and docstrings are rewritten: the phase lives on oriented words, the orientation is a declared convention antisymmetric under reversal (as a loop's orientation is data its image does not carry), and every "path-dependent" claim reads word-dependent. The co-terminality content survives honestly: the routed histories' windings differ by more than a sign, which no presentation flip accounts for. The canonical-orientation branch (deriving the sign from the built charge flux) is left as the standing forward-note for any successor series; no theorem currently delivers it.
- **P3R1-S2 (3.1, the bet was closed before the series ran) — fixed in part, relabeled in part.** Fixed: step zero's macro-non-autonomy fact is landed as `ws3_macro_not_autonomous` (two summary-identical states diverge in summary under one move — the summary level supports no autonomous dynamics), the series' genuinely dynamical theorem. Relabeled: the ws3 header now scopes the series to observational non-invertibility over a reversible microdynamics, states that no theorem distinguishes past from future, and carries the closed-arms disclosure (`transparent` closed by counting, `opaque` by 3.0); `ws3_observation_always_lossy`'s docstring now states its equivalence to the static lossiness. The status ledger records that the arms were closed before the series was built.
- **P3R1-S3 (3.4, the law is one unfolding deep) — fixed in part, relabeled in part.** Fixed: the strict-contraction theorem `ws4_flux_contracts` (distance at least two before, at most one after, for a non-attended non-self target) — the law's non-definitional content, previously unclaimed — with the supporting `mem_ball_one_iff`. Relabeled: "the shape of gravity" is struck; the ws4 header and docstrings now present a per-event law linking two readings of one attention event, coupled by common cause, with no field equation stated or claimed and the absent grain-driven law named as absent.

## Real

- **P3R1-R1 (3.2 double-count)** — disclosed here and in the status; the flag vector is left as landed (the orbit theorem and its contrapositive remain two flags; the tying theorem makes the dependence visible in its own hypotheses). The genuinely new content is `ws3_orbits_are_capacity`, as the review says.
- **P3R1-R2 (pre-registration without risk; the skipped gate)** — process finding, standing. The status already disclosed the gate merge; this review is the gate's discharge, arriving late by the owner's direction. For any future arc: outlines are to state, per pre-registered arm, why the arm is live at outline time — a one-line obligation added to the practice by this closure.
- **P3R1-R3 (phase group not delivered)** — fixed where it was wrong (the status table now reads "a classified ±1 phase," not "a genuine phase group"); the charter's target stands as unmet ambition, recorded rather than rewritten. The missing tie from the winding to `incr`/charge is the same forward-note as P3R1-S1's canonical-orientation branch.
- **P3R1-R4 (3.1 prose)** — fixed: "is exactly" is now "includes … an instance, not a characterization"; the single-move scope is stated in the docstring.

## Cosmetic

- **(a)** fixed: 3.0's `nondegen` tying hypothesis now carries the full two-sided wall proposition. **(b)** softened in the status: the cone transfer is an expectation, no artifact exists. **(c)** stands as disclosed. **(d, e)** noted; no change.

## Verification after closure

All five series and their axiom checks rebuild green; every headline on the standard three axioms or fewer, every `ws5_verdict_eq` on none; gate green; hygiene greps clean. The program verdict after repair: the core stands as **flowing / observational-arrow / ledger**, the post-gate pair as **word-level phase (sign forced at ±1 scope) / per-event flux law with strict contraction** — each now named at the strength the Lean record supports.
