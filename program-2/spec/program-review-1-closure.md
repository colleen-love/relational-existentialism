# Program Review 2-1 — Closure Ledger

**What this is.** The per-finding closure record for `program-review-1.md`, under the series protocol §0.2a binary: each SERIOUS finding closes **Fixed** (the strengthened target built, the theorem named) or **Relabeled** (the obstruction recorded — here, recorded *as a theorem* wherever one is stateable — and the claim re-scoped). The Fixed branches live in the new review-repairs library **`PR2R1`** (`program-2/review/formal/PR2R1.lean`), registered in `lake/lakefile.toml` and `scripts/gate.sh`, built green and axiom-clean (all 25 headlines on Mathlib's standard three or fewer, verified by `PR2R1.AxiomCheck`). The prose corrections live in `README.md`; the audit-sweep edits live in each series' `ws5.lean`. Nothing in any series' proof-bearing code was weakened; every edit is additive or prose.

---

## SERIOUS findings

### PR2-S1 (total-bisimilarity degeneracy) — **Fixed** (the two-sided wall built), with a disclosed residue.

Built: `PR2R1.pr2s1_two_sided_wall` on the new carrier `V` (a leaf and two self-loops):

- `wall_collapse_not_total` — plain bisimilarity is NOT total: no bisimulation relates a loop to the leaf. The first Program 2 witness whose plain behavior is not fully collapsed.
- `wall_label_recoverable` — a **non-constant label that IS recoverable** (the leaf/loop label): every plain bisimulation already respects it. The recoverable side of the Import Theorem boundary is inhabited by a genuine distinction for the first time in the program.
- `wall_label_import` — on the SAME carrier, a non-constant label across the plain-bisimilar loop pair is NOT recoverable. The import test now provably **discriminates**: alignment with plain structure decides recoverability.

**Residue (disclosed, Relabeled):** the original series' payoffs still live on their all-SHNE carriers, where the finding's analysis stands — on those witnesses every non-constant label is an import and the wall is one-sided. The two-sided wall shows the *framework* can discriminate; it does not retroactively make the landed payoffs discriminating. Re-proving each series' payoff on a non-degenerate carrier is future work, series by series.

### PR2-S2 (verdict flags hand-set) — **Fixed** (the flags formally tied), with two disclosed meta-flag residues.

Built: fourteen tying theorems `PR2R1.pr2s2_s0_verdict_tied` … `pr2s2_s13_verdict_tied`, one per series. Each states: for ANY booleans whose truth is equivalent to the flag's justifying proposition, the series' verdict function computes the landed outcome. The false flags are **refuted, not assumed** (S5's `foldRealizedOnTower` from `ws4_no_fold_on_tower`; S7's `inSightConserved` and `conservedReachable` from `ws3_not_conserved`; S10's `builtHasCore` from the exhaustive `ws4_no_core_built`; S13's `couplingPresent` from `ws3_grain_test`). The flag-to-theorem link is now formal, not documentary.

**Residue (disclosed, Relabeled):** two meta-flags have no propositional content and remain literal arguments in their tying theorems — S6's `carrierDecided`/`carrierWoven` and S7's `globalForced`. They are disclosed in the tying theorems' docstrings; making them propositional would require formalizing "a structural principle forces a canonical carrier / a global invariant," which no series defined. Additionally, the finding's observation that some alternative outcomes are unreachable **in principle** (S0's per-instance PARTIAL; S1/S2's TOTALIZED; S12's STOCHASTIC-NOT-BORN) is not repaired by tying — it is a property of the flag vocabularies, recorded here as standing.

### PR2-S3 (painted witnesses) — **Relabeled** (the obstruction recorded; prose corrected).

No general repair is honestly available at review scope: deriving each series' ranks/gradings/tick-hood from the tower machinery is a per-series rebuild. Closure: the review stands as the record; the README's strongest "earned, not postulated" phrasings are corrected (the S9 rate is now stated as *defined*; the S12 square as *exhibited representative*, not forced); and the witnesses' status as consistency models rather than discoveries is the review's standing finding. Any future series inherits the review's rule: a `decide` on a co-designed table certifies consistency, not discovery.

### PR2-S4 (Phase-3 recoveries by definition) — closed per series:

- **S9 (CONE) — Fixed.** The missing connective theorem is built: `PR2R1.pr2s4_cone_bounds_reach` proves, for EVERY attention, source, and depth, that `n`-step reachability is contained in the ball of radius `rate·n` (triangle inequality + sup-bound — a theorem, not a definition unfolding). The honest slack is a companion theorem: `pr2s4_ball_exceeds_reach` (the ball is symmetric where the attention is directed, so containment is strict). README corrected accordingly. Residue: the cone still carries no tick/dynamics; "light cone" remains an interpretive gloss, per the review.
- **S11 (INTERFERING) — Fixed** at the attention level: `PR2R1.pr2s4_destructive_iff_odd_holonomy` proves, for EVERY attention on the population, that the combined weight falls below the parts **iff** the built holonomy is odd — the equivalence the series claimed in prose, now a theorem over all 512 attentions. Residue (Relabeled): the parity *choice* of sign remains a choice; no theorem forces `amp` to be the parity character, and the review's finding S-1 stands as scope.
- **S12 (BORN) — Relabeled, with the obstruction now a theorem.** `PR2R1.pr2s4_square_not_unique` proves the absolute-value weight ALSO respects the cancellation, is non-negative, non-trivial, non-classical, and differs from the squared form: "FORCED" is formally refuted inside the artifact, and the verdict's honest content ("the exhibited representative of the cancellation-respecting class") is what the README now says.
- **S13 (INERT) — Fixed** where a bridge is true, **Relabeled** where it is not: `PR2R1.pr2s4_bridge_faithful` proves the re-seated `pathDist`, applied to Series 2.4's own `attendsW`, agrees with the built `stepsFrom` on every reachable pair (all thirteen); `pr2s4_bridge_diverges` records the seam as a theorem (`stepsFrom` returns 0 on unreachable pairs — conflating "unreachable" with "here" — where `pathDist` reports the sentinel). The faithfulness claim is no longer prose. Residue: the grain-blindness of `adjDist` remains definitional (the projection cannot vary in its discarded argument), so INERT remains a structural fact about the re-seat's type, per the review; the README's S13 paragraph now discloses the bridge and its seam.

### PR2-S5 (MONOTONE-ONLY misdescription) — **Relabeled** (the obstruction recorded as a theorem; prose corrected).

`PR2R1.pr2s5_tick_not_monotone` makes the periodicity a theorem: the built reification LOWERS the measure at `e2` (2 → 0), the three reachable states cycle with period three, and the rise at `e0` stands. The README's "the arrow fundamental" claims are re-scoped to what is proven (no measure-preserving bijective core; an arrow in the no-conserved-core sense on a periodic tick). The verdict name `monotoneOnly` is left in the code (renaming an accepted series' Outcome constructor is Tier-1's call, not a review repair); the mismatch between the name and the periodic model is the recorded obstruction. The total-collapse degeneracy underlying "conserved measures are trivial" is the PR2-S1 residue and closes with it.

---

## REAL findings

- **PR2-R1 (structure-independent universals)** — Relabeled: recorded; no repair at review scope. The tying theorems at least make explicit *which* propositions carry each flag, so the universals' role is now visible in the statements.
- **PR2-R2 (vacuous `True` audits)** — **Fixed**: all twelve `ws5_audit_names_not_terms : True := trivial` (S1–S12) replaced with the accepted S13 C1-S1 form (the outcome codomain proved a genuine discrimination among neutrally-named values, `by decide`), each docstring noting the repair. The review's caveat stands: this form is the accepted house repair, and it remains a weak statement; the real enforcement is the protocol §6 grep. S2's `ws5_audit_downstream_open` and S3's `ws5_audit_direction_open` remain `True` (they assert the *absence* of a theorem, which has no in-logic witness) — disclosed here.
- **PR2-R3 (documentation overclaims)** — **Fixed** for the load-bearing instances: README corrected on "for every stream" (twice, now stated as quantification over witness-carrier labelings), the contextuality claim (removed — no code referent), the S9 "earned" and cone-content phrasing (now citing the containment theorem and its slack), the S12 "earned rather than named" (now the class-representative statement citing `pr2s4_square_not_unique`), the S13 "model's own distance" (now citing the bridge and its seam), and the 2.10 "arrow is fundamental" (twice, now scoped to the no-core sense on a periodic tick). The series summaries were not swept; the README is the program's face and was the priority.
- **PR2-R4 (re-seats without bridges)** — **Fixed** for the two standing instances (S13's distance: the bridge theorems; S9's rate/reach: the containment theorem connects the cone to the reach machinery). The rule the review proposed — *a re-seat without a connecting theorem is a fresh object and must be named as one* — is recorded here for any future series.
- **PR2-R5 (series-local defects)** — Relabeled: recorded in the review; the S4 `sInf ∅ = 0` conflation is now additionally a *theorem* (`pr2s4_bridge_diverges` exhibits it), so the wart is at least formally visible. The remaining items (S3's `Faithful₂` collapse, S5's definitional non-causation and fiat singleton, S6's abandoned `succDep`) are per-series rebuilds, out of review scope.

---

## Verification state after closure

- `lake build` green over all nineteen targets (the eighteen prior plus `PR2R1`); `PR2R1.AxiomCheck` shows all 25 repair headlines on the standard three axioms or fewer.
- `scripts/gate.sh` green over all nineteen closure lines (the `PR2R1` line documents its deliberate cross-cutting imports: `P2S10`, `P2S12`, `P2S13`).
- The twelve swept `ws5.lean` files rebuild green; no proof-bearing statement in any series was weakened — the sweep replaced only the vacuous audit placeholders, strictly strengthening each (a `True` became a `decide`-proved discrimination).
- Sorry-free, no `native_decide`, no custom axioms, throughout.

*Closure discipline: every Fixed names its theorem; every Relabeled names its recorded obstruction (as a theorem where stateable). The residues disclosed above are open by honest necessity, not oversight; they are the review's standing findings for the program's next iteration.*
