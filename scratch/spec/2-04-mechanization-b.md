# 2-04-mechanization-b — Work Order: Carving Ω_C, Re-anchoring, and the C1 Landing

Target file: `scratch/formal/Spec204d.lean` (Spec204a–c occupied). Conventions in force: no `sorry`; doc-comment every declaration with its spec address (cite 2-04, per the spec-first resolution recorded in the Spec204 headers); axiom audit per theorem reproduced in-build; results appended to 2-04 post-hoc-marked, predictions left frozen; hostile-first ordering mandatory.

**Naming note.** The prior results note referred to this order as "2-05-mechanization-b"; that label is retired here for consistency with the spec-first resolution (spec = 2-04.md, orders = 2-04-x). Alias recorded; nothing else changes.

**Scope in one line.** Everything 2-03 §1's honesty lemmas said was vacuous or trivial over the collapsed universe is now restated and proved contentful over the corrected universe; T16 lands at the ω-tier with its loan-scaffold named; and the C1 conditional — *we are born as bridges* — is discharged on the hosted connected part. On success, the condition proposed at O-2-04-5 ("execution complete") is met: D19 may be written, and the self-reference spec opens. **No declaration in this file may consult the D19 register**; that discipline holds through the last line of this order precisely because it is the last order before the register is opened.

---

## Stage 0 — Ω_C carved (MUST)

The one item Spec204c left uncarved, now made an object:

- `coherentPartC` — the greatest coherent subcoalgebra of `ZΩC` (Knaster–Tarski over the L1-C covariety; all ingredients proved in Spec204a/c). `Ω_C` := its carrier pair.
- Lambek in both sorts on the coherent part; `closeC` the anamorphism into Ω_C (not merely into ZΩC).
- Citizens relocated: `omegaHat2_mem_ΩC`, `elt2_mem_ΩC`, `elt3_mem_ΩC`; `anti_mirror_ΩC` restated so FP5's separation is a fact *about Ω_C the object*, one `exact` away from Spec204c's theorem.
- `hostedC : Ω_R → Prop` (∃ object-point whose pattern contains it) and `hostedPart` — the doctrine of 2-04 §5 given its formal referent. Interpretation note in the doc-comment: doctrine-level quantifiers over relations relativize here; this is application of normative §5, not a new decision.

## Stage 1 — the honesty lemmas, lifted (MUST)

Spec203's `eqDepth_trivial` and `genesis_vacuous` exist so no reader mistakes T5/T10 for resolved; this stage replaces both with contentful counterparts.

- `EqDepthC` / `ρC` over Ω_C, definitions carried from Spec201d with `ends` over O ⊕ R.
- **FP-B1:** `eqDepthC_nontrivial` — a pair of Ω_C elements agreeing to depth 0 and separating at depth 1 (elt2/elt3 are the intended witnesses; their Spec204c separation is depth-1 by sort-profile, so the eqDepth computation should be mechanical).
- **FP-B2:** `GenesisC` stated over Ω_C; `genesisC_nonvacuous` — the hypothesis class is inhabited (the vacuity of the collapsed universe is gone). **Truth-value stays open**, exactly as 2-01d anchored it; the doc-comment says so in referee-hostile terms. T10's sharpened form ("is F(1)'s pregnancy enough to reach everything?") is *stated* as `ReachableFromSeeds` and left open — it is now a precise question about Ω_C, which is the re-anchoring deliverable, not its answer.
- T5 surrogate: `closing_denseC` **attempted** under the same drop clause as its ancestor (drop freely if the assembly needs machinery out of scope; the deferral was providential once and is sanctioned again). No frozen prediction — logged as OPEN-attempt, outcome recorded either way.

## Stage 2 — T16 at the ω-tier, loan named loudly (MUST)

- `Ω_R_infinite` — from the strict ascent (`ascentC` / stage embeddings): the corrected relation carrier is infinite.
- **FP-B3:** `T16_ω` — no object of Ω_C has a total pattern: `pat` is finite (ω-tier) and Ω_R is infinite; done.
- **The honesty note, mandatory, in the doc-comment and the results write-up:** this is *scaffold-assisted* T16 — the finiteness that proves it is the D4 κ-loan's ω-instance, not an intrinsic bound. The intrinsic T16 still owes T11 (or the A-T fallback). T16_ω is real and usable at this tier; it is not the loan's discharge. Any downstream theorem consuming T16_ω inherits this caveat by citation.

## Stage 3 — the C1 landing (SHOULD; the order's star)

The conditional is proved (`no_windowless_of_connected_of_no_total`, Spec202); T16_ω discharges its no-total hypothesis at this tier. What remains is connectivity — and the record already contains the anti-desired-outcome precedent (`coprod_disconnected`), so:

- **FP-B4 (hostile):** Ω_C is **not** globally connected — unhosted chaff and disjoint behaviors predicted to witness disconnection. Prove the disconnection witness if it exists; if Ω_C surprises us by being connected, better news, post-hoc note.
- `connectedHostedPart` or the appropriately relativized hypothesis: connectivity stated over the hosted part / the close-image of connected descriptions, whichever the proofs favor — the relativization is the §5 doctrine at work.
- **FP-B5:** `no_windowless_hosted` — on the hosted connected part of Ω_C, at the ω-tier, there is no windowless object: `Internal(x) = pat(x)` is unsatisfiable there. *We are born as bridges*, machine-checked, with its two hypotheses honestly priced (ω-scaffold via T16_ω; hostedness via doctrine). The doc-comment carries both prices and cites 2-02 §4's original conjecture route.

## Stage 4 — P3h, positive direction (SHOULD)

Deferred from the prior order's Stage 7:

- `ConnectedDescription` defined (every relation-point reachable from some object-point via pat/ends descent).
- **FP-B6:** `hosted_of_closeC_connected` — every relation-point in the close-image of a connected coherent description is hosted. Together with `unhosted_exists` (Spec204b), the P3h picture completes: fails globally, holds on the connected close-image — FP3's split, both halves landed.

## Stage 5 — B5 completion: the interface pack (SHOULD)

Re-instantiate against `TwoSortedC` the interface theorems not yet carried (P4_static_C, piC_comm, contextsC_differ done):

- T14 pack: `containedInC_preorder` (refl, trans), π-monotonicity, the antisymmetry-failure witness, the MutualPartial corner. The fish corner's doc-comment keeps its line.
- Reveal pack: P1 barrier two, existence form (`revealC_asymmetric` — models with shared r where the two Reveals differ); T13 chain-step bound (`hearsayC_bound` — the intersection ⊆-chain).
- `deployableC` and the dichotomy analogue; `holdDepthC` lemmas as needed by Stage 3's Internal work.
- MAY (drop freely): the comparative fish/partner witness (T14d) — still deferred unless it falls out of boolWitnessC extensions.

## Stage 6 — T4 profiles, staged (MAY; gate to order c)

With EqDepthC in hand, T4's raw material exists for the first time:

- Profile definitions only (`wProfile`, the reachable Reveal-assemblies along finite hearsay chains; O8 default: all finite depths) + `≈w` as profile-isomorphism-over-pat(w) + reflexivity/symmetry (transitivity MAY defer).
- A non-degeneracy witness (two objects, one observer, ≈w distinguishing) if cheap.
- **Full T4, the S1 pigeonhole, and T7 are out of scope** — they are order c's contract, queued per 2-02 §7, and S1 must be attacked hostile-first there (R3's most-wantable warning still applies).

---

## Frozen predictions (hostile-first; frozen at this commit)

| # | Prediction | Falsifier would mean |
|---|---|---|
| FP-B1 | eqDepthC nontrivial (elt2/elt3) | separation was shallower than believed; re-audit FP5 |
| FP-B2 | GenesisC non-vacuous; truth-value open | vacuity persists — re-anchoring incomplete, diagnose |
| FP-B3 | T16_ω holds (finite pat, infinite Ω_R) | ascent misread; halt Stage 3 |
| FP-B4 | Ω_C globally disconnected (chaff witnesses) | global connectivity — C1 lands *unrelativized*, post-hoc note, better news |
| FP-B5 | no_windowless on the hosted connected part | C1's route fails despite T16_ω — most interesting negative of the order; loud write-up |
| FP-B6 | hosted on connected close-image | the §5 doctrine loses its positive half; doctrine deepens, marked |

## Deliverable summary

| Stage | Level | Contract items |
|---|---|---|
| 0 | MUST | coherentPartC, Lambek, closeC, citizens, hostedPart |
| 1 | MUST | FP-B1, FP-B2, closing_denseC attempt (drop clause) |
| 2 | MUST | FP-B3 + the loan caveat |
| 3 | SHOULD | FP-B4, FP-B5 — the star |
| 4 | SHOULD | FP-B6 |
| 5 | SHOULD | T14/Reveal/T13/deployable pack |
| 6 | MAY | T4 profile scaffolding |

Success criterion: Stages 0–2 land clean → re-anchoring is done and the honesty debts are paid. Stage 3's outcome, either way, is the headline. **On completion of Stages 0–5: the O-2-04-5 condition is met — record it in the results, and hand the file back without touching §8. The register is the owner's to open.**
