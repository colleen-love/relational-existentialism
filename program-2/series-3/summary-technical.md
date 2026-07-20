# Series 2.3 — Technical summary

**Verdict: SHAPE-DRAWN, computed by `P2S3.verdict` from the WS1-WS4 flags (`ws5_verdict_eq : verdict true true
true true = Outcome.shapeDrawn`, by `rfl`). Build: sorry-free, axiom-clean (standard three only; `faithful_converges_iff`,
`ws5_verdict_eq`, `ws5_verdict_discriminates` axiom-free; `ws1_converges_typed`/`ws1_two_sided_free`/`ws5_audit_no_evaluation`
on a proper subset), gate-green (`P2S3` imports `P2S2` and its own roots plus Mathlib; `P2S1`/`P2S0`/`P1` reached
transitively through S2). Namespace `P2S3`, built on the `P2S2` pair. The convergence machinery is built FRESH and
constrained, NOT imported from Series 12 (excluded from the foundation for program-review-1's PR1-S1, the
tautology).**

## The primitive (the two additions over the S2 pair)

Series 2.3 adds exactly two things to the imported S2 pair (`slf`, `oth`, `attendsR`, `rankR`, `RCar := Fin 5`,
the collapse engine, `Recoverable`, all reached through `P2S2`), no new atom:

- `structure Valuation (X Or : Type)` with `val : X → Or` (the per-perspective valuation, from an exogenous space
  `Or`) and `raise : X → X → Or → Or` (the per-edge raising).
- `def Converges₂ c x y := c.raise x y (c.val x) = c.val y` — the valuation at `x`, raised toward `y`, agrees with
  the valuation at `y`. Instantiated at `(slf, oth)`.

Two constraint predicates make the fork genuine (anti-PR1-S1):

- `def Faithful₂ c := ∀ x y, c.raise x y = id` — the raising carries the valuation unchanged, so `Converges₂ c x y
  ↔ c.val x = c.val y` (`faithful_converges_iff`).
- `def InSight dest c := ∀ x y, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y` — the valuation agrees on every
  plain-bisimilar pair (what the structure can SEE). `dest` is LOAD-BEARING (contrast PR1-S1's phantom carrier).

The witness valuations, used ONLY inside existentials (audit (a)): `cUnif := ⟨fun _ => ⟨true⟩, fun _ _ o => o⟩`
(uniform, faithful, in-sight, converges) and `cDiss := ⟨fun z => if z = slf then ⟨true⟩ else ⟨false⟩, fun _ _ o =>
o⟩` (dissenting, faithful, NOT in-sight, fails).

## The theorems (all BUILT)

| WS | Theorem | Content | Strips to |
|----|---------|---------|-----------|
| WS1 | `ws1_converges_typed` | a faithful valuation converging at `(slf, oth)` exists (`Converges₂` inhabited) | an equality-in-`Or` fact |
| WS1 | `ws1_two_sided_free` | a converging AND a non-converging faithful valuation both exist at `(slf, oth)` — the relation fixes no valuation (audit (a), "no valuation evaluated") | `val slf = val oth` free to hold or fail |
| WS2 | `ws2_converges_decided_in_sight` | over the in-sight faithful class, `Converges₂` at `(slf, oth)` is FORCED (uses `slf`/`oth` plain-bisimilar) | "a valuation agreeing on plain-bisimilar states agrees on `slf`, `oth`" |
| WS2 | `ws2_insight_inhabited` / `ws2_sight_is_uniform` | the in-sight class is inhabited (`cUnif`); on this SHNE carrier its members are globally constant (disclosed degeneracy) | inhabitation / a bisimilarity-uniformity fact |
| WS3 | `valLift_not_recoverable` | valuation-difference on a plain-bisimilar SHNE pair ⇒ the `val`-labelled lift is `¬ Recoverable` (Series 07 read for the valuation) | a bare `¬ Recoverable` fact |
| WS3 | `ws3_dissent_is_import` | every faithful valuation FAILING `Converges₂` at `(slf, oth)` yields a `¬ Recoverable` lift, via `valLift_not_recoverable` (collapse engine + negative import horn) | "`val slf ≠ val oth` on plain-bisimilar `slf`, `oth` ⇒ `¬ Recoverable`" |
| WS4 | `ws4_insight_proper` | the in-sight class is inhabited (`cUnif`) AND properly contained in faithful (`cDiss` faithful, out of sight): `InSight ⊊ Faithful₂` (anti-PR1-S1) | inhabited + proper-subset fact |
| WS4 | `ws4_two_zone` | (i) full-class underdetermination (`cUnif` converges, `cDiss` fails, both faithful); (ii) in-sight forcing; (iii) every dissent an import — both zones on witnessed valuations at `(slf, oth)` | "a discriminating function over a constrained class reaching two values, both witnessed" |
| WS5 | `ws5_verdict_eq` | `verdict true true true true = Outcome.shapeDrawn` (computed, `rfl`) | a computed outcome |
| WS5 | `ws5_verdict_discriminates` | the verdict reaches `forcedFull` / `disconnected` / `partial'` on flipped flags — more than one value | a discrimination fact |
| WS5 | `ws5_flags_justified` | the four `true` flags earned by the WS1-WS4 headlines | the conjunction of the WS1-WS4 stripped statements |
| WS5 | `ws5_audit_no_evaluation` / `ws5_audit_fork_genuine` / `ws5_audit_dissent_import` / `ws5_audit_faces_are_readers` | audit (a)/(c)/(d) + the K1 anchor (`oth` `RealFor` the named `slfReader`, twoness `¬ Recoverable`, cited from S2) | genuine propositions |
| WS5 | `ws5_audit_direction_open` / `ws5_audit_names_not_terms` | audit (b)/(e), grep-certified `True` (NAMES/absence properties, the CORRECT non-decisions) | — |

## Why this is not the PR1-S1 tautology (audit (c))

PR1-S1: Series 12's first convergence fork was a tautology because `Compass`/`Converges` mentioned neither `dest`
nor `reify` — the fork landed the same on every coalgebra by the parameter type alone. Series 2.3 forecloses it,
load-bearing on the S2 structure:

1. **The forcing uses the structure.** `ws2_converges_decided_in_sight` consumes `slf`/`oth` plain-bisimilarity
   (`ws1_atomless_bisim` on `outDest attendsR`, every node `SHNE`). On a carrier where `slf`, `oth` were not
   plain-bisimilar it would fail. `dest` appears in `InSight`.
2. **The class is genuinely constrained.** `ws4_insight_proper`: `InSight ⊊ Faithful₂`, both inhabited — the
   `cDiss` witness is faithful yet NOT in-sight (it separates the plain-bisimilar `slf`, `oth`). Restricting to
   in-sight excludes a genuine faithful valuation.
3. **Both zones witnessed on the same pair; the verdict discriminates.** `ws4_two_zone` + `ws5_verdict_discriminates`.

## The disciplines (all held)

- **(a) No valuation evaluated.** Every theorem quantifies over `Or` and `c`; `cUnif`/`cDiss` appear only inside
  existentials; `ws1_two_sided_free` witnesses that `Converges₂` fixes no valuation.
- **(b) The direction is never decided.** No theorem states `∀ c, Converges₂ c slf oth` or its negation. The
  in-sight forcing is conditional on a proper sub-class; the verdict locates the fork (reaches both values) and
  fills neither. `ws5_audit_direction_open` is the correct non-decision.
- **(c) The fork is genuine.** Above. Confirmed by the Phase C and Phase F blind reviews (audit (c) pressed hardest).
- **(d) Dissent is an import.** `ws3_dissent_is_import` is a proof term resting on Series 07.
- **(K1) The faces stay the load-bearing readers.** `ws5_audit_faces_are_readers` cites `ws2_other_reader_wise`
  (`oth` `RealFor` the named `slfReader`) and `ws2_other_non_recoverable` (the twoness an import), so the coherence
  is between genuine readers, not decoration over labels.
- **(e) Names-not-terms.** No identifier embeds a forbidden content-name; every `\b(orientation|convergence|
  coherence|compass|self|other|…)\b` grep hit is docstring prose. `Converges₂`/`converges` (verb) allowed;
  `val`/`Valuation` allowed; `slf`/`oth` allowed.

## Disclosed

- **PX-1 twoness-lift NOT taken.** The S2 twoness is rank-based; the charter permits lifting it to import over
  lateral peers. Weighed at Phase B and declined: the fork's genuineness rests on `slf`/`oth` plain-bisimilarity
  (orthogonal to rank-vs-import), the twoness is already a `¬ Recoverable` import in S2 (cited via the K1 anchor),
  and a lateral construction would add complexity without strengthening SHAPE-DRAWN.
- **The in-sight class is degenerate on this carrier** (constant valuations only, `ws2_sight_is_uniform`), the
  Series 12 PR3-R1 disclosure — still proper and inhabited, so the fork stands; disclosed rather than hidden.
- **`ws4_two_zone` is a packaging conjunction** over WS2/WS3 + the underdetermination witnesses (the accepted
  Series 12 `ws4_two_zone` pattern), not a new cross-lemma.
