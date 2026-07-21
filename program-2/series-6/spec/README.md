# Program 2 Series 6 (2.6) — Design index (`spec/README.md`)

**THE THREAD, and whether the relating carries it. This is the design batch for Series 2.6: prove that STRICT
relational identity fails across a tick (WS1, the trivial ground), fork the WEAK continuity's recoverability
(WS2, recoverable — an endogenous succession — or an import), read the single lived line as the self's
LINEARIZATION import (WS3, 1D lived time self-relative, on Series 2.1), and at the knot draw the fork on the weak
continuity — WOVEN and SEVERED both reachable, a companion mortality fork (attention-relative cessation), the
continuity self-relative, no fiat and no costume (WS4). It fixes the imported chain, the two new primitives (the
weak continuity built fresh and the reading of the single line as the linearization import), the discipline (the
knot on the weak continuity not on strict identity failing, 1D on the linearization import not scalar rank, the
fork not by fiat, no absolute persistence), the cross-workstream triage, the outcome classes, and the
names-in-prose rule. Committed as one batch with `ws1-design.md`…`ws5-design.md` before any `formal/` file exists
(Phase B gate).**

---

## 1. The imported chain (reached, not rebuilt)

Series 2.6 imports **`P2S5` only** and reaches `P2S4` / `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively (the
layered chain; the gate enforces `^import (P2S5|P2S6)…`). Its working material, reached through the chain:

| Piece | Origin (transitive) |
|---|---|
| The recoverability / import test: `Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `ws4_recoverable_not_import`, `ws1_atomless_bisim` (the collapse engine), `LkObj`, `PkObj`, `SHNE`, `pkSingle` | `P1.Core` / `P2S0` |
| The rank-labelled lift and the attention-distinction: `rankLift`, `AttentionDistinguishes`, `ws2_many_general`, the passive in-attention `attendedBy` | `P1.Reader` / `P2S0` |
| The tick witness `TCar = Fin 7`: `attendsT`, `rankT`, `reifyT`, `kA`/`kB`/`kC`, `isTick`, `causal`, `ws1_tcar_SHNE`, `plainOf_rankLiftT` | `P2S1` |
| **The linearization import** (a total order of the concurrent moments is non-recoverable): `ws4_linearization_import`, `ws4_causal_order_endogenous` | `P2S1` (read as the single line at S6 WS3) |
| The knowing-asymmetry (for attention-relative cessation): the directional labelled lift, `ws3_direction_not_recoverable` pattern | `P2S0` (reworked fresh at S6 WS2/WS4) |
| **The weak continuity** (a successor-continuity lift, coarser than strict identity) and the reading of the single line as the linearization import | **built fresh at S6 WS1/WS2/WS3** |

**Series 2.6 adds exactly two things:** THE WEAK CONTINUITY (a successor-continuity lift over the relating,
coarser than the rank lift that fixes strict identity) and the reading of the single lived line as the self's
LINEARIZATION import. Nothing below `P2S5` is imported directly.

## 2. The primitives, built fresh

### 2.1 The three levels of identity (the frame of the series)

Over a labelled lift `destL : X → LkObj κ Q X` with plain reduct `plainOf destL`, three relations of "sameness"
sit nested, weakest to strongest:

1. **PLAIN bisimilarity** — `∃ R, IsBisim (plainOf destL) R ∧ R x y`. On any `SHNE` (atomless) carrier the
   collapse engine (`ws1_atomless_bisim`) makes EVERY pair plain-bisimilar: too weak to be identity.
2. **The WEAK continuity** — recoverability of a coarse continuity lift `contLift` (a labelled lift whose label
   marks the successor-continuity, coarser than rank). This is the new object. It is genuinely BETWEEN plain and
   strict: it can hold where strict identity fails.
3. **STRICT identity** — label-bisimilarity of the FULL rank lift `rankLift dest rank`. Across a tick the
   reified successor outranks its constituent, so strict identity FAILS (`AttentionDistinguishes`, the
   `ws2_many_general` mechanism) while the pair stays plain-bisimilar. This is WS1, the trivial ground.

The series lives at level 2: is the weak continuity RECOVERABLE from the plain relating (an endogenous
succession the structure carries), or an IMPORT (non-recoverable, a grace from outside)?

### 2.2 The weak continuity as a continuity lift

The weak continuity is a labelled lift `contLift : X → LkObj κ Q X` whose label marks the successor-continuity
bit (the "same-stream" mark, the directional knowing that binds one moment to the next). Its recoverability is
the fork:

- **Recoverable (WOVEN):** when the continuity mark is uniform over the relating — the MERGED carrier, where the
  self's stream is one (mutual attention across the tick) — every plain bisimulation is already a
  continuity-bisimulation. The continuity is endogenous. Proved by the general lemma `const_first_recoverable`
  (a lift all of whose edge-labels share one value is `Recoverable`).
- **Non-recoverable (SEVERED):** when the continuity mark distinguishes a plain-bisimilar pair — the CUT carrier,
  where the self's attention is cut between contexts (one-way attention, the knowing-asymmetry) — the continuity
  is NOT recoverable, an import. Proved via `AttentionDistinguishes ⇒ ¬ Recoverable` (`ws4_recoverable_not_import`
  contrapositive), the `ws3_direction_not_recoverable` mechanism reworked fresh.

The weak continuity is GENUINELY WEAKER than strict identity: on the merged carrier the rank lift (strict
identity) separates the two rank-distinct moments while the continuity lift (weak) is recoverable and relates
them (`ws2_weaker_than_strict`). So it is not strict identity relabelled (audit b).

### 2.3 The single line as the linearization import

The partial causal order on the moments (`causal`, a reification-dependency) is ENDOGENOUS: witnessed, rank
constrained, and genuinely PARTIAL (the concurrent pair `kA`,`kB` is incomparable). The single lived line is a
TOTAL linearization of that partial order, and Series 2.1 proved every such linearization an IMPORT: for any
order label `ord` distinguishing the concurrent pair, the ordered lift is not `Recoverable`
(`ws4_linearization_import`). So the ONE-DIMENSIONALITY of lived time is the self's import over a
partially-ordered reality, and it rests on the total order being non-recoverable, NOT on rank being an
ℕ-valued scalar — the tower `rankT` cannot even linearize the concurrent pair (`rankT kA = rankT kB`). (WS3,
audit d.)

### 2.4 The two witnesses for the fork

Both at `Cardinal.{0}` on `Fin`/`Bool`, monomorphic (as in S0/S1/S5).

- **The merged carrier `MCar = Fin 2`** (built fresh): the WOVEN zone. Two moments `m0` (rank 0), `m1` (rank 1,
  the reified successor) with MUTUAL attention (`m0 ⇄ m1`). Strict identity fails (`rankLift`-separated), yet the
  continuity lift `mergeLift` (uniform continuity mark) is `Recoverable`: a recoverable weak continuity binding
  rank-distinct moments. Everything is mutually attended (nothing ceases): the CONSERVATIVE companion.
- **The cut carrier `CCar = Bool`** (built fresh): the SEVERED zone. `c0` attends `c1`, `c1` attends nothing;
  the continuity lift `cutLift` tags the directional knowing (`c0` knows `c1`, `c1` does not know `c0`). Its
  plain reduct is the symmetric relating (both nodes `SHNE`), and the continuity is NOT recoverable
  (`AttentionDistinguishes`): the continuity is an import. `c0` is attended by nothing (`attendedBy = ∅`): a self
  a self nothing holds, the MORTAL companion (attention-relative cessation).

Two carriers, one question (is the coarse continuity recoverable), forked WOVEN vs SEVERED. Both reachable ⇒ the
fork is not decided by fiat, and the continuity is SELF-RELATIVE.

## 3. The discipline (the honesty invariants, transcribed)

- **The knot on the weak continuity, not the strict failure (audit c, the Phase-2 costume gate).** The verdict
  (WS5) keys on the weak continuity's recoverability (WS2/WS4) and the linearization import (WS3), NOT on strict
  identity failing. Strip the strict-failure flag alone and the verdict does not decide; the verdict requires
  the line-is-import flag and the weak-continuity reachability flags. "Relational identity fails across a tick,
  so the self is a new relatum" is a true fact but a COSTUME; the finding rests on the weak continuity and the
  linearization.
- **The 1D line on the linearization import, not scalar rank (audit d).** `ws3_line_is_import` rests on
  `ws4_linearization_import` (the total order non-recoverable), and `ws3_line_not_scalar` shows the tower rank
  cannot linearize the concurrent pair (`rankT kA = rankT kB`). The partial order is endogenous; the single line
  is the import.
- **No absolute persistence (audit a, the self-relative discipline).** No theorem asserts the self persists
  frame-independently; the weak continuity's recoverability is FOR a carrier, self-relative — WOVEN and SEVERED
  both reachable, neither forced. The single line is the self's import.
- **The fork not by fiat (audit b).** WOVEN (`ws2_cont_recoverable`) and SEVERED (`ws2_cont_is_import`) are both
  reachable structures; the weak continuity is genuinely weaker than strict identity (`ws2_weaker_than_strict`,
  it holds where strict fails), not strict identity relabelled, and SEVERED is not excluded by construction.
- **Names-not-terms (audit e).** No proof term, definition, or discharged obligation is named "self," "thread,"
  "persistence," "life," "death," "time," "here," "there," "God," "choice," or "subjectivity" as content. The
  carriers use neutral names (`MCar`, `CCar`, `mergeLift`, `cutLift`, `succDep`, `Outcome.woven`/`severed`); the
  interpretive words live only in docstring prose. Audit e is enforced by the protocol §6 grep, not by a proof
  term.

## 4. Cross-workstream triage

| WS | Payoff | Strips to |
|---|---|---|
| WS1 | strict identity fails across a tick; the tick-successor relation | a reified relatum is plain-bisimilar to its constituent yet rank-lift-separated (`AttentionDistinguishes`); a witnessed reification-dependency edge |
| WS2 | the weak continuity is recoverable on the merged carrier, an import on the cut carrier, and genuinely weaker than strict identity | a lift with one edge-label value is `Recoverable`; a lift separating a plain-bisimilar pair is not `Recoverable`; on one carrier the rank lift separates a pair the continuity lift relates |
| WS3 | the single line is the linearization import; the partial order is endogenous; rank does not linearize | for any order label distinguishing an incomparable pair, the ordered lift is not `Recoverable`; a witnessed rank-constrained partial order with an incomparable pair; `rankT kA = rankT kB` |
| WS4 | the fork: WOVEN and SEVERED both reachable, self-relative; the mortality companion (attention-relative cessation) reachable, conservative reachable | a `Recoverable` lift and a non-`Recoverable` lift both exist; a node with empty in-attention exists, and one whose in-attention is nonempty |
| WS5 | the verdict computed + audit a–e | an `Outcome`-valued function of booleans, `= shapeDrawn` by `rfl`, discriminating by `decide`, flags earned by the WS1–WS4 headlines |

## 5. Outcome classes (WS5)

`inductive Outcome | woven | severed | shapeDrawn | partial'` (neutral names; no forbidden content-name).

- **SHAPE-DRAWN (the computed verdict).** Strict identity fails and the single line is an import (the ground);
  the weak continuity is RECOVERABLE on the merged carrier and an IMPORT on the cut carrier (both reachable);
  so which obtains is SELF-RELATIVE and not forced by the structure. The thread is drawn exactly; whether it is
  recoverable is undecidable from within, self-relative. This is the honest expectation.
- **SEVERED (pre-registered, honest).** Would obtain if NO recoverable weak continuity existed — every candidate
  an import, the self a discontinuous succession, the continuity always a grace from outside. FALSIFIED here by
  the merged carrier's recoverable continuity; reported in its direction if the merged witness fell.
- **WOVEN (pre-registered, honest).** Would obtain if the weak continuity were recoverable ABSOLUTELY (forced on
  every carrier) — the self persisting as an endogenous succession. FALSIFIED here by the cut carrier's import.
- **PARTIAL' (degenerate).** No strict failure, or no linearization import, or one side of the fork excluded by
  construction (a fiat).

## 6. Module layout (`P2S6` namespace, registered at Phase E)

`P2S6.lean` imports `P2S6.ws1`…`P2S6.ws5`; `P2S6/wsN.lean` one per workstream; `P2S6/AxiomCheck.lean` runs
`#print axioms`. `ws1` imports `P2S5` (the chain); `ws2`…`ws5` import their predecessor `ws` files. Namespace
`P2S6`, mirroring `program-1/series-13/formal/Series13/`. Gate: `check program-2/series-6
"^import (P2S5|P2S6)(\.[A-Za-z0-9_]+)*$"`.

---

*No em dashes in final academic copy. The thread this batch designs is the self through time, re-woven each
moment; the knot is whether the relating carries the weave or it is imported. The verdict is computed, never
hand-set; the fork is genuine (WOVEN and SEVERED both reachable); the knot rests on the weak continuity and the
linearization import, not on strict identity failing, and not on rank being a scalar.*
