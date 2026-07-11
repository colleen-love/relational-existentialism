# Series 05 — Design docs index

Seven per-workstream design documents for **Relational Existentialism, Series 05** (*Stratification as boundlessness*). Each follows the Series 04 spec discipline: candidate framings of the obligation (with exact Lean 4 signatures, ambient theory, success condition, and explicit failure mode), a paper-decidable triage, the framing decision collapsed into a table with the choice downstream of the triage, then the winning candidate developed into a full mathematical design with proof architecture, definitions/lemmas, and upstream dependencies.

- **[ws01-design.md](./ws01-design.md)** — The tower and its colimit *(blocking; the colimit gate)*.
- **[ws02-design.md](./ws02-design.md)** — The explosion, and the forced answer *(the spine; Explosion Dilemma + index theory)*.
- **[ws03-design.md](./ws03-design.md)** — Boundlessness without a wall.
- **[ws04-design.md](./ws04-design.md)** — No first, no last: poles and the view from nowhere *(two severe coincidence duties)*.
- **[ws05-design.md](./ws05-design.md)** — The self-bounding of the world, revisited.
- **[ws06-design.md](./ws06-design.md)** — Relating across levels, and attention as grade-shift *(the deepest technical risk; the distributive law)*.
- **[ws07-design.md](./ws07-design.md)** — The anti-trivialization audit *(the verdict; the strip-test ledger)*.

## Standalone convention

Series 05 is **wholly standalone** (charter §1). Every Series 04 (and, in WS6, Series 03) theorem it uses is **transcribed** into `series-05/formal/wsNN.lean` and re-namespaced `Series05.WSNN` — nothing is imported from `series-04/` or `archive/`. The transcribed carrier machinery (`PkObj`, `PkMap`, `Coalg`, `IsTerminalCoalg`, `lambek`, `Bisim`, `bisim_eq`, `νPk`, `νLk`, `Cofix`, `Reaches`, `ReachSet`, `face`, `lcomp`, `NonAtomic`, `carrier_card_ge`, `ws2_collapse`, `ws3_faces_never_annihilate`, `ws4_no_top_cardinal`, `ws5_global_groundless_collapses`, `ws6_lawvere_incomplete`, `ws6_omega_nonterminating`, `ws3_no_distributive_law`, `ws3_weak_bialgebra`, `ProgramVerdict`) is faithful — the same axiom-clean proofs, re-rooted. Toolchain pinned as Series 04: Lean 4 `v4.15.0` / Mathlib `v4.15.0`. Build root `Series05`; `AxiomCheck.lean` owed, importing the whole build and emitting `#print axioms` for every headline theorem.

## The single ambient-theory choice, shared across workstreams

- **Encoding:** ZFC as in Lean 4 + Mathlib; anti-foundedness *modelled* by terminal coalgebras (QPF `Cofix`), not an AFA axiom — inherited from Series 04/03.
- **Carrier functor `F`:** the labelled bounded-powerset functor `X ↦ P_{κ_α}(Q × X)` at each level; **no single `F_∞`** on the colimit (the structure map is level-indexed) — a colimit functor `F_∞` is the pre-registered WS1 fallback if WS6 needs a uniform distributive law.
- **Monad `T`:** `P_κ` (bounded union), entering at WS6 as the composition/algebra side.
- **Distributive law `λ`:** no *strict* law (transcribed Series 03 impossibility `ws3_no_distributive_law`); a **graded weak** Egli–Milner law commuting with the depth-grade (WS6 DL2), whose existence is conditional on the grade being an inert `ℤ`-label.
- **Index `I`:** `ℤ` (WS2 winner) — no least, no greatest, self-dual, all decidable; `ℚ` (dense) is the typed escalation if WS6 needs interpolation.

## Cross-workstream triage summary (the framing decisions, collapsed)

| WS | Winning candidate | Key rejected candidate | Decisive triage fact | Expected outcome |
|---|---|---|---|---|
| 1 | C2 — ordinal-cofinal directed colimit, bound-relaxing inclusions | C1 (union over ℕ: supremum cardinal walls); C4 (bidirectional limit: `P_κ` breaks cofiltered limits) | gate reduces to level-local `bisim_eq` + `ι_inj` | Discharged |
| 2 | E1 (dichotomy) + `ℤ` index + F2 forced answer | E2 (proof-predicate, unstatable); I3 (coinductive index, overkill) | both Explosion horns are transcribed Series 04 theorems | Discharged + Impossibility (the Dilemma) |
| 3 | B2 — no-top on colimit, powered by no-last-level | B4 (face-counting wall: Series 04 proved impossible) | strip no-last-level ⇒ falls to single-carrier cardinal wall | Discharged; B4 recorded as inherited impossibility |
| 4 | A2 (+coincidence); P1 for ℤ; **V1+V3** no-view coincidence | **V2** (launders the strip test); C4 categorical biproduct | V2 survives stripping `View` → bare order fact; V3 does not | Discharged (conditional on WS6); no-view Partial if only V2 |
| 5 | G1 (thesis) + G2 (earned adjudication) | G3 (off-spine improper face: self-face trivial off diagonal) | M1/M2 stand; endogeneity is between-levels, not within-carrier | Discharged with residual-fiat caveat (G4) |
| 6 | GF1 (inert ℤ-label grade); DL1 (no strict law) + DL2 (graded weak law) | GF2 (functorial grade); AT2/AT3 (attention coincidences) | `ℤ` has no bottom ⇒ grade-composition is floor-free; union commutes with grade-shift | Discharged (A/B/C, DL); attention **Partial/Trivialized** |
| 7 | `payoffsEstablished` verdict + strip-test ledger | `oneDoubleUnboundedness` (reduction incomplete); `trivialized` (anchors refute) | 2 payoffs derive from double-unboundedness, leak-freeness does not (a second fact) | Discharged; verdict `payoffsEstablished` |

## The honest headline the design anticipates

Stratification genuinely delivers **boundlessness without a wall** (WS3, no-top powered by no-last-level, surviving its strip test), **groundlessness without collapse** (WS4, the local/global decoupling), **cross-level leak-free relating** (WS6, transported verbatim and floor-free because `ℤ` has no bottom), and it **dissolves** Series 04's face-bounding problem by relocating the bound between levels rather than solving it within a carrier (WS5). But three "totality" items are, by the paper triage, *index facts with philosophical readings* rather than earned carrier theorems: the **pole coincidence** (order self-duality), the naive **no-view-from-nowhere** (the V2 that launders), and **attention-as-grade-shift** (Trivialized unless the replicator/convergence coincidence delivers, which is negative on this carrier). The predicted verdict is therefore `payoffsEstablished`, not `oneDoubleUnboundedness` — the same honest middle Series 04 reached, for the same structural reason: the reduction to one fact is partial, and the design says exactly where.
