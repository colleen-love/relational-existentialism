# WS2, The inherited collapse (baseline, transcription, NOT relitigation)

**Design doc. Series 0. Owns: `ws2_collapse_inherited`, the statement that without the import the atomless symmetric world is the One, restated over the symmetric relating `symDest` by APPLYING the imported P1 collapse engine `ws2_import_theorem_static`. This is BASELINE, in a handful of lines, explicitly not a new or uncertain result of Series 0. No series verdict hangs on it (discipline 4, audit d).**

*Series 0 IMPORTS the P1 engine (README §2.1); WS2 does not re-prove the collapse, it APPLIES the imported theorem to `symDest`. The one signature risk is discipline 4: dramatizing the collapse as a Series-0 result, or letting the WS5 verdict hinge on it, is the category error the charter forbids (SERIOUS).*

## The object at stake

The charter's WS2 (§2): re-establish, by transcription from the P1 collapse engine (`κ`-free), that without the import the atomless symmetric world is the One — atomless states are plain-bisimilar over the symmetric relating, so a behaviorally-identified atomless carrier is a subsingleton. Stated and proved as the INHERITED baseline the import will act against, NOT argued for or against. The symmetric relating's neighborhoods may be infinite (unbounded in-degree); the engine tolerates this as it tolerated `κ`-bounded neighborhoods in Program 1. No drama, no verdict hangs on it.

**Ambient theory.** README §2.1 (imported `ws2_import_theorem_static`, `BehaviorallyIdentified`, `SHNE`), §2.2 (`symDest`).

## Candidates

### C1, apply the imported engine to `symDest` (the lead)

```lean
/-- **The inherited collapse (baseline).** Without the import, the atomless, behaviorally-identified
    symmetric world is a subsingleton: the One. The imported P1 engine, applied to `symDest`. -/
theorem ws2_collapse_inherited (hinf : ℵ₀ ≤ κ) (hcar : Cardinal.mk X < κ) (attends : X → Finset X)
    (hbehav : BehaviorallyIdentified (symDest hinf hcar attends))
    (hatom : ∀ x, SHNE (symDest hinf hcar attends) x) : Subsingleton X :=
  P1.Core.ws2_import_theorem_static (symDest hinf hcar attends) hbehav hatom
```

One line: the collapse is the imported `ws2_import_theorem_static` instantiated at `symDest`. It is manifestly NOT re-proved; the proof term IS the P1 engine. `hcar : mk X < κ` is the ambient carrier-size hypothesis for `symDest`'s possibly-infinite in-attention neighborhoods (README §2.2, audit a), NOT an ontological ceiling.

- **Ambient:** `P1.Core.ws2_import_theorem_static`, `symDest`.
- **Success condition (baseline):** typechecks as a direct application of the imported theorem.
- **Failure mode:** *relitigation (discipline 4).* Foreclosed: the proof is the imported engine verbatim; no new argument, no drama. **Winner (the baseline).**

**Paper triage.** Immediate: `symDest hinf hcar attends : X → PkObj κ X` is a plain coalgebra, so `ws2_import_theorem_static` applies unchanged. **Winner.**

### C2, re-prove the collapse from scratch over the symmetric relating (rejected)

```lean
theorem ws2_collapse_reproved (…) : Subsingleton X := by/- rebuild hneRel_isBisim, ws1_recovers_static … -/
```

Re-derive the collapse engine (`hneRel`, `hneRel_isBisim`, `ws1_recovers_static`) freshly over `symDest`. **Reject:** this DRAMATIZES the collapse as a Series-0 result, the exact category error the charter forbids (§4.c, discipline 4). The collapse is Program 1's theorem, inherited; re-proving it invites presenting it as new or uncertain. **Reject, and the review greps that `ws2_collapse_inherited`'s proof term is the imported engine, not a fresh derivation.**

### C3, make the collapse an input to the WS5 verdict (rejected, SERIOUS)

```lean
def verdict (…) (collapseHolds : Bool) : Outcome := if collapseHolds then … else …   -- REJECT
```

Let the verdict branch on whether the collapse holds. **Reject as SERIOUS (audit d):** no series verdict may hinge on the inherited collapse. WS5's `verdict` consumes WS1/WS3/WS4 flags ONLY; `ws2_collapse_inherited` is baseline, cited in the audit as "transcribed and untouched," never a verdict input. The audit clause `ws5_audit_collapse_inherited` states exactly this: the collapse theorem is definitionally the imported one, and it is not among `verdict`'s arguments.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | apply imported engine to `symDest` | `ws2_import_theorem_static` | yes, one application | **win (baseline)** |
| C2 | re-prove from scratch | the engine, rebuilt | yes, but dramatizes | reject (relitigation) |
| C3 | collapse feeds the verdict | `verdict` | yes, the wall | **reject (audit d, SERIOUS)** |

## Winning candidate: C1

### Definitions and obligations (cite README §2.1–§2.2)

```lean
-- ws2_collapse_inherited := P1.Core.ws2_import_theorem_static (symDest …)   (C1)
```

**Proof architecture.** Direct application; the only content is that `symDest hinf hcar attends` is a well-typed `PkObj κ`-coalgebra (README §2.2, whose well-definedness `mk {y | sym x y} < κ` comes from `hcar` via `Cardinal.mk_subtype_le`). The subsingleton conclusion is the imported engine's, verbatim. **Dependencies:** imported `ws2_import_theorem_static`; `symDest` (WS1/README). **WS2 is one theorem; it consumes only the import and the carrier, and delivers only the baseline.**

## Outcome classes (per charter §5)

- **Baseline (the WS2 payoff):** `ws2_collapse_inherited` transcribed as the imported engine, stated as the ground the import acts against, no verdict hanging on it.
- **No fork.** WS2 has no OBSTRUCTED/PARTIAL branch: it is transcription, near-certain by construction. The only failure is a DISCIPLINE breach (relitigation or a verdict hinging on it), which the review catches.
- **Strip test.** Delete "collapse / the One / import / baseline" and it is *"a behaviorally-identified atomless `PkObj κ`-coalgebra is a subsingleton, by `ws2_import_theorem_static`"*, the imported engine verbatim. No name is a term.

## Deliverable

`program-2/series-0/formal/P2S0/ws2.lean`: `import P1`; `ws2_collapse_inherited` as the single application of `P1.Core.ws2_import_theorem_static` to `symDest`. **WS2 is baseline; no verdict hinges on it (audit d).** Axiom check: `#print axioms ws2_collapse_inherited` reduces to `ws2_import_theorem_static`'s standard three. **The collapse is inherited, in one line, and the audit certifies the verdict never reads it.**
