# Series 9 — Axiom check log

**The committed record of `#print axioms` over every Series 9 headline, and — the single most important
record (protocol §C, charter §4.1) — the unfolded proof term of the spine, confirming it is a diagonal
fixed-point contradiction and NOT a bisimulation / behavioral identity.**

Run: `lake build Series9.AxiomCheck` (see `formal/Series9/AxiomCheck.lean`). Toolchain
`leanprover/lean4:v4.15.0`, Mathlib `v4.15.0`. Every headline below reduces to Mathlib's standard three
axioms `[propext, Classical.choice, Quot.sound]` — no `sorry`, no custom axiom. The whole package
(`lake build`: Series7 + Series8 + Series9) builds clean, sorry-free, warning-free.

---

## THE COINCIDENCE CHECK (the reason the series exists) — PASSED

`#print ws1_no_self_total_hold` yields the proof term:

```
theorem Series9.WS1.ws1_no_self_total_hold.{u} : ∀ {κ : Cardinal.{u}} {X : Type u} (dest : X → PkObj κ X)
  (insp : Hold dest → HoldPred dest), ¬∃ t, SelfTotal insp t :=
fun {κ} {X} dest insp a =>
  Exists.casesOn a fun t ht =>
    let_fun h := ht t;                     -- h : insp t t ↔ ¬ insp t t   (the self-total equation at the diagonal point t)
    let_fun np := fun hp => h.mp hp hp;    -- np : ¬ insp t t
    np (h.mpr np)                          -- False
```

This is a **pure Cantor/Lawvere diagonal fixed-point contradiction**: it instantiates the self-total
equation `ht` at the diagonal point `t` itself, obtains `insp t t ↔ ¬ insp t t`, and derives `False` by
the standard `p ↔ ¬p` argument. It references **only** `insp`, `Iff.mp`, `Iff.mpr`, and
`Exists.casesOn`. It contains:

- **NO** `IsBisim`, **NO** `IsBisimL`
- **NO** `BehaviorallyIdentified`, **NO** `BehaviorallyIdentifiedL`
- **NO** `ws1_symmetric_states_bisimilar`, **NO** `hneRel`, **NO** `ws1_atomless_bisim`
- **NO** `SReaches`, **NO** `SHNE`, no relational-identity machinery of any kind

**Verdict: the spine is genuinely a fixed-point contradiction, INDEPENDENT of relational identity. The
Series 8 coincidence is NOT re-hit.** This is the whole repair of Series 8, confirmed at the proof-term
level. `ws1_diagonal_not_bisim` states the orthogonality as a theorem (the spine holds on any carrier,
whether relational identity is trivial there or not); `ws7_coincidence_check` contrasts the spine's shape
(denies a fixed point) with `ws1_symmetric_states_bisimilar`'s shape (produces a bisimulation from
symmetry) in one statement.

```
'Series9.WS1.ws1_no_self_total_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Full axiom pass (every headline reduces to the standard three)

### WS1 — the hold-reflexive carrier and the diagonal spine
- `ws1_no_self_total_hold` — [propext, Classical.choice, Quot.sound]
- `ws1_insp_not_surjective` — [propext, Classical.choice, Quot.sound]
- `ws1_diagonal_not_bisim` — [propext, Classical.choice, Quot.sound]
- `ws1_unrestricted_carrier_inconsistent` — [propext, Classical.choice, Quot.sound]
- `ws1_holdreflexive_not_selfloop` — [propext, Classical.choice, Quot.sound]
- `ws1_hold_forced` — [propext, Classical.choice, Quot.sound]
- `ws1_symmetric_states_bisimilar` (the transcribed negative touchstone) — [propext, Classical.choice, Quot.sound]

### WS2 — the residue breaks the collapse from one position
- `ws2_residue_distinct`, `ws2_residue_free`, `ws2_residue_is_import`, `ws2_from_one_position`,
  `ws2_distributed_special_case` — all [propext, Classical.choice, Quot.sound]

### WS3 — the re-diagonalization engine
- `ws3_redi_no_leaf` (NL), `ws3_redi_not_function` (NF), `ws3_dynamics_forced`, `ws3_order_endogenous`,
  `ws3_imported_index_refuted` — all [propext, Classical.choice, Quot.sound]

### WS4 — the tower and depth
- `ws4_new_blind_spot`, `ws4_depth_is_tower`, `ws4_reaches_is_trace`, `ws4_depth_grows_witness` — all
  [propext, Classical.choice, Quot.sound]

### WS5 — the monotonicity fork (Refuted-universal / Partial)
- `ws5_retention_refuted`, `ws5_kill_condition`, `ws5_monotone_on_fresh`, `ws5_verdict_justified` — all
  [propext, Classical.choice, Quot.sound]

### WS6 — the heuristic ceiling / retraction
- `ws6_provable_core`, `ws6_monotonicity_retracted` — all [propext, Classical.choice, Quot.sound]

### WS7 — the audit, the coincidence check, and the typed verdict
- `ws7_audit`, `ws7_verdict`, `ws7_verdict_eq`, `ws7_coincidence_check`, `ws7_no_coincidence`,
  `ws7_no_monotonicity_by_fiat`, `ws7_freeness_not_defined_in`, `ws7_carrier_genuine`,
  `ws7_strip_ledger` — all [propext, Classical.choice, Quot.sound]

`ws7_verdict = Series9Verdict.selfReferenceEstablished` by `rfl` on the discharged `Audit` (whose
flagship field `diagonalNotBisim` carries the spine's independence), so the verdict cannot be hand-set.
