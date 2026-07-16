/-
`series-11/formal/Series11/ws3.lean`

WS3 — **No total attention (the bound's engine).** Series 11, the inspection-level diagonal, the cleanest
result of the series, the seed the bound turns on.

`(NT)` no self-total hold exists — a total attention is a self-total hold, forbidden by the diagonal
`ws1_no_self_total_hold`, an Impossibility. `(NL)` attention reads full relata, never leaves
(`ws3_reify_preserves_SHNE`). Bounded-holding derived ENDOGENOUSLY from finitude (the guard against
κ-readmitted, charter §4.4). The bound (EB) and the crown are NOT attempted here — WS4/WS5's.

**Honest scope (protocol §0.5; series-review-1 R1).** `ws3_no_total_attention` is `ws1_no_self_total_hold`
re-read: its proof references NO cardinal, so NT is κ-free — the genuine κ-removal, the bound as a diagonal
fact, not a cardinal fact. Bounded-holding is `att.reads.Finite` (holding), refutable by an unbounded hold,
on a carrier that may be `Infinite X` — not a size ceiling. **R1 correction:** NT is an
INSPECTION-LEVEL diagonal fact — `TotalAttention insp t := SelfTotal insp t` ranges over a single-coalgebra
`Hold dest` with `insp` a FREE parameter, NOT over the `towerN`/`reifyStep` tower (which appears in no NT/EB
term). The "at tower scale" reading is interpretive, tower-independent, as Series 10 Phase E honestly
restated its inspection-level `ws4_close_forbidden`; the machine-checked content is the diagonal over `insp`.

Depends on WS1. Design doc: `series-11/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws1

universe u

namespace Series11.WS3

open Series11.WS1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **D0 — total attention = self-total hold (the pin).** A hold whose reading is the totality of contents
below it — the completed self-inspection. Pinned `:= SelfTotal`, so NT routes through the diagonal, not a
definitional clause. -/
def TotalAttention {X : Type u} {dest : X → PkObj κ X}
    (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop := SelfTotal insp t

/-- **D1 — (NT) THE IMPOSSIBILITY.** No self-total hold exists: a total attention is a self-total hold,
forbidden by the diagonal. The bound's engine. (Inspection-level, `insp` a free parameter; the tower
reading is interpretive, R1.) -/
theorem ws3_no_total_attention {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, TotalAttention insp t :=
  ws1_no_self_total_hold dest insp

/-- **D2 — (NT) is κ-free (the genuine κ-removal).** No cardinal; independent of relational identity. -/
theorem ws3_no_total_attention_kappa_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ws1_diagonal_not_bisim dest insp

/-- **D3 — (NL) attention reads full relata (no leaf).** -/
theorem ws3_attention_reads_full_relata {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) :=
  ws3_reify_preserves_SHNE dest reify h s hs hsucc

/-- **D4 — bounded-holding, endogenous (the κ-readmitted guard).** Every finite attention reads a bounded
part: its reading is finite (`att.fin`), so on an infinite tower it does NOT hold the whole. The bound is
FINITUDE OF HOLDING, refutable by an unbounded hold — NOT a cardinality ceiling on the tower's size. -/
theorem ws3_bounded_holding_endogenous {Q X : Type u} (dest : X → LkObj κ Q X)
    (att : FiniteAttention dest) : att.reads.Finite ∧ ¬ (att.reads = Set.univ ∧ Infinite X) := by
  refine ⟨att.fin, ?_⟩
  rintro ⟨huniv, hinf⟩
  haveI := hinf
  exact Set.infinite_univ (huniv ▸ att.fin)

/-- **D5 — unboundedly many yet never assembled (previewing WS4).** The tower may be infinite, yet no hold
assembles it and no hold's content is the totality: the many is unbounded but never a completed totality. -/
theorem ws3_unbounded_yet_unassembled {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t) ∧ (∀ h : Hold dest, insp h ≠ residue insp) :=
  ⟨ws1_no_self_total_hold dest insp, ws2_residue_distinct dest insp⟩

end Series11.WS3
