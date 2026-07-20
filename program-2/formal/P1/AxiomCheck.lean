/-
`program-2/formal/P1/AxiomCheck.lean`

Imports the whole P1 foundation and emits a `#print axioms` record for every headline carrier theorem. The
bar: sorry-free and no new axioms — every headline rests only on Mathlib's standard three, `propext` /
`Classical.choice` / `Quot.sound`, with no `sorryAx` and no custom `axiom`. Because `P1.Core` / `P1.Reader`
are Series 12 WS1 / WS2 transcribed verbatim, a clean pass here reproduces the Series 12 axiom record for the
transcribed subset.
-/
import P1

-- Core (from Series 12 WS1) — the base carrier: collapse engine, import theorem, dichotomy,
-- the labelled import test, the diagonal and free residue, the reification section and tower, the opening.
#print axioms P1.Core.ws1_atomless_bisim
#print axioms P1.Core.ws2_import_theorem
#print axioms P1.Core.ws2_import_theorem_static
#print axioms P1.Core.ws3_atomless_distinct_is_import
#print axioms P1.Core.ws4_labelLoop_not_recoverable
#print axioms P1.Core.ws1_no_self_total_hold
#print axioms P1.Core.ws2_residue_free
#print axioms P1.Core.ws1_reify_injective
#print axioms P1.Core.ws3_reify_preserves_SHNE
#print axioms P1.Core.ws3_order_endogenous
#print axioms P1.Core.ws1_two_halves
#print axioms P1.Core.ws1_shape_coincidence
#print axioms P1.Core.ws1_coincidence_not_identity_witness

-- Reader (from Series 12 WS2) — the bounded reader and the reader-load-bearing plurality (PR1-S2 fix).
#print axioms P1.Reader.ws2_many_general
#print axioms P1.Reader.ws2_many_witness
#print axioms P1.Reader.ws2_attention_makes_real
#print axioms P1.Reader.ws2_reification_loadbearing
#print axioms P1.Reader.ws_witness_rank_noninjective
#print axioms P1.Reader.ws2_no_import_is_one
#print axioms P1.Reader.ws2_distinction_free
