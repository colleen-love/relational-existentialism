/-
`program-2/series-0/formal/P2S0/AxiomCheck.lean`

Imports the whole Series 0 build and emits a `#print axioms` record for the headline theorem of every
workstream. The bar (protocol §6): sorry-free and no new axioms. A clean pass shows every headline rests only
on Mathlib's standard three, `propext` / `Classical.choice` / `Quot.sound`, with no `sorryAx` and no custom
`axiom`. (`Classical.choice` enters via the cardinal machinery `Cardinal.mk_finset_of_infinite` / `Cardinal.eq`
for `ws1_reification_exists`, via `toPk` / `mk_subtype_le`, and via the imported P1 engine, Mathlib-base
axioms, not new ones. `ws5_verdict_eq` depends on NO axioms.)
-/
import P2S0

-- WS1 - the carrier and the finite-functor reification, the finite bound (audit (a)), and the FIRST OTHER
-- (Charter Extension 1: reification creates a genuine, non-recoverable other on the unified witness)
#print axioms P2S0.ws1_reification_exists
#print axioms P2S0.ws1_finreify_injective
#print axioms P2S0.ws1_bound_is_finite_attention
#print axioms P2S0.ws1_tower_monotone
#print axioms P2S0.ws1_first_other

-- WS2 - the inherited collapse (the imported engine applied to the symmetric relating)
#print axioms P2S0.ws2_collapse_inherited

-- WS3 - the asymmetry of knowing (the knot): direction non-recoverable, passive constitution, two modes
#print axioms P2S0.ws3_direction_not_recoverable
#print axioms P2S0.ws3_passive_constitution
#print axioms P2S0.ws3_active_passive_distinct

-- WS4 - the import seated, quantified, never named
#print axioms P2S0.ws4_import_breaks_baseline
#print axioms P2S0.ws4_import_quantified

-- WS5 - the verdict computed from WS1/WS3/WS4 and the folded-in audit (a)-(e)
#print axioms P2S0.ws5_verdict_eq
#print axioms P2S0.ws5_verdict_not_obstructed
#print axioms P2S0.ws5_verdict_not_partial
#print axioms P2S0.ws5_flags_justified
#print axioms P2S0.ws5_audit_no_ceiling
#print axioms P2S0.ws5_audit_asymmetry_not_label
#print axioms P2S0.ws5_audit_direction_free
#print axioms P2S0.ws5_audit_collapse_inherited
#print axioms P2S0.ws5_audit_import_quantified
