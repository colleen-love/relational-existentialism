-- `Series13` - the live Lean root (Spec Series 13).
--
-- Series 13 is WHOLLY STANDALONE (charter §1): the two prior results it presupposes and names are Series 07
-- (the import theorem) and Series 12 WS1 (the shape-coincidence and non-identity), transcribed (not imported)
-- into `series-13/formal/Series13/wsNN.lean` and re-namespaced `Series13.WSNN`. Nothing is imported from
-- `series-07/`, `series-12/`, `archive/`, or any other series. The full build compiles `sorry`-free with no
-- custom axioms; every result rests only on Mathlib's standard three (`propext` / `Classical.choice` /
-- `Quot.sound`), recorded by `AxiomCheck.lean`.
--
-- HEADLINE. The FIT, drawn as an adjoint pair and left open. WS1 fixes the two ORDERS (on inspections, by
-- residue; on labelled coalgebras, residue-position covariant and reference-position antitone), each proved
-- non-trivial. WS2 builds the MINT and proves the transport (every inspection's minted label fails
-- `Recoverable`, by the diagonal) exogenously (the mint above the plain layer). WS3 builds the ADJOINT and
-- the `GaloisConnection`, with a non-identity round trip (the interior strictly below the identity). WS4
-- tests mintability UP TO EQUIVALENCE: DUAL on carriers with a second hold (an import order-equivalent to no
-- mint, the exclusion structural), TOTAL on the degenerate single-hold carrier. WS5 computes the verdict as
-- a function of which, folds in the audit, and leaves the fork open.

-- WS1 - the two orders (the knot), each non-trivial (`ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial`).
import Series13.ws1
-- WS2 - the mint, the transport (`ws2_mint_lands_in_opening`) and the exogeneity (`ws2_mint_exogenous`).
import Series13.ws2
-- WS3 - the adjoint, the `GaloisConnection` (`ws3_galois`) and the non-identity round trip (`ws3_roundtrip_not_identity`).
import Series13.ws3
-- WS4 - mintability up to `≈`: the defect (`ws4_mint_not_surjective`) or TOTAL (`ws4_mint_essentially_surjective_degenerate`).
import Series13.ws4
-- WS5 - the verdict as a function of WS1-WS4 (`ws5_verdict`, computed) and the folded-in audit.
import Series13.ws5
