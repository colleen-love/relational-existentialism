**Classification: Partial.**

The WS4 design (v3) aimed for **Discharged** — its §6 defines discharge around Layer C (weak-pullback preservation, `WQRel_le_comp`, step 6), plus `wq_reduces_to_pk` (step 16) and the full step-20 `ws4_resolved` bundle. The Lean file (`ws4.lean`) does **not** prove those. So the target the design registered as its discharge bar is not met, and the file is honest about this: the top-level theorem is named `ws4_graded_coherence_Luk`, deliberately *not* `ws4_resolved`, so an importer can't mistake the delivered coherence for the registered discharge.

**What is actually proved (the discharged fragment):**
- Layers A–B: the enriched functor `W_Q` as a QPF, terminal coalgebra via `Cofix`, Lambek, bisimulation = identity, behavioural equivalence = identity (`νWQ_terminal`, `wqLambek`, `wq_bisim_eq`, `wq_bisim_behavioural`) — criteria (i)–(iii) for the enriched carrier.
- Layer D multiplication coherence: `wqAlg_pentagon` (the [REV-B]-corrected join-of-destructors form), `wqAlg_unit`, `wq_reflects_part`.
- The concrete non-idempotent witness `Łₙ` as a `DivisibleQuantale`, with `tensor_section` proved constructively and `ws4_quantitative_witness` certifying non-idempotence for n ≥ 2 (the tripwire that grading is genuinely quantitative, not a frame in disguise).
- `weight_split`: the pointwise ⊗-factorization that Layer C would consume — isolated and proved.

**What is left open (the precise obstruction):**
- **Layer C / step 6** (`WQRel_le_comp`, weak-pullback preservation) is registered as a *typed hole* (`WQPreservesWeakPullback`), not asserted. This was the design's own "one genuinely new proof… attack first, may resist." The obstruction is made precise: the pointwise residuation (`weight_split`) is done; what remains is the **global witness assembly** — building a single weighted graph whose fibre-sup projections match, where the naive composite weight `wR(x,y) ⊗ wS(y,z)` fails to project unless the middle's outgoing weight is 1 (the non-normalization difficulty).
- `wqAlg_join` (step 13 associativity), `wq_reduces_to_pk` (step 16 Bool-reduction), and `noStrictLaw` are absent.
- The §8 negative theorem `ws4_no_quantitative_grading` is also unproved — so the step-6 fork is genuinely open, decided in **neither** direction. This is why the outcome is Partial and not Impossibility proved: the design specified F6 as an Impossibility-proved branch, but no impossibility is established.

**Against the charter:** this is exactly the class the charter pre-registered for WS4 — the two ratification duties pinned on it (WS2-inherited weak-pullback preservation, WS3-pinned weak-law persistence/canonicity) are precisely what remain unclosed. Criterion (iv) therefore stays **Partial**, unchanged: content present, multiplication coherence proved, canonicity open.

**Methodology note (per §5, not a reframe):** report WS4 as Partial with Layer C as a named typed obligation carrying its made-precise obstruction (global witness assembly under non-normalized composite weights); route the still-open weak-pullback-preservation duty and the canonical-weak-law question forward (the `(F, κ, μ, #Q)` collector duty to WS7, canonicity at the `(Q, κ)` level inherited from WS3). Do **not** report criterion (iv) as closed, and do not let the proved quantitative witness (`Łₙ`) launder the unproved Layer C into looking discharged — the file's naming discipline (`ws4_graded_coherence_Luk` ≠ `ws4_resolved`) already enforces this and should be preserved in the charter's status line.
