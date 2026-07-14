# WS2, The mint and the transport theorem (near-certain)

**Design doc. Series 13. Owns: the MINT `mintL` (from any inspection, the labelled coalgebra whose residue-position broadcasts that inspection's residue and whose reference-position broadcasts a fixed content), and TWO named obligations, the TRANSPORT `ws2_mint_lands_in_opening` (for every inspection the minted label fails `Recoverable`, the engine the diagonal `ws2_residue_distinct`) and the EXOGENEITY `ws2_mint_exogenous` (the mint's operation is non-recoverable from the plain relating: `plainOf ∘ mintL` is constant in the inspection, yet the mint is not, so the plain relating cannot perform it). WS2 is the guard against the mint smuggled below the plain line (discipline 3).**

*Series 13 is standalone; the diagonal and residue (`residue`, `diag`, `ws2_residue_distinct`, `ws1_no_self_total_hold`), the labelled lift and import test (`LkObj`, `IsBisimL`, `plainOf`, `Recoverable`, `toPk`), the collapse-engine bisimulation (`IsBisim`, `plainOf_labelLoop_true_bisim` as the template), and the non-identity witness (`ws1_coincidence_not_identity_witness`) are transcribed and cited from `spec/README.md`. WS2 DEFINES the mint (README §2.7) and proves the two obligations. It depends on WS1's orders only for the codomain type `Lab dest`; the transport and exogeneity themselves are order-free facts. The two signature risks: the mint recoverable from the plain relating (discipline 3, foreclosed by `plainOf ∘ mintL` constant), and a transport that does not consume the diagonal (foreclosed by routing through `ws2_residue_distinct`).*

## The object at stake

The charter's WS2 (§2): construct the mint and prove the transport theorem, every inspection's minted label non-recoverable, the engine the diagonal (recovering the minted label would realize what `ws2_residue_free` proves unrealizable); and prove the exogeneity, the mint consuming inspective data above the plain layer, its operation non-recoverable from the plain relating, so no contradiction with Series 07 threatens and the theorem says so. This is the forced-for-all paying for the exists-satisfying: the residue, non-recoverable for EVERY inspection, funds an import (a witnessed non-recoverable labelled distinction) for every inspection. The diagonal, being total, is a factory for imports.

**Ambient theory.** `spec/README.md` §2.2 (import test), §2.3 (diagonal + residue), §2.6 (the codomain `Lab dest`), §2.7 (the mint).

## The mint (README §2.7), fixed

```lean
/-- **The mint.** Carrier `MCar dest = ULift Bool`; label `HoldPred dest`. Region `⟨true⟩` = residue-position,
    self-loops broadcasting `residue insp`; region `⟨false⟩` = reference-position, self-loops broadcasting the
    fixed content `insp h₀`. Both successor sets are singletons (`mk = 1 < κ`), so `mintL insp : Lab dest`. -/
noncomputable def mintL {X} (dest : X → PkObj κ X) (h₀ : Hold dest) (insp : Insp dest) : Lab dest :=
  fun i => match i with
    | ⟨true⟩  => toPk hinf {(residue insp, ⟨true⟩)}
    | ⟨false⟩ => toPk hinf {(insp h₀,       ⟨false⟩)}

@[simp] lemma mintL_true  (insp) : (mintL dest h₀ insp ⟨true⟩).1  = {(residue insp, ⟨true⟩)} := rfl
@[simp] lemma mintL_false (insp) : (mintL dest h₀ insp ⟨false⟩).1 = {(insp h₀,       ⟨false⟩)} := rfl

/-- **The plain projection is CONSTANT in the inspection.** `plainOf (mintL insp) i = {i}` for every insp,
    the ground of exogeneity: the plain relating is blind to which inspection was minted. -/
@[simp] lemma plainOf_mintL (insp) (i) : (plainOf (mintL dest h₀ insp) i).1 = {i} := by
  cases i using ULift.rec with | up b => cases b <;> simp [plainOf, PkMap, mintL, Set.image_singleton]
```

## Candidates (transport)

### T-C1, transport by the residue/reference diagonal separation (the lead)

```lean
/-- **THE TRANSPORT THEOREM.** For every inspection, the minted labelled coalgebra fails `Recoverable`.
    Engine: the diagonal. `⊤` (the all-related relation) is a plain-bisimulation of `plainOf (mintL insp)`
    (every state self-loops), but it is NOT a label-bisimulation, because at the pair `(⟨true⟩, ⟨false⟩)`
    the residue-position's label `residue insp` must match the reference-position's `insp h₀` (`ws2_residue_distinct`),
    and it cannot: `residue insp ≠ insp h₀`. -/
theorem ws2_mint_lands_in_opening {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) (insp : Insp dest) :
    Opening (@Recoverable κ (MCar dest) (HoldPred dest)) (mintL dest h₀ insp) := by
  intro hrec
  -- ⊤ is a plain-bisim (plainOf (mintL insp) is i ↦ {i}, all states self-loop, mirror plainOf_labelLoop_true_bisim)
  have hplain : IsBisim (plainOf (mintL dest h₀ insp)) (fun _ _ => True) := …
  have hlab : IsBisimL (mintL dest h₀ insp) (fun _ _ => True) := hrec _ hplain
  -- forward at (⟨true⟩, ⟨false⟩): ⟨true⟩'s edge (residue insp, ⟨true⟩) must match a ⟨false⟩ edge with equal label
  obtain ⟨hf, _⟩ := hlab ⟨true⟩ ⟨false⟩ trivial
  obtain ⟨q, hq, hfst, _⟩ := hf (residue insp, ⟨true⟩) (by simp)
  rw [mintL_false, Set.mem_singleton_iff] at hq; subst hq
  exact (ws2_residue_distinct dest insp h₀).symm hfst    -- residue insp = insp h₀ contradicts ws2_residue_distinct
```
The transport, mirroring `ws4_label_survives_quotient` exactly but with the label carrying the residue: the separation between the residue-position and the reference-position is `residue insp ≠ insp h₀`, which is `ws2_residue_distinct dest insp h₀`, itself `ws1_no_self_total_hold` at `h₀` (`residue insp h₀ = ¬ insp h₀ h₀ ≠ insp h₀ h₀`).

- **Ambient:** `Recoverable`, `IsBisim`, `IsBisimL`, `plainOf`, `ws2_residue_distinct`, the `⊤`-plain-bisim template `plainOf_labelLoop_true_bisim`.
- **Success condition (Dual, transport):** `∀ insp, ¬ Recoverable (mintL insp)`, the proof consuming `ws2_residue_distinct` (hence the diagonal `ws1_no_self_total_hold`).
- **Failure mode:** *non-recoverability by a shortcut that does not consume the diagonal.* Foreclosed: the ONLY step refuting label-bisimulation is `ws2_residue_distinct dest insp h₀`; strip it and the proof is gone. **Winner.**

**Paper triage.** Decidable: `plainOf (mintL insp)` is `i ↦ {i}` (every state self-loops), so `⊤` is a plain-bisim exactly as `labelLoop`; the label separation at `(⟨true⟩,⟨false⟩)` is `residue insp = insp h₀`, refuted by `ws2_residue_distinct`. Universal in `insp`. **Winner.**

### T-C2, transport stated as `∀ insp` at once (the forced-for-all packaging)

```lean
theorem ws2_transport_forall {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∀ insp : Insp dest, ¬ Recoverable (mintL dest h₀ insp) :=
  fun insp => ws2_mint_lands_in_opening dest h₀ hinf insp
```
The forced-for-all packaging: the residue is non-recoverable for EVERY inspection, so the mint lands in the opening for every inspection, the universal fact funding existential imports.

- **Success condition (Dual):** the `∀`-form typechecks from T-C1. **Winner (the forced-for-all statement).**

### T-C3, transport via `ws2_residue_free` at the content level (the alternative engine)

```lean
theorem ws2_transport_via_free {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) (insp : Insp dest) :
    ¬ ResidueRecoverable insp → ¬ Recoverable (mintL dest h₀ insp)
```
Route transport through `ws2_residue_free` (`¬ ResidueRecoverable`) rather than `ws2_residue_distinct`, to make the strip test land on `ws2_residue_free` verbatim.

- **Ambient:** `ws2_residue_free`, `ResidueRecoverable`.
- **Note:** `ws2_residue_free` and `ws2_residue_distinct` are siblings (both from `ws1_no_self_total_hold`); T-C1's separation `residue insp ≠ insp h₀` is `ws2_residue_distinct` at `h₀`, which is the specific instance `ws2_residue_free` proves in aggregate. **Winner as the alternative-engine framing;** the build ships T-C1 (direct, `decide`-clean) and notes T-C3 as the strip-test-faithful reading (the engine IS the free residue). Either satisfies the strip test.

### T-C4, transport by asserting non-recoverability directly (the shortcut sin)

```lean
theorem ws2_transport_asserted (insp) : ¬ Recoverable (mintL dest h₀ insp) := by
  sorry   -- or: unfold Recoverable and close by a decision procedure that does not touch residue
```
Assert non-recoverability by a route that never mentions the residue (e.g. a cardinality or typing shortcut).

- **Failure mode:** *transport that does not consume the diagonal, SERIOUS (protocol §0.3, the transport check).* If the proof does not run through `ws2_residue_distinct`/`ws2_residue_free`, the payoff strips to something OTHER than the diagonal fact and the "factory" claim is unearned. **Reject.** T-C1 makes the diagonal load-bearing: delete `ws2_residue_distinct` and there is no proof.

## Candidates (exogeneity)

### E-C1, exogeneity by plain-projection constancy + mint non-constancy (the lead)

```lean
/-- **THE EXOGENEITY.** The mint's operation is non-recoverable from the plain relating: two inspections the
    plain relating cannot tell apart (their minted coalgebras share the SAME plain projection) receive
    DIFFERENT mints. So no function of the plain relating alone can reproduce the mint; it genuinely consumes
    inspective data above the plain layer, and no contradiction with Series 07 threatens. -/
theorem ws2_mint_exogenous {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∃ insp₁ insp₂ : Insp dest,
        plainOf (mintL dest h₀ insp₁) = plainOf (mintL dest h₀ insp₂)     -- plain relating BLIND to the difference …
      ∧ mintL dest h₀ insp₁ ≠ mintL dest h₀ insp₂ := by                   -- … yet the mint SEES it
  refine ⟨(fun _ _ => True), (fun _ _ => False), ?_, ?_⟩
  · funext i; cases i using ULift.rec with | up b => cases b <;> simp [plainOf_mintL]  -- both i ↦ {i}
  · intro he; -- residue ⊤i = ⊥ ≠ ⊤ = residue ⊥i, so the ⟨true⟩ labels differ, so the mints differ
    have := congrArg (fun d => (d ⟨true⟩).1) he
    simp [mintL_true, residue, diag] at this
    exact absurd (this h₀ …) …   -- ⊥ h₀ = ⊤ h₀ is False
```
The exogeneity witness is exactly the `ws1_coincidence_not_identity_witness` pair (`⊤i`, `⊥i`), whose residues are `⊥`, `⊤` (distinct). Their plain projections coincide (both `i ↦ {i}`), so the plain relating cannot distinguish them; their mints differ (the `⟨true⟩` labels are the distinct residues). A mint the relating could perform on itself would have to agree on `⊤i` and `⊥i` (indistinguishable plainly) yet the mint separates them, so the mint is not a function of the plain relating: exogenous.

- **Ambient:** `plainOf_mintL`, `ws1_coincidence_not_identity_witness` (the residue-distinct pair), `residue`/`diag`.
- **Success condition (Dual, exogeneity):** the witnessed pair with equal plain projection and unequal mint, a genuine proof term.
- **Failure mode:** *exogeneity a docstring gloss (discipline 3).* Foreclosed: `ws2_mint_exogenous` is an existential with a constructed witness and two proved conjuncts, not an assumption. **Winner.**

**Paper triage.** Decidable: `plainOf (mintL insp)` is `i ↦ {i}` for all insp (`plainOf_mintL`), so equal for `⊤i, ⊥i`; `residue ⊤i = ⊥ ≠ ⊤ = residue ⊥i` (evaluate at `h₀`), so the `⟨true⟩` labels and hence the mints differ. **Winner.**

### E-C2, exogeneity as "no plain-recovery function" (the sharp corollary)

```lean
theorem ws2_mint_not_plain_function {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ g : (MCar dest → PkObj κ (MCar dest)) → Lab dest,
        ∀ insp : Insp dest, mintL dest h₀ insp = g (plainOf (mintL dest h₀ insp)) := by
  rintro ⟨g, hg⟩
  obtain ⟨insp₁, insp₂, hplain, hne⟩ := ws2_mint_exogenous dest h₀ hinf
  exact hne (by rw [hg insp₁, hg insp₂, hplain])
```
The sharp form: there is NO function `g` from the plain relating that reproduces the mint. Immediate from E-C1 (a `g` would agree on `⊤i, ⊥i` via their equal plain projection, contradicting the unequal mints).

- **Success condition (Dual):** the impossibility typechecks from E-C1. **Winner (the sharp corollary, the "mint the relating could perform on itself" impossibility as a theorem).**

### E-C3, exogeneity as label-separation within one mint (the conflation trap)

```lean
theorem ws2_exo_within (insp) : ¬ Recoverable (mintL dest h₀ insp)   -- = transport, relabeled "exogeneity"
```
State exogeneity as the mint's OWN non-recoverability (i.e. re-use the transport theorem under the exogeneity name).

- **Failure mode:** *conflating transport with exogeneity.* Transport says the OUTPUT is an import; exogeneity says the MAP is not a function of the plain relating. They are different obligations (charter §4.c, protocol §0.6), and collapsing them would leave exogeneity unproved. **Reject.** E-C1/E-C2 prove the map-level fact (the plain relating cannot perform the mint), which transport does not.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| T-C1 | transport via residue/reference separation | `ws2_residue_distinct`, `Recoverable` | yes, `⊤` plain-bisim not label-bisim | **win (transport)** |
| T-C2 | forced-for-all packaging | T-C1 | yes, `∀`-form | **win (forced-for-all)** |
| T-C3 | transport via `ws2_residue_free` | `ws2_residue_free` | yes, sibling engine | **win (strip-faithful)** |
| T-C4 | non-recoverability asserted | — | yes, no diagonal | **reject (SERIOUS, no engine)** |
| E-C1 | plain projection constant, mint not | `plainOf_mintL`, residue-distinct pair | yes, evaluate at `h₀` | **win (exogeneity)** |
| E-C2 | no plain-recovery function | E-C1 | yes, corollary | **win (sharp)** |
| E-C3 | transport relabeled exogeneity | — | yes, conflation | reject (unproved) |

## Winning candidates: T-C1 (transport) + T-C2 (forced-for-all) + E-C1 (exogeneity) + E-C2 (sharp)

### Definitions and obligations (cite `spec/README.md` §2.2–§2.3, §2.7)

```lean
namespace Series13.WS2
-- Recoverable, IsBisim, IsBisimL, plainOf, ws2_residue_distinct, ws2_residue_free, ws1_no_self_total_hold,
-- ws1_coincidence_not_identity_witness, toPk, Opening — transcribed (README §6). Insp, Lab, MCar — from WS1.
-- mintL, mintL_true, mintL_false, plainOf_mintL (README §2.7)
-- ws2_mint_lands_in_opening (T-C1), ws2_transport_forall (T-C2), ws2_mint_exogenous (E-C1),
-- ws2_mint_not_plain_function (E-C2)
```

**Proof architecture.** The mint broadcasts the residue at `⟨true⟩` and the reference content at `⟨false⟩`; its plain projection is the insp-independent `i ↦ {i}` loop (`plainOf_mintL`). TRANSPORT (T-C1): `⊤` is a plain-bisim (all states self-loop, template `plainOf_labelLoop_true_bisim`), but not a label-bisim, because the residue-position and reference-position are label-separated by `ws2_residue_distinct dest insp h₀`; so `¬ Recoverable (mintL insp)` for EVERY insp (T-C2). EXOGENEITY (E-C1): the residue-distinct pair `⊤i, ⊥i` share a plain projection (`plainOf_mintL`) but receive distinct mints (distinct `⟨true⟩` labels), so no plain-relating function reproduces the mint (E-C2). **Dependencies:** `ws2_residue_distinct` / `ws1_no_self_total_hold` (the diagonal, transport's engine, README §2.3); `plainOf_mintL` (exogeneity's ground); `ws1_coincidence_not_identity_witness` (the witness pair). **The transport runs on the diagonal and the exogeneity on the plain-projection constancy, neither assumed.**

## Outcome classes (per charter §5)

- **Dual (the WS2 payoff):** T-C1/T-C2 (transport, forced-for-all, via the diagonal) and E-C1/E-C2 (exogeneity, the mint above the plain layer, a proof term). Every within-generated opening manufactures a without-required one; the diagonal is a factory for imports.
- **Partial (pre-registered):** if transport held only per-inspection (some insp with a recoverable mint), or exogeneity only for one pair without the sharp corollary. Foreclosed: transport is `∀ insp` and exogeneity carries E-C2.
- **Refuted (pre-registered, would reshape the series):** if `mintL insp` were provably Recoverable for some insp, the diagonal would not fund the import there; foreclosed by `ws2_residue_distinct`.
- **Strip test.** Delete "mint / factory / transport / exogeneity" from `ws2_mint_lands_in_opening` and it is the bare fact *"for every inspection, the two-region labelled coalgebra broadcasting the residue and the reference-content is not `Recoverable`, because `residue insp ≠ insp h₀` at `h₀` (`ws2_residue_distinct`)"*, a `Recoverable`/diagonal fact, exactly protocol §0.3's target. Delete the same from `ws2_mint_exogenous` and it is *"two inspections with equal plain projection and unequal minted coalgebra"*, a `plainOf`-constancy fact. Both survive as their named facts; no name is a term.

## Deliverable

`series-13/formal/Series13/ws2.lean`: the transcribed carrier + diagonal + import test (README §6); `mintL`, `mintL_true`, `mintL_false`, `plainOf_mintL` (README §2.7); `ws2_mint_lands_in_opening` (T-C1), `ws2_transport_forall` (T-C2), `ws2_mint_exogenous` (E-C1), `ws2_mint_not_plain_function` (E-C2). **WS2 depends on WS1's orders for `Lab dest`; the transport and exogeneity are order-free. WS3's connection and WS4's defect are about THIS mint.** Axiom check: `#print axioms ws2_mint_lands_in_opening` reduces through `ws2_residue_distinct`/`ws1_no_self_total_hold` to the standard three; `ws2_mint_exogenous` through `plainOf_mintL` and the residue-distinct pair. **The mint lands in the opening (transport, via the diagonal) exogenously (the plain relating cannot perform it): the forced-for-all residue funds an exists-satisfying import for every inspection, and the mint stays above the plain line.**
