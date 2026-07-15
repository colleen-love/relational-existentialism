# WS1-orders, The two orders (the knot)

**Design sub-artifact. Series 13, WS1's concrete construction, consumed by WS2–WS4. Owns: the ONE preorder on inspections (`instLEInsp`) and the ONE preorder on labelled coalgebras (`instLELab`), the paper triage of each candidate against the two questions the protocol fixes (is the order non-trivial? does it admit a monotone mint?), the winning pair with its non-triviality proofs, and the rejected candidates recorded. This is the knot: the whole coda rests on a non-trivial pair of orders admitting a monotone mint and a non-vacuous connection. DISCONNECTED is the pre-registered honest outcome, and this artifact records the precise obstruction that would trigger it (the variance wall).**

*Series 13 is standalone; the residue and diagonal (`residue`, `diag`, `ws2_residue_distinct`, `ws1_no_self_total_hold`), the labelled lift (`LkObj`, `IsBisimL`, `plainOf`, `Recoverable`), and the non-identity witness (`ws1_coincidence_not_identity_witness`) are transcribed and cited from `spec/README.md`. This sub-artifact adds only the two preorders and their certificates. It is the guard against connection-by-fiat (discipline 2): a trivial order makes any monotone pair a Galois connection vacuously, so BOTH orders must be proved non-trivial, and the winning pair must be the one that survives the paper triage below, not the first order that typechecks.*

## The object at stake

The charter's WS1 (§2, the knot): define a preorder on inspections and a preorder on labelled coalgebras such that the mint can be monotone and the connection non-vacuous, with both orders non-trivial (neither discrete `= equality` nor indiscrete `= all-related` on the carriers of interest). The charter fixes only the bar; the orders are design work. The genuine difficulty, made precise here and nowhere hidden, is a **variance wall**:

> The transport theorem (WS2) is universal (`∀ insp`, the minted label fails `Recoverable`) and its only engine is the diagonal, `ws2_residue_distinct`. So the mint must broadcast the RESIDUE `residue insp = diag insp`, which is ANTITONE in `insp` under the pointwise-implication order (if `insp₁ h → insp₂ h` pointwise then `¬ insp₂ h h → ¬ insp₁ h h`, so `residue insp₂ ⊑c residue insp₁`, reversed). A mint that also broadcasts a COVARIANT quantity (any `insp h`) cannot be monotone into a single covariant order. **Reconciling the antitone residue with a monotone mint is the knot**, and a pair of orders that fails to reconcile them is the DISCONNECTED obstruction.

**Ambient theory.** `spec/README.md` §2.3 (diagonal + residue), §2.2 (import test), §2.5–§2.6 (the two orders as fixed), §2.7 (the map pair). Notation: `Insp dest := Hold dest → HoldPred dest`; `c₁ ⊑c c₂ := ∀ h, c₁ h → c₂ h` (content implication); `⊤i := (fun _ _ => True)` (residue `⊥`), `⊥i := (fun _ _ => False)` (residue `⊤`); a distinguished hold `h₀ : Hold dest`.

---

## Part A, the order on inspections

### Candidates

#### A-C1, pointwise implication on inspections (the naive order)

```lean
instance : LE (Insp dest) where le insp₁ insp₂ := ∀ h h', insp₁ h h' → insp₂ h h'
```
Order inspections by pointwise implication of their content assignments (the inclusion order on the graph `{(h,h') | insp h h'} ⊆ Hold × Hold`).

- **Non-trivial?** YES. `⊥i ≤ ⊤i`, `⊥i ≠ ⊤i` (related-unequal, not discrete, needs `h₀`); `¬ (⊤i ≤ ⊥i)` (unrelated, not indiscrete); incomparable singletons exist if `|Hold| ≥ 2`.
- **Admits a monotone mint?** **NO.** The residue is antitone under this order (`ws2_residue_distinct`'s `diag` reverses implication). The residue-broadcasting mint (the only one whose transport is universal) is therefore antitone, not monotone, into any covariant labelled order. **This is the variance wall, and it is the paper-decidable reason A-C1 is rejected.** (An antitone mint could ground an antitone Galois connection, A-C4 below, but the charter and Mathlib `GaloisConnection` are covariant; the residue order A-C2 turns the same map covariant, which is cleaner.) **Reject (variance).**

#### A-C2, by residue (the lead)

```lean
instance instLEInsp : LE (Insp dest) where le insp₁ insp₂ := ∀ h, residue insp₁ h → residue insp₂ h
```
Order inspections by their residue (the diagonal signature): `insp₁ ≤ insp₂ := residue insp₁ ⊑c residue insp₂`. Pullback of `⊑c` along `residue : Insp → HoldPred`.

- **Non-trivial?** YES (proved, `ws1_orders_insp_nontrivial`, below): `residue ⊤i = ⊥` (`¬ True`), `residue ⊥i = ⊤` (`¬ False`), so `⊤i ≤ ⊥i` (`⊥ ⊑c ⊤`) and `⊥i ≰ ⊤i` (`⊤ ⋢c ⊥`, needs `h₀`), and `⊤i ≠ ⊥i` (needs `h₀`). Not discrete (`⊤i ≤ ⊥i`, unequal), not indiscrete (`⊥i ≰ ⊤i`).
- **Admits a monotone mint?** **YES.** Under this order the residue is COVARIANT by construction, so the residue-broadcasting mint is monotone (WS3 `ws3_mint_monotone`). This is precisely the order that dissolves the variance wall on the inspection side. **Winner.**

**Paper triage.** Non-triviality is `decide`/`⊤ ≠ ⊥`-level given `h₀`. Monotone-mint is immediate: `mintL insp ⟨true⟩` broadcasts `residue insp`, and `≤` on inspections IS `⊑c` on residues, so `insp₁ ≤ insp₂ ⟹ mintL insp₁ ⟨true⟩`-label `⊑c mintL insp₂ ⟨true⟩`-label. **Winner.**

#### A-C3, by realized-content set (the reach order)

```lean
instance : LE (Insp dest) where le insp₁ insp₂ := Set.range insp₁ ⊆ Set.range insp₂
```
Order inspections by the set of contents they realize (`Set.range insp = {c | ∃ h, insp h = c}`), the charter's "refinement of inspective reach."

- **Non-trivial?** YES (ranges vary).
- **Admits a monotone mint?** **NO, cleanly.** The mint reads the residue, and the residue is by `ws2_residue_free` the canonical content NOT in `Set.range insp`; range-inclusion does not control the residue (two inspections can share a range and have different residues, or differ in range and share a residue). So `range`-monotone does not give residue-monotone, and the mint is not monotone. **Reject (does not control the residue the mint reads).** Recorded because it is the charter's named candidate and its rejection is instructive: reach is the wrong invariant; the residue is the right one.

#### A-C4, antitone order / order-dual (the polarity route)

```lean
instance : LE (Insp dest) where le insp₁ insp₂ := ∀ h h', insp₂ h h' → insp₁ h h'   -- A-C1 reversed
```
The order dual of A-C1, under which the residue is covariant (so the mint is monotone) but the order is "reversed implication."

- **Non-trivial?** YES (dual of a non-trivial order).
- **Admits a monotone mint?** YES (residue covariant). **Viable, but rejected in favor of A-C2**, because A-C2 orders by exactly the quantity the mint reads (the residue) with no reference to the full content assignment, so its non-triviality and the monotonicity are one-line facts, and the connection's non-identity round trip (WS3) reads off the residue cleanly. A-C4 is A-C2 composed with the antitone `diag`; A-C2 is the honest primitive. Recorded as the equivalent polarity framing.

#### A-C5, discrete / indiscrete (the trivial orders, stated to be rejected)

```lean
instance : LE (Insp dest) where le a b := a = b          -- discrete
instance : LE (Insp dest) where le a b := True           -- indiscrete
```
- **Failure mode:** *connection by fiat (discipline 2), SERIOUS.* Discrete makes the mint monotone vacuously (any function is monotone for `=`) but the Galois connection collapses to an order-iso on singletons; indiscrete makes every pair a Galois connection vacuously. Both are trivial. **Reject.** The non-triviality theorems (`ws1_orders_insp_nontrivial`) are exactly the certificate that the winner A-C2 is neither.

### Winner (inspections): A-C2, by residue

```lean
def Insp {X : Type u} (dest : X → PkObj κ X) : Type u := Hold dest → HoldPred dest
def leC {X} {dest : X → PkObj κ X} (c₁ c₂ : HoldPred dest) : Prop := ∀ h, c₁ h → c₂ h    -- ⊑c

instance instLEInsp {X} (dest : X → PkObj κ X) : LE (Insp dest) where
  le insp₁ insp₂ := leC (residue insp₁) (residue insp₂)
instance instPreorderInsp {X} (dest) : Preorder (Insp dest) where
  le_refl insp := fun h hh => hh
  le_trans a b c hab hbc := fun h hh => hbc h (hab h hh)

/-- **The inspection order is non-trivial (WS1).** Not discrete: `⊤i ≤ ⊥i` with `⊤i ≠ ⊥i`. Not indiscrete:
    `¬ (⊥i ≤ ⊤i)`. Certified on any inhabited-`Hold` carrier. -/
theorem ws1_orders_insp_nontrivial {X} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    (∃ a b : Insp dest, a ≤ b ∧ a ≠ b)              -- not discrete (a related, unequal pair)
  ∧ (∃ a b : Insp dest, ¬ a ≤ b) := by              -- not indiscrete (an unrelated pair)
  refine ⟨⟨(fun _ _ => True), (fun _ _ => False), ?_, ?_⟩, ⟨(fun _ _ => False), (fun _ _ => True), ?_⟩⟩
  · intro h hh; simp [residue, diag] at hh ⊢          -- residue ⊤i = ⊥ ⊑c ⊤ = residue ⊥i
  · intro he; have := congrFun (congrFun he h₀) h₀; simp at this   -- ⊤i ≠ ⊥i at h₀
  · intro hle; have := hle h₀; simp [residue, diag] at this        -- residue ⊥i = ⊤ ⋢c ⊥ = residue ⊤i
```

---

## Part B, the order on labelled coalgebras

The mint's codomain shape is fixed (README §2.6): carrier `MCar dest := ULift Bool`, label `HoldPred dest`, `Lab dest := MCar dest → LkObj κ (HoldPred dest) (MCar dest)`. Region `⟨true⟩` = residue-position; `⟨false⟩` = reference-position. Notation `labSet d y := (d y).1 : Set (HoldPred dest × MCar dest)`.

### Candidates

#### B-C1, raw pointwise successor-set inclusion (the naive order)

```lean
instance : LE (Lab dest) where le d₁ d₂ := ∀ y, labSet d₁ y ⊆ labSet d₂ y
```
- **Non-trivial?** YES (empty vs singleton successor sets).
- **Admits a monotone mint?** **NO.** `mintL insp` has singleton successors, so `mintL insp₁ ≤ mintL insp₂` under `⊆` forces `mintL insp₁ = mintL insp₂`, hence (labels determine) `insp₁ = insp₂`. So the ONLY inspection order making the mint monotone into B-C1 is the DISCRETE one (A-C5), forbidden. **Reject (forces a trivial inspection order).**

#### B-C2, residue-position only, covariant (the coarse order)

```lean
instance : LE (Lab dest) where
  le d₁ d₂ := ∀ p ∈ labSet d₁ ⟨true⟩, ∃ q ∈ labSet d₂ ⟨true⟩, p.2 = q.2 ∧ leC p.1 q.1
```
Compare only the residue-position, covariantly by content-implication.

- **Non-trivial?** YES (residue-labels `⊥` vs `⊤`).
- **Admits a monotone mint?** YES (residue covariant under A-C2). **But:** the connection collapses to an ISOMORPHISM. `readInsp` (WS3) inverts the residue-position exactly (`residue (readInsp c) = c`), so both round trips are the identity in B-C2, the connection is an order-iso, and `ws3_roundtrip_not_identity` FAILS. This is *iso in disguise* (discipline 2), the pre-registered PARTIAL/"coincidence restated." **Reject as the winner; retain as the diagnostic that a genuine connection needs the labelled order to see MORE than the residue-position (the reference-position, B-C3).**

#### B-C3, residue-position covariant + reference-bit antitone (the lead, the diagonal link)

```lean
instance instLELab (h₀ : Hold dest) : LE (Lab dest) where
  le d₁ d₂ :=
      (∀ p ∈ labSet d₁ ⟨true⟩,  ∃ q ∈ labSet d₂ ⟨true⟩,  p.2 = q.2 ∧ leC p.1 q.1)        -- residue-position, covariant
    ∧ (∀ p ∈ labSet d₂ ⟨false⟩, ∃ q ∈ labSet d₁ ⟨false⟩, p.2 = q.2 ∧ (p.1 h₀ → q.1 h₀))   -- reference bit, ANTITONE (d₁,d₂ swapped)
```
Compare the residue-position covariantly AND the reference-position antitonically, but only through its self-application bit at `h₀`. The antitone (order-dual) reference-position is the principled reflection that the reference-content sits at a diagonal (contravariant) position, and it is exactly what lets the residue-broadcasting AND reference-broadcasting mint be monotone while keeping the connection non-iso.

- **Non-trivial?** YES (proved, `ws1_orders_lab_nontrivial`, below): the empty coalgebra `d⊥` and the minted coalgebras give a related-unequal pair and an unrelated pair.
- **Admits a monotone mint?** **YES** (WS3 `ws3_mint_monotone`): residue-position covariant (from A-C2) and reference-bit antitone (`insp₁ ≤ insp₂` gives `residue insp₁ ⊑c residue insp₂`, i.e. `insp₂ h h → insp₁ h h` at every diagonal argument, so at `h₀`: `insp₂ h₀ h₀ → insp₁ h₀ h₀`, exactly the antitone reference-bit condition). **And the connection is NON-iso:** `readInsp` forgets the reference-position, so the interior round trip `mintL ∘ readInsp` cannot restore an arbitrary reference-bit; the interior is strictly below the identity at any coalgebra whose reference-bit at `h₀` violates the diagonal link `residue-label h₀ = ¬ reference-bit` that every minted coalgebra satisfies (WS3 `ws3_roundtrip_not_identity`, WS4 `ws4_mint_not_surjective`). **Winner.**

**Paper triage.** Non-triviality: `decide`-level on the concrete minted/empty coalgebras. Monotone-mint: the residue-position matches A-C2 and the reference-bit condition is the diagonal-argument specialization of A-C2, both one-line. Non-iso: the reference-position is order-relevant but `readInsp`-invisible, so `mintL ∘ readInsp ≠ id` at the diagonal-violating witness. All three paper-decidable. **Winner.**

#### B-C4, label-distinguishing strength relative to `plainOf` (the charter's other candidate)

```lean
instance : LE (Lab dest) where le d₁ d₂ := ∀ R, IsBisimL d₂ R → IsBisimL d₁ R
```
Order by "d₂ is at least as label-distinguishing as d₁" (finer labels = fewer label-bisimulations), the charter's "label-distinguishing strength."

- **Non-trivial?** YES.
- **Admits a monotone mint?** **NOT paper-decidably.** Whether `insp₁ ≤ insp₂` (residue order) implies every `IsBisimL (mintL insp₂)` is an `IsBisimL (mintL insp₁)` depends intricately on how the residue-labels sit inside the bisimulation clauses; it does not reduce to a content-implication and is not obviously monotone. **Reject (the monotone-mint check is not paper-decidable, and the winner B-C3 already secures a genuine connection).** Recorded as the charter's named alternative; a build that wanted B-C4 would owe the monotonicity as a nontrivial lemma, and the risk of it failing (Disconnected) is higher than B-C3.

#### B-C5, discrete / indiscrete (trivial, rejected)

As A-C5. **Reject (connection by fiat).** The non-triviality theorem is the certificate.

#### B-C6, the order reverse-engineered from the mint's output (the fifth fiat mode, B-C3's own exposure)

```lean
instance : LE (Lab dest) where le d₁ d₂ := (readInsp d₁) ≤ (readInsp d₂)      -- pullback of instLEInsp along the adjoint
-- or, equivalently in spirit: any le crafted case-by-case so that mintL is monotone and mintL ∘ readInsp ≠ id,
-- with no independent justification for WHY the ⟨false⟩ position is compared antitonically.
```
The failure mode B-C3 is MOST EXPOSED to, and the one the discrete/indiscrete/iso-in-disguise triad does not name: an order **reverse-engineered from the mint's own output** to force monotonicity and non-iso, as opposed to an order whose variances are fixed by the objects independently of the mint. B-C3 pairs a covariant residue-position with an ANTITONE reference-position; a reviewer is entitled to ask whether that antitone choice is PRINCIPLED (forced by what the reference-content is) or TUNED (chosen because it is what makes `mintL` monotone and `mintL ∘ readInsp` non-identity). If tuned, the connection is genuine only by fiat: the order was solved for the map, and any map would then look adjoint. **Reject the tuned reading; B-C3 survives only if the antitone reference-position is principled**, which the defense below establishes checkably.

- **Failure mode:** *the reverse-engineered order (a fifth connection-by-fiat mode, discipline 2), SERIOUS if tuned.* Distinct from A-C5/B-C5 (trivial orders) and from B-C2 (iso in disguise): here the order is non-trivial and the connection non-iso, but for the WRONG reason, because it was fitted to the mint. **Reject unless the variance is independently justified (the defense).**

**The principled-contravariance defense (stated so the blind reviewer can confirm or break it).** The antitone reference-position of B-C3 is NOT tuned to the mint; it is forced by where the reference-content sits in the diagonal. The claim, checkable without seeing the mint:

> The order-direction of the `⟨false⟩` (reference) position matches the SIGN with which the self-application enters the residue, and that sign is negative, fixed by `residue = diag` (`diag insp h = ¬ insp h h`), independently of `mintL`.

Concretely: the residue `residue insp` depends on the self-application `insp h₀ h₀` NEGATIVELY, `residue insp h₀ = ¬ insp h₀ h₀`. The reference-position broadcasts exactly the self-application data (`insp h₀`, seen at `h₀` as the self-bit `insp h₀ h₀`). A position that enters the diagonal negatively is a CONTRAVARIANT (order-dual) position, so comparing it antitonically is the variance the diagonal dictates, not a tuning knob. The check a reviewer runs: (i) confirm `instLELab`'s `⟨false⟩` clause is antitone (the `d₁, d₂` swap); (ii) confirm the residue's dependence on the `⟨false⟩` data is negation (`residue insp h₀ = ¬ insp h₀ h₀`, definitional, `rfl`); (iii) confirm these two signs AGREE. If they agree, the contravariance is principled (the order-dual tracks the diagonal's sign, which exists before any mint). If a reviewer exhibits an order that makes `mintL` monotone and the connection non-iso WHILE comparing the reference-position covariantly (against the diagonal's sign), B-C3's variance was a coincidence and the fiat charge stands; the design's position is that no such order exists, because covariant-reference would make `mintL` non-monotone at the reference-position (the diagonal's negative sign forces it), which is the variance wall from the other side. **The defense is a claim, not a silence: the reference-position is antitone because the diagonal is negative there, and the reviewer can break it by producing a covariant-reference order that still works.**

### Winner (labelled coalgebras): B-C3, residue-position covariant + reference-bit antitone

```lean
def MCar {X} (dest : X → PkObj κ X) : Type u := ULift.{u} Bool
def Lab {X} (dest) : Type u := MCar dest → LkObj κ (HoldPred dest) (MCar dest)

instance instLELab {X} (dest) (h₀ : Hold dest) : LE (Lab dest) where
  le d₁ d₂ :=
      (∀ p ∈ (d₁ ⟨true⟩).1,  ∃ q ∈ (d₂ ⟨true⟩).1,  p.2 = q.2 ∧ leC p.1 q.1)
    ∧ (∀ p ∈ (d₂ ⟨false⟩).1, ∃ q ∈ (d₁ ⟨false⟩).1, p.2 = q.2 ∧ (p.1 h₀ → q.1 h₀))
instance instPreorderLab {X} (dest) (h₀) : Preorder (Lab dest) where
  le_refl d := ⟨fun p hp => ⟨p, hp, rfl, fun x => x⟩, fun p hp => ⟨p, hp, rfl, fun x => x⟩⟩
  le_trans d₁ d₂ d₃ h12 h23 := …   -- residue-part: compose ⊑c; reference-part: compose implications with the swap

/-- **The labelled order is non-trivial (WS1).** Not discrete: the empty coalgebra `d⊥ := fun _ => toPk hinf ∅`
    is `≤ mintL insp` (vacuously, no edges to dominate) and unequal. Not indiscrete: `mintL ⊥i ≰ mintL ⊤i`,
    because the residue-position labels are `⊤` and `⊥` and `⊤ ⋢c ⊥` at `h₀`. -/
theorem ws1_orders_lab_nontrivial {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    (∃ a b : Lab dest, a ≤ b ∧ a ≠ b)
  ∧ (∃ a b : Lab dest, ¬ a ≤ b) := by
  refine ⟨⟨(fun _ => toPk hinf ∅), mintL dest h₀ (fun _ _ => True), ?_, ?_⟩,
          ⟨mintL dest h₀ (fun _ _ => False), mintL dest h₀ (fun _ _ => True), ?_⟩⟩
  · exact ⟨fun p hp => absurd hp (by simp [toPk]), fun p hp => ⟨p, ?_, rfl, fun x => x⟩⟩   -- d⊥ ≤ mintL ⊤i
  · intro he; …    -- d⊥ ≠ mintL ⊤i (empty ≠ singleton successor at ⟨true⟩)
  · rintro ⟨hres, _⟩; …   -- residue-position: ⊤ ⋢c ⊥ at h₀, so mintL ⊥i ≰ mintL ⊤i
```

---

## The knot resolved (or the DISCONNECTED report)

The winning pair **A-C2 × B-C3** dissolves the variance wall exactly once, and the resolution is the design's whole content, stated so a reviewer can check it by inspection:

1. **The inspection order is by residue** (A-C2), making the residue COVARIANT, so the residue-broadcasting mint's residue-position is monotone.
2. **The labelled order sees the reference-position ANTITONELY** (B-C3, the order-dual on the diagonal position), so the mint's reference-position (the reference-bit at `h₀`, which the residue order controls at the diagonal argument) is also monotone, and the mint is monotone overall.
3. **The reference-position is `readInsp`-invisible**, so the connection is not an isomorphism: the interior round trip forgets the reference-bit, and the defect (WS4) is exactly the reference-bit the mint cannot forge freely (it is forced to `¬ residue-label h₀`, the diagonal link). Non-triviality and non-iso are secured together.

**The DISCONNECTED trigger, pre-registered and precise.** If, at build, the reference-bit antitone condition (B-C3) cannot be made to (a) keep `instLELab` non-trivial AND (b) make `mintL` monotone AND (c) keep the connection non-iso, all three at once, then no non-trivial pair reconciles the antitone residue with a monotone mint, the variance wall stands, and WS1 reports **DISCONNECTED** with the obstruction "the residue is antitone and no non-trivial labelled order makes the residue-and-reference-broadcasting mint monotone without collapsing to an isomorphism (B-C2) or forcing a discrete inspection order (B-C1)." Phase C then builds only this obstruction (README §4), and WS2–WS5 are not built. The paper triage above judges this UNLIKELY (B-C3 passes all three checks on paper), so the pre-registered LEAD is DUAL; but the trigger is named so the build reaches for it before the compiler if B-C3 resists.

## Outcome classes (per charter §5)

- **Dual (the payoff, both orders):** `ws1_orders_insp_nontrivial` and `ws1_orders_lab_nontrivial`, the two orders proved non-trivial, admitting the monotone mint (WS3) and the non-vacuous connection (WS3), with the defect (WS4) certifying non-iso.
- **Disconnected (pre-registered, first-class):** the variance wall stands (B-C3 fails one of the three checks). The obstruction is the result; WS2–WS5 not built.
- **Partial (pre-registered):** an order proves non-trivial but the connection collapses to an iso anyway (B-C2 leaked in) or holds only per-instance. Reported as such.
- **Strip test.** Delete "duality / fit / knot" from `ws1_orders_insp_nontrivial` / `ws1_orders_lab_nontrivial` and they are the bare facts *"the residue order on inspections has a related-unequal pair and an unrelated pair"* and *"the two-region labelled order has a related-unequal pair and an unrelated pair"*, i.e. two non-triviality facts, exactly what discipline 2 demands. No name is a term.

## Build-realization note (`series-review-1.md` SR1-2, closed Fixed)

The `ws1_orders_lab_nontrivial` sketch above witnesses with `mintL dest h₀`, but `mintL` is defined in **WS2** (it consumes the WS1 orders), so a **WS1** theorem cannot name it — a dependency-cycle inconsistency in this design. Realized faithfully across two files, preserving the obligation (a §0.5 certificate that exercises the ANTITONE reference position and the mint points): (i) `ws1_orders_lab_nontrivial` (WS1) gains a third conjunct `∃ a b, a.cT = b.cT ∧ ¬ a ≤ b`, isolating the failure to the reference clause (`⟨⊤,⊥⟩ ⋠ ⟨⊤,⊤⟩`, non-vacuous, with `⟨⊤,⊤⟩` genuinely OFF the diagonal link); (ii) `ws2_mint_nontrivial` (WS2) certifies non-triviality AT MINT POINTS (`mintL ⊤i ≤ mintL ⊥i`, unequal, converse fails). The reference-position non-triviality is exactly the off-link-coalgebra fact the WS3 non-iso and WS4 defect rest on, so the antitone choice is principled, not tuned (B-C6's defense, now a certificate). Recorded in `charter-status.md` (SR1-2 closure).

## Deliverable

`series-13/formal/Series13/ws1.lean`: the transcribed carrier (README §6); `Insp`, `leC`, `instLEInsp`/`instPreorderInsp`, `MCar`, `Lab`, `instLELab`/`instPreorderLab`; `ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial` (the reference-position conjunct added, SR1-2), with `ws2_mint_nontrivial` (WS2) the mint-point half. **WS1 is blocking; the two orders are ambient for WS2–WS4.** Axiom check: both non-triviality theorems reduce through `residue`/`diag` (propositional) to the standard three. **The two orders are the residue order on inspections and the residue-covariant/reference-antitone order on labelled coalgebras, both proved non-trivial, together dissolving the variance wall so the mint is monotone and the connection non-iso, with DISCONNECTED pre-registered and its obstruction (the variance wall) recorded precisely.**
