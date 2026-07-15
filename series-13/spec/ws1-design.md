# WS1, The two orders (blocking, the knot)

**Design doc. Series 13, the blocking workstream. Owns: the ORDER ON INSPECTIONS (`instLEInsp`) and the ORDER ON LABELLED COALGEBRAS (`instLELab`), each proved NON-TRIVIAL (neither discrete nor indiscrete on the carriers of interest), so the mint can be monotone and the connection non-vacuous. The concrete construction of both orders, the full candidate triage, and the rejected candidates live in the sub-artifact `spec/ws1-orders-design.md`; this doc frames the WS1 OBLIGATION, selects the packaging, and fixes the contract WS2–WS4 build against. WS1 is blocking: if it lands DISCONNECTED, the whole series reports Disconnected and WS2–WS5 are not built.**

*Series 13 is standalone; the residue and diagonal (`residue`, `diag`, `ws2_residue_distinct`), the labelled lift (`LkObj`, `Recoverable`, `plainOf`), and the non-identity witness (`ws1_coincidence_not_identity_witness`) are transcribed and cited from `spec/README.md` §2. WS1 DEFINES the two preorders (README §2.5–§2.6) and their non-triviality; the concrete orders are `spec/ws1-orders-design.md`. The one signature risk is connection-by-fiat (discipline 2): an order so trivial (discrete or indiscrete) that any monotone pair is a Galois connection vacuously.*

## The object at stake

The charter's spine (§2, the knot): a preorder on inspections and a preorder on labelled coalgebras such that the mint is monotone and the connection non-vacuous, both non-trivial, rejected candidates recorded. This is the series' genuinely uncertain obligation. The design's burden is to state the pair at exactly the right strength: **two preorders, each proved non-trivial, together admitting a monotone mint and a non-iso connection, over the existing transcribed carrier and no new structural machinery.** The pre-registered sin (discipline 2): a trivial order makes the connection hold by fiat.

**Ambient theory.** `spec/README.md` §2.5 (`instLEInsp`), §2.6 (`instLELab`); `spec/ws1-orders-design.md` (the full construction and triage).

## Candidates (framings of the WS1 obligation)

### C1, two non-triviality theorems, one per order (the lead)

```lean
theorem ws1_orders_insp_nontrivial {X} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    (∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b)
theorem ws1_orders_lab_nontrivial {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    (∃ a b : Lab dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest, ¬ a ≤ b)
```
Package non-triviality as, per order, a related-unequal pair (NOT discrete: `≤` is strictly coarser than `=`) and an unrelated pair (NOT indiscrete: `≤` is strictly finer than `⊤`). Discharged on the residue order (A-C2) and the residue/reference order (B-C3) of the sub-artifact.

- **Ambient:** `instLEInsp`, `instLELab`, the witnesses `⊤i`, `⊥i`, `d⊥`, `mintL ⊤i`, `mintL ⊥i` (sub-artifact).
- **Success condition (Dual, WS1 half):** both theorems typecheck; each exhibits a discrete-refuting and an indiscrete-refuting pair.
- **Failure mode:** *connection by fiat (discipline 2).* Foreclosed: the theorems ARE the non-triviality certificate; a discrete or indiscrete order fails one conjunct. **Winner (the non-triviality contract).**

**Paper triage.** Decidable and immediate (sub-artifact Part A/B): `⊤i ≤ ⊥i ∧ ⊤i ≠ ⊥i` and `¬ (⊥i ≤ ⊤i)` for inspections; the empty-vs-minted and minted-vs-minted pairs for labelled coalgebras. **Winner.**

### C2, one bundled "both orders non-trivial" theorem (the aggregate)

```lean
theorem ws1_orders_nontrivial {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ((∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b))
  ∧ ((∃ a b : Lab dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest, ¬ a ≤ b)) :=
  ⟨ws1_orders_insp_nontrivial dest h₀, ws1_orders_lab_nontrivial dest h₀ hinf⟩
```
The conjunction of C1, one object for WS5's audit to consume.

- **Success condition (Dual, WS1 half):** typechecks as the pair of C1 theorems.
- **Failure mode:** none (it is the conjunction). **Winner (the audit-facing aggregate).**

### C3, the orders as Mathlib `Preorder` instances (the structural obligation)

```lean
instance instPreorderInsp {X} (dest) : Preorder (Insp dest) := …
instance instPreorderLab {X} (dest) (h₀) : Preorder (Lab dest) := …
```
The obligation that the two `LE`s are genuine preorders (reflexive, transitive), so Mathlib's `GaloisConnection` (which needs `Preorder`s) applies in WS3.

- **Ambient:** `instLEInsp`, `instLELab`.
- **Success condition (Dual, WS1 half):** both `Preorder` instances typecheck (sub-artifact: reflexivity and transitivity of `⊑c` and of the swapped reference condition).
- **Failure mode:** *a relation that is not transitive.* Foreclosed: `⊑c` is transitive; the reference-bit implication composes with the swap. **Winner (the preorder obligation, WS3's prerequisite).**

### C4, non-triviality via a THREE-element chain (the over-strong framing)

```lean
theorem ws1_orders_insp_chain {X} (dest) (h₀ h₁ : Hold dest) (hne : h₀ ≠ h₁) :
    ∃ a b c : Insp dest, a ≤ b ∧ b ≤ c ∧ ¬ b ≤ a ∧ ¬ c ≤ b   -- a strict 3-chain
```
Certify non-triviality by a strict 3-chain (stronger than "not discrete + not indiscrete").

- **Failure mode:** *needs `|Hold| ≥ 2` (a second hold `h₁`), a stronger hypothesis than the charter's bar.* Not wrong, but over-strong: the charter asks only "neither discrete nor indiscrete," which C1 discharges from `h₀` alone. **Reject as the contract (retain as an optional strengthening if `|Hold| ≥ 2` is available); C1 is the right strength.**

### C5, the order defined to make the mint monotone by fiat (the pullback sin)

```lean
instance : LE (Insp dest) where le a b := mintL dest h₀ a ≤ mintL dest h₀ b   -- pullback along the mint
```
Define the inspection order AS the mint's pullback of the labelled order, so the mint is monotone by definition.

- **Failure mode:** *connection by fiat (discipline 2), SERIOUS.* Engineering the order to make the map work is precisely the escape the charter forbids: the order carries no content of its own, and the "connection" is tautological. **Reject.** The winner A-C2 orders by the residue, a quantity defined WITHOUT reference to the mint, and the monotonicity is then a THEOREM (WS3), not a definition.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | two non-triviality theorems | `instLEInsp`, `instLELab`, witnesses | yes, related-unequal + unrelated pairs | **win (the contract)** |
| C2 | bundled aggregate | C1 | yes, the conjunction | **win (audit-facing)** |
| C3 | genuine `Preorder` instances | the two `LE`s | yes, refl/trans | **win (WS3 prerequisite)** |
| C4 | strict 3-chain | `|Hold| ≥ 2` | yes, but over-strong | reject (wrong strength) |
| C5 | order = mint-pullback | — | yes, tautological | **reject (fiat, SERIOUS)** |

## Winning candidates: C1 (non-triviality) + C2 (aggregate) + C3 (preorders)

### Definitions and obligations (cite `spec/README.md` §2.5–§2.6; `spec/ws1-orders-design.md`)

The two `LE`s and `Preorder`s are the sub-artifact's A-C2 and B-C3. WS1 delivers:

```lean
-- instLEInsp, instPreorderInsp, instLELab, instPreorderLab  (from ws1-orders-design.md)
-- ws1_orders_insp_nontrivial (C1), ws1_orders_lab_nontrivial (C1), ws1_orders_nontrivial (C2)
```

**Proof architecture.** C3 supplies the `Preorder` instances (reflexivity/transitivity, sub-artifact). C1 discharges non-triviality per order from the concrete witnesses (`⊤i`, `⊥i` for inspections; `d⊥`, `mintL ⊤i`, `mintL ⊥i` for labelled coalgebras), each a related-unequal pair (discrete-refuting) and an unrelated pair (indiscrete-refuting). C2 bundles them for WS5. **Dependencies:** `residue`/`diag` (README §2.3) and the mint `mintL` (README §2.7, defined in WS2 but its witnesses are used here for the labelled non-triviality; the build orders WS1's non-triviality after `mintL` is in scope, a WS1↔WS2 file edge recorded in the ledger). **The two orders and the argument that each is non-trivial are the sub-artifact's whole content; WS1 owns the contract.**

## Outcome classes (per charter §5)

- **Dual (the WS1 payoff):** `ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial` (both orders non-trivial), the `Preorder` instances (WS3's prerequisite), the mint monotone (WS3), the connection non-iso (WS3/WS4).
- **Disconnected (pre-registered, first-class, the honest obstruction):** the variance wall stands (sub-artifact "The knot resolved" §, the trigger). No non-trivial pair reconciles the antitone residue with a monotone mint without an iso or a discrete order. The obstruction is the result; WS2–WS5 not built. **The design says so explicitly: WS1 DISCONNECTED ⟹ series Disconnected.**
- **Partial (pre-registered):** an order proves non-trivial but the connection collapses to an iso (B-C2 leaked into the labelled order), so the non-triviality is real but the connection is by fiat; reported Partial.
- **Strip test.** Delete "duality / fit / knot" from the two non-triviality theorems and they are the bare facts *"the residue order on inspections is neither `=` nor `⊤`"* and *"the two-region labelled order is neither `=` nor `⊤`"*, two order-non-triviality facts, exactly discipline 2's demand. No name is a term.

## Deliverable

`series-13/formal/Series13/ws1.lean`: the transcribed carrier (README §6); the two orders and preorders (sub-artifact); `ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial`, `ws1_orders_nontrivial`. **WS1 is blocking; the two orders are ambient for WS2–WS4; DISCONNECTED is pre-registered with the variance wall recorded (sub-artifact).** Axiom check: `#print axioms ws1_orders_nontrivial` reduces through `residue`/`diag` and the finite witnesses to the standard three. **The two orders are proved non-trivial (neither discrete nor indiscrete), the guard against connection-by-fiat, and the contract WS2–WS4 build against.**
