# WS3, The connection (the fit)

**Design doc. Series 13. Owns: the ADJOINT `readInsp` (the best-approximation inspection, realizing the reference-folded residue-label as a residue), the `GaloisConnection` between the WS1 orders (`ws3_galois`, Mathlib), the round trips as closure and interior operators (`ws3_roundtrip_closure`, `ws3_roundtrip_interior`), and the NON-IDENTITY round trip on a named element (`ws3_roundtrip_not_identity`), so the connection is genuinely adjoint and not an isomorphism in disguise. WS3 is the guard against connection-by-fiat (discipline 2, the iso-in-disguise half).**

*Series 13 is standalone; the residue and diagonal (`residue`, `diag`), the WS1 orders (`instLEInsp`, `instLELab`, `instPreorderInsp`, `instPreorderLab`), and the mint (`mintL`, WS2) are transcribed/consumed from `spec/README.md` and the WS1/WS2 designs. WS3 DEFINES the adjoint `readInsp` (README §2.7) and proves the connection. Mathlib's `GaloisConnection` (`Mathlib.Order.GaloisConnection`) carries the machinery: `GaloisConnection l u := ∀ a b, l a ≤ b ↔ a ≤ u b`, and the closure/interior facts (`gc.le_u_l`, `gc.l_u_le`) are downstream. The signature risk: the connection collapsing to an ISOMORPHISM (both round trips the identity), the coincidence restated rather than the fit proved; foreclosed by `ws3_roundtrip_not_identity`, the interior strictly below the identity at a named element.*

## The object at stake

The charter's WS3 (§2): define the best-approximation adjoint (the finest inspection whose mint sits below a given labelled coalgebra) and prove the Galois connection between the WS1 orders; prove the round trips are closure and interior operators; and prove at least one round trip NOT the identity on a named element, so the connection is genuinely adjoint and not an isomorphism in disguise. The unit and counit defects are the measurement: what an import forgets of any diagonal origin (the interior drops the reference-bit), what a residue gains in becoming a label. The categorical upgrade (functors, unit/counit as natural transformations) is a stretch target, recorded if reached and not owed.

**The knot resolved (from `spec/ws1-orders-design.md`).** The inspection order is by residue (covariant); the labelled order sees the residue-position covariantly and the reference-position ANTITONICALLY (through its self-bit at `h₀`). The mint `mintL insp = (residue insp, insp h₀)` is monotone. The adjoint folds the reference-bit into the residue, making the Galois iff EXACT, the closure the identity, and the interior strictly below the identity exactly where the reference-bit is active. That fold is the fit: the connection is adjoint, not an isomorphism.

**Ambient theory.** `spec/README.md` §2.5–§2.7 (orders, mint, adjoint); `spec/ws1-orders-design.md` (the orders and the knot); Mathlib `GaloisConnection`. Notation: `bT b`, `bF b` are the residue-position and reference-position self-loop labels of `b : Lab dest`; `gb b := fun h => bT b h ∧ (h ≠ h₀ ∨ ¬ bF b h₀)` (the reference-fold); `c₁ ⊑c c₂ := ∀ h, c₁ h → c₂ h`.

## The adjoint (README §2.7), fixed

```lean
noncomputable def realizeAsResidue {X} (dest) (c : HoldPred dest) : Insp dest := fun _ h' => ¬ c h'
/-- `residue (realizeAsResidue c) = c` classically: residue (realizeAsResidue c) h = ¬ ¬ c h = c h. -/
lemma residue_realizeAsResidue (c : HoldPred dest) : residue (realizeAsResidue dest c) = c := by
  funext h; simp [residue, diag, realizeAsResidue]   -- ¬ ¬ c h = c h via Classical

noncomputable def readInsp {X} (dest) (h₀ : Hold dest) (b : Lab dest) : Insp dest :=
  realizeAsResidue dest (fun h => bT b h ∧ (h ≠ h₀ ∨ ¬ bF b h₀))       -- realize the reference-folded gb b
```

## Candidates

### C1, `GaloisConnection mintL (readInsp · h₀)` via the reference-fold (the lead)

```lean
/-- **THE GALOIS CONNECTION.** `mintL insp ≤ b ↔ insp ≤ readInsp b`, both sides equal `residue insp ⊑c gb b`.
    LHS = (residue insp ⊑c bT b) ∧ (bF b h₀ → ¬ residue insp h₀), which folds to `residue insp ⊑c gb b`;
    RHS = residue insp ⊑c residue (readInsp b) = residue insp ⊑c gb b (`residue_realizeAsResidue`). -/
theorem ws3_galois {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    GaloisConnection (mintL dest h₀) (fun b => readInsp dest h₀ b) := by
  intro insp b
  -- unfold instLELab at (mintL insp) (singleton edges) and instLEInsp; both reduce to residue insp ⊑c gb b
  simp only [instLELab, instLEInsp, mintL_true, mintL_false, readInsp, residue_realizeAsResidue]
  constructor
  · rintro ⟨hres, href⟩; intro h hc; …    -- (c ⊑c bT) ∧ (bF h₀ → ¬ c h₀) ⟹ c ⊑c gb b
  · intro hle; refine ⟨?_, ?_⟩; …          -- c ⊑c gb b ⟹ residue-part ∧ reference-part
```
The connection exact by the fold, `c := residue insp`. The mint is the left leg (WS2), `readInsp` the right leg. Both directions of the iff are the fold identity `((c ⊑c bT) ∧ (bF h₀ → ¬ c h₀)) ↔ c ⊑c gb b`, decidable case-split on `bF h₀`.

- **Ambient:** Mathlib `GaloisConnection`; `instLELab`, `instLEInsp`; `mintL_true`, `mintL_false`; `residue_realizeAsResidue`.
- **Success condition (Dual, connection):** `GaloisConnection mintL (readInsp · h₀)` typechecks, the iff exact via the fold.
- **Failure mode:** *connection by fiat / no adjoint.* Foreclosed: the fold makes the iff exact, so the adjoint genuinely exists; the non-triviality of the orders (WS1) and the non-identity round trip (C4) keep it from being vacuous or an iso. **Winner.**

**Paper triage.** Decidable: the LHS unfolds (singleton edges) to `(c ⊑c bT) ∧ (bF h₀ → ¬ c h₀)`; a two-case split on `bF h₀` shows it equals `c ⊑c gb b`; the RHS is `c ⊑c gb b` by `residue_realizeAsResidue`. **Winner.**

### C2, closure operator `readInsp ∘ mintL` (the unit, identity here)

```lean
/-- **The closure round trip.** `readInsp (mintL insp)` is order-equivalent to `insp`: its residue is
    `gb (mintL insp) = residue insp` (the fold is inert on minted coalgebras, because `bT = residue insp` and
    `bF h₀ = insp h₀ h₀ = ¬ residue insp h₀` make the fold drop nothing). So the closure is the identity
    (up to the order), `insp` is always "closed". -/
theorem ws3_roundtrip_closure {X} (dest) (h₀ : Hold dest) (hinf) (insp : Insp dest) :
    readInsp dest h₀ (mintL dest h₀ insp) ≤ insp ∧ insp ≤ readInsp dest h₀ (mintL dest h₀ insp) := by
  have hgc := ws3_galois dest h₀ hinf
  refine ⟨?_, hgc.le_u_l insp⟩          -- insp ≤ u (l insp) is the general GC closure-inflation
  -- residue (readInsp (mintL insp)) = gb (mintL insp) = residue insp, so u (l insp) ≤ insp too
  …
```
The unit/closure: on minted coalgebras the reference-fold is inert (the diagonal link `bT h₀ = ¬ bF h₀` holds, so `gb` drops nothing), so the closure `readInsp ∘ mintL` is the identity up to the order. "What a residue gains in becoming a label" is nothing it cannot get back: minting then reading recovers the residue.

- **Ambient:** `ws3_galois`, `GaloisConnection.le_u_l`, `residue_realizeAsResidue`.
- **Success condition (Dual):** the closure is the identity (both `≤`), a theorem. **Winner (the closure operator).**

### C3, interior operator `mintL ∘ readInsp` (the counit, the defect)

```lean
/-- **The interior round trip.** `mintL (readInsp b) ≤ b` always (GC interior-deflation), and it recovers
    `b` iff the reference-bit is inert. Its residue-label is `gb b ⊑c bT b` and its reference-label is
    `¬ gb b h₀`; when `bF b h₀` holds, `gb b ⊊ bT b`, so the interior is STRICTLY below `b`. -/
theorem ws3_roundtrip_interior {X} (dest) (h₀ : Hold dest) (hinf) (b : Lab dest) :
    mintL dest h₀ (readInsp dest h₀ b) ≤ b :=
  (ws3_galois dest h₀ hinf).l_u_le b       -- l (u b) ≤ b is the general GC interior-deflation
```
The counit/interior: reading a labelled coalgebra as an inspection then re-minting gives something below it, and STRICTLY below wherever the reference-bit is active, because the mint cannot forge a reference-bit inconsistent with its residue-label (the diagonal link). "What an import forgets of any diagonal origin" is the reference-bit the interior drops.

- **Ambient:** `ws3_galois`, `GaloisConnection.l_u_le`.
- **Success condition (Dual):** the interior is `≤ b`, a theorem; strict at the named element (C4). **Winner (the interior operator).**

### C4, the non-identity round trip on a named element (the fit, the payoff)

```lean
/-- **THE NON-IDENTITY ROUND TRIP.** On the named coalgebra `bRefActive := (⊤, ⊤)` (both self-loop labels
    the constant-true content), the interior round trip is STRICTLY below the identity: `mintL (readInsp
    bRefActive) < bRefActive`, i.e. `mintL (readInsp bRefActive) ≤ bRefActive` but NOT `bRefActive ≤ mintL
    (readInsp bRefActive)`. So the connection is NOT an isomorphism: it is a genuine adjunction with a real
    counit defect. -/
theorem ws3_roundtrip_not_identity {X} (dest) (h₀ : Hold dest) (hinf) :
    mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)) ≤ bRefActive dest hinf
  ∧ ¬ (bRefActive dest hinf ≤ mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf))) := by
  refine ⟨ws3_roundtrip_interior dest h₀ hinf _, ?_⟩
  rintro ⟨hres, _⟩
  -- bRefActive has bT = ⊤, bF = ⊤; gb bRefActive = ⊤ ∖ {h₀} (drops h₀ since bF h₀ = True);
  -- so mintL (readInsp bRefActive) has residue-label gb = ⊤∖{h₀}, and bRefActive's is ⊤;
  -- residue-part of (bRefActive ≤ mintL (readInsp bRefActive)) demands ⊤ ⊑c (⊤∖{h₀}), which fails at h₀.
  obtain ⟨q, hq, hfst, hle⟩ := hres (⊤, ⟨true⟩) (by simp [bRefActive])
  exact absurd (hle h₀ trivial) (by simp [gb])       -- ⊤ h₀ = True but (⊤∖{h₀}) h₀ = False
```
where `bRefActive dest hinf : Lab dest := fun i => match i with | ⟨true⟩ => toPk hinf {((fun _ => True), ⟨true⟩)} | ⟨false⟩ => toPk hinf {((fun _ => True), ⟨false⟩)}` (both labels `⊤`). Because `bF bRefActive h₀ = True`, the fold `gb bRefActive` drops `h₀`, so the re-minted residue-label `⊤ ∖ {h₀}` is strictly below `⊤`, and the interior is strictly below the identity at this named element.

- **Ambient:** `ws3_roundtrip_interior`, `instLELab`, the named `bRefActive`.
- **Success condition (Dual, the payoff):** the interior is `≤` but not `≥` at `bRefActive`, so the round trip is not the identity, and the connection is not an iso.
- **Failure mode:** *iso in disguise (discipline 2), the pre-registered PARTIAL.* Foreclosed: the reference-bit at `h₀` makes the fold lossy, so the interior strictly drops `h₀` from the residue-label; the connection is proved non-iso by a named witness. **Winner (the fit).**

**Paper triage.** Decidable: `gb bRefActive h₀ = (⊤ h₀ ∧ (h₀ ≠ h₀ ∨ ¬ ⊤ h₀)) = (True ∧ (False ∨ False)) = False`, while `bT bRefActive h₀ = ⊤ h₀ = True`, so `bT ⋢c gb` at `h₀`, so `bRefActive ⋢ₗ mintL (readInsp bRefActive)`. Strictly below. **Winner.**

### C5, both round trips proved identity (the iso, the sin stated to be rejected)

```lean
theorem ws3_roundtrip_iso (b) : mintL (readInsp b) = b := …   -- would say the connection is an isomorphism
```
Prove (or claim) both round trips are the identity, making the connection an order-isomorphism.

- **Failure mode:** *the coincidence restated, not the fit proved (discipline 2), SERIOUS.* An isomorphism would say the mint and the adjoint are mutually inverse, i.e. the diagonal manufactures exactly the imports and nothing is lost, contradicting the WS4 defect. It is FALSE here (`ws3_roundtrip_not_identity` refutes it at `bRefActive`). **Reject.** The connection is a genuine adjunction with a counit defect, not an iso.

### C6, the categorical upgrade (functors, unit/counit as natural transformations) (the stretch)

```lean
-- Compass the mint and adjoint as functors between the preorder categories, unit/counit as natural
-- transformations. Recorded if reached; NOT owed (charter §2, WS3 stretch target).
```
- **Status:** stretch. The preorder GC already gives the closure/interior; the categorical dressing adds naturality. **Recorded, not owed.** Ship if the build reaches it; otherwise the preorder connection is the deliverable.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `GaloisConnection` via the fold | Mathlib GC, `residue_realizeAsResidue` | yes, iff exact by case-split | **win (connection)** |
| C2 | closure = identity | `gc.le_u_l`, fold inert on mints | yes | **win (closure)** |
| C3 | interior `≤ b` | `gc.l_u_le` | yes | **win (interior)** |
| C4 | interior strictly below at `bRefActive` | `instLELab`, named witness | yes, `gb h₀ = False ≠ True` | **win (the fit)** |
| C5 | both round trips identity (iso) | — | yes, refuted by C4 | reject (SERIOUS, iso) |
| C6 | categorical upgrade | preorder categories | — | stretch (not owed) |

## Winning candidates: C1 (connection) + C2 (closure) + C3 (interior) + C4 (non-identity)

### Definitions and obligations (cite `spec/README.md` §2.5–§2.7; consume WS1, WS2)

```lean
namespace Series13.WS3
-- instLEInsp, instLELab, instPreorderInsp, instPreorderLab (WS1); mintL, mintL_true, mintL_false (WS2);
-- GaloisConnection (Mathlib) — consumed. residue, diag, HoldPred — transcribed.
-- realizeAsResidue, residue_realizeAsResidue, readInsp (README §2.7)
-- ws3_mint_monotone, ws3_read_monotone (monotonicity, from the GC or direct)
-- ws3_galois (C1), ws3_roundtrip_closure (C2), ws3_roundtrip_interior (C3), ws3_roundtrip_not_identity (C4)
```

**Proof architecture.** `readInsp` realizes the reference-folded content `gb b` as a residue (`residue_realizeAsResidue`). C1 proves the Galois iff by unfolding both orders on the singleton-edge coalgebras and folding: `mintL insp ≤ b ↔ (residue insp ⊑c bT b) ∧ (bF b h₀ → ¬ residue insp h₀) ↔ residue insp ⊑c gb b ↔ insp ≤ readInsp b`. Monotonicity of `mintL`/`readInsp` (`ws3_mint_monotone`, `ws3_read_monotone`) follows from the GC (`GaloisConnection.monotone_l`, `.monotone_u`) or is proved directly (the residue-covariant/reference-antitone check, `ws1-orders-design.md`). C2 shows the closure is the identity (the fold is inert on minted coalgebras: `bT = residue insp`, `bF h₀ = ¬ residue insp h₀`, so `gb (mintL insp) = residue insp`). C3 is the general GC interior-deflation. C4 exhibits `bRefActive = (⊤,⊤)`, where `bF h₀ = True` makes the fold drop `h₀`, so the interior is strictly below the identity, the connection non-iso. **Dependencies:** WS1 orders (non-trivial, the GC is over them), WS2 mint (the left leg), Mathlib `GaloisConnection`. **The connection is a genuine adjunction: the closure recovers the residue, the interior drops the reference-bit, and the drop is a theorem on a named element.**

## Outcome classes (per charter §5)

- **Dual (the WS3 payoff):** C1 (`GaloisConnection`, Mathlib), C2 (closure = identity), C3 (interior operator), C4 (`ws3_roundtrip_not_identity`, the interior strictly below at `bRefActive`). The connection genuinely adjoint, not an iso.
- **Partial (pre-registered, discipline 2):** if the only provable order made the connection an ISO (both round trips identity, `bRefActive` failing to be strictly dropped), the connection is by fiat and WS3 reports Partial (the coincidence restated). Foreclosed by C4.
- **Disconnected (inherited from WS1):** if WS1 landed Disconnected (no non-trivial order pair), WS3 is not built.
- **Strip test.** Delete "connection / fit / adjoint / unit / counit" from `ws3_galois` + `ws3_roundtrip_not_identity` and it is the bare fact *"a `GaloisConnection` between two non-trivial preorders (WS1) whose interior round trip is not the identity on the named element `bRefActive`"*, exactly protocol §0.3's target for the connection payoff. No name is a term.

## Deliverable

`series-13/formal/Series13/ws3.lean`: the WS1 orders and WS2 mint consumed; `realizeAsResidue`, `residue_realizeAsResidue`, `readInsp` (README §2.7); `ws3_mint_monotone`, `ws3_read_monotone`, `ws3_galois` (C1), `ws3_roundtrip_closure` (C2), `ws3_roundtrip_interior` (C3), `ws3_roundtrip_not_identity` (C4). The categorical upgrade (C6) shipped only if reached. **WS3 depends on WS1 (the orders) and WS2 (the mint); WS4's defect is the class of elements the interior drops.** Axiom check: `#print axioms ws3_galois` reduces through Mathlib `GaloisConnection` and `residue_realizeAsResidue` (Classical) to the standard three; `ws3_roundtrip_not_identity` through `instLELab` and the finite witness. **The Galois connection is proved, the closure and interior exhibited, and one round trip proved non-identity on a named element: the fit, not an isomorphism in disguise.**
