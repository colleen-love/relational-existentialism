# WS3 — The import zone (dissent is import). Design.

**Target (charter §2-WS3).** Prove that every valuation under which `Converges₂` FAILS at `(slf, oth)` is a
genuine IMPORT: the failing valuation is non-recoverable from the plain relating (`ws3_dissent_is_import`, resting
on Series 07). So the failure of coherence lives exactly on Series 07's import boundary.

## 1. Candidates

- **(A) `¬ Recoverable` asserted as a hypothesis.** REJECTED: the import must be PROVED, a proof term resting on
  Series 07, not assumed.
- **(B) Label the failing valuation with the free point-tag (`labelLoop`).** REJECTED: the point-tag import (PR1-S2
  ancestry); the separating label must be the valuation itself, tower/content-graded.
- **(C, WINNER) Broadcast the valuation as the successor label (`valLift`), and show orientation-difference on a
  plain-bisimilar pair is `¬ Recoverable`.** Series 12's `orientLift`/`orientLift_not_recoverable` (PR1-R1),
  rebuilt fresh as `valLift`/`valLift_not_recoverable`. The failing valuation separates `slf`, `oth` (which are
  plain-bisimilar), so its lift is a genuine import.

## 2. Triage (paper)

| Criterion | (C) verdict |
|---|---|
| Rests on Series 07 (audit d) | `valLift_not_recoverable` → `ws1_atomless_bisim` + `ws4_recoverable_not_import` (P1.Core, the Series 07 collapse engine and negative import horn). |
| Universally quantified | `∀ (Or) (c), Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift … c.val)`. No valuation named. |
| Strip test | Strips to "`val slf ≠ val oth` on the plain-bisimilar `slf`, `oth` ⇒ the `val`-labelled lift is `¬ Recoverable`." |

## 3. Winning construction (typed signatures)

Fresh machinery (transcribed in spirit from Series 12 WS3, NOT imported — the layered chain forbids it):

```lean
/-- The valuation lift: broadcast a valuation as the successor label (the `val` analog of `rankLift`). -/
noncomputable def valLift {X Or : Type} (dest : X → PkObj κ X) (f : X → Or) : X → LkObj κ Or X :=
  fun x => PkMap κ (fun z => (f x, z)) (dest x)

lemma plainOf_valLift {X Or : Type} (dest : X → PkObj κ X) (f : X → Or) :
    plainOf (valLift dest f) = dest

/-- **Valuation-difference on a plain-bisimilar pair is an import.** If `f` separates two `SHNE` states
    `x`, `y` that are plain-bisimilar, `valLift dest f` is not recoverable: the plain quotient merges `x`, `y`
    but the valuation label distinguishes their edges. The general mechanism (Series 07 read for the valuation). -/
theorem valLift_not_recoverable {X Or : Type} (dest : X → PkObj κ X) (f : X → Or)
    (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) (hne : f x ≠ f y) :
    ¬ Recoverable (valLift dest f)

/-- **WS3 — DISSENT FROM CONVERGENCE IS AN IMPORT (Series 07's work, as a proof term).** EVERY faithful
    valuation that FAILS `Converges₂` at `(slf, oth)` does so by a genuine import: its valuation, lifted to
    labels, is `¬ Recoverable`. The failure lives exactly on Series 07's import boundary. Universally
    quantified over valuations (the discipline holds). -/
theorem ws3_dissent_is_import (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
    ¬ Recoverable (valLift (outDest hinf attendsR) c.val)
```

Proof of `ws3_dissent_is_import`: from `¬ Converges₂ c slf oth` and `Faithful₂ c`, `faithful_converges_iff` gives
`c.val slf ≠ c.val oth`; then `valLift_not_recoverable (outDest hinf attendsR) c.val slf oth (ws1_rcar_SHNE hinf
slf) (ws1_rcar_SHNE hinf oth) hne`. `valLift_not_recoverable` transcribes `orientLift_not_recoverable` line for
line, over `valLift`.

## 4. Outcome classes

- **shapeDrawn contribution:** dissent is an import (this WS), the import side of the two-zone boundary.
- **partial':** if dissent could not be shown an import (it can — (C)), the WS3 flag is false and the verdict is
  `partial'`. Pre-registered, not reached.

## 5. Strip-test annotation

`ws3_dissent_is_import` strips (delete "dissent"/"convergence"/"valuation") to: "if `f slf ≠ f oth` for `f : RCar
→ Or`, then the `f`-labelled lift of `outDest attendsR` is `¬ Recoverable`" — a bare import fact about a labelled
lift over a plain-bisimilar pair, exactly Series 07's necessity. Survives.
