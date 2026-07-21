# WS4 design — The continuity's fork (the knot) (2.6)

**Prove the fork on the weak continuity: WOVEN (a recoverable weak continuity, an endogenous succession) and
SEVERED (no recoverable weak continuity, the succession an import) both REACHABLE, on genuine carriers, so the
continuity is SELF-RELATIVE (charter §2 WS4). The fork must be GENUINE: both readings reachable (no fiat), the
weak continuity genuinely weaker than strict identity (WS2). A companion MORTALITY fork: CONSERVATIVE (nothing
ceases; every moment is attended) or MORTAL (a self ceases when no attention holds it — attention-relative
cessation, on the knowing-asymmetry). The knot rests on the weak continuity's recoverability, not on strict
identity failing (audit c); the fork is not by fiat (audit b); no persistence is asserted absolutely (audit a).**

## 1. Candidate constructions

1. **Decide the continuity (assert WOVEN, or assert SEVERED) as a fact.** REJECTED: the fiat (charter §4.d). The
   verdict must be the residue of a computation over reachable carriers, not asserted.
2. **Exhibit BOTH carriers and read the self-relativity (CHOSEN).** WOVEN is reachable (`ws2_cont_recoverable` on
   the merged carrier) and SEVERED is reachable (`ws2_cont_is_import` on the cut carrier); neither is forced by
   the plain structure, so the continuity is self-relative (`ws4_carrier_relative`). The mortality companion is
   stated on the DIRECTIONAL knowing that the continuity lift encodes, so the mortal moment and the import
   describe ONE structure (Phase D, finding C2-S1): on the cut carrier `c0` KNOWS `c1` but `c1` does not know
   `c0` (`cutKnows`, the directional knowing that `cutLift` tags), so `c0` is known by nothing — a moment nothing
   holds, attention-relative cessation (`ws4_cessation_relative`, bundled with `¬ Recoverable (cutLift)`, both
   about the same asymmetric knowing); on the merged carrier the knowing is mutual (`mergeKnows`), so every
   moment is held (`ws4_conservative_reachable`). Both mortality readings reachable.

## 2. Triage

- **No costume (audit c).** The fork is the recoverability of the WEAK continuity (`Recoverable (mergeLift)` vs
  `¬ Recoverable (cutLift)`), NOT strict identity failing. The verdict (WS5) keys on these flags and the WS3 line
  import, never on the WS1 strict-failure flag alone.
- **No fiat (audit b).** WOVEN and SEVERED are both reachable structures; the weak continuity is genuinely weaker
  than strict identity (`ws2_weaker_than_strict`); SEVERED is not excluded by construction (the cut carrier
  realizes it).
- **No absolute persistence (audit a).** No theorem asserts the continuity holds frame-independently; it is FOR a
  carrier — WOVEN on the merged carrier, SEVERED on the cut carrier, neither forced. `ws4_carrier_relative`
  bundles both reachabilities as the self-relativity.
- **Strip test.** `ws4_woven_reachable` → "a `Recoverable` lift exists"; `ws4_severed_reachable` → "a
  non-`Recoverable` lift exists"; `ws4_carrier_relative` → "both exist"; `ws4_cessation_relative` → "a node with
  empty in-attention exists, and the holding is non-recoverable"; `ws4_conservative_reachable` → "a carrier where
  every node has nonempty in-attention." Bare `Recoverable` / in-attention facts.
- **Names-not-terms (audit e).** `ws4_woven_reachable`, `ws4_severed_reachable`, `ws4_carrier_relative`,
  `ws4_cessation_relative`, `ws4_conservative_reachable` embed no forbidden content-word (note: `carrier_relative`,
  not `self_relative`).

## 3. Winning construction — typed signatures

```
-- WOVEN reachable: a recoverable weak continuity exists (the merged carrier).
theorem ws4_woven_reachable {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) : Recoverable (mergeLift hinf)

-- SEVERED reachable: a non-recoverable weak continuity (an import) exists (the cut carrier).
theorem ws4_severed_reachable {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (cutLift hinf)

-- THE CONTINUITY IS SELF-RELATIVE (audit a): both WOVEN and SEVERED reachable, neither forced.
theorem ws4_carrier_relative {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)

-- The directional knowing the continuity lifts encode (mortality is read off THIS, one structure with the lift).
def cutKnows : CCar → CCar → Prop := fun x y => x = c0 ∧ y = c1              -- c0 knows c1; c1 does not know c0
def mergeKnows : MCar → MCar → Prop := fun x y => (x = m0 ∧ y = m1) ∨ (x = m1 ∧ y = m0)   -- mutual

-- MORTALITY COMPANION — attention-relative cessation (MORTAL reachable): a moment nothing actively knows (c0),
-- and the knowing-direction non-recoverable from the symmetric relating — both about the same asymmetric knowing.
theorem ws4_cessation_relative {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∃ x : CCar, ∀ y : CCar, ¬ cutKnows y x) ∧ ¬ Recoverable (cutLift hinf)

-- CONSERVATIVE reachable: on the merged carrier every moment is known (held); nothing ceases.
theorem ws4_conservative_reachable : ∀ x : MCar, ∃ y : MCar, mergeKnows y x
```

`cutKnows`/`mergeKnows` are the directional knowings the continuity lifts encode (`cutLift` tags `c0 → c1` with
the active mark, `c1 → c0` with the passive mark; `mergeLift` tags both directions active). On the cut carrier
nothing knows `c0` (`∀ y, ¬ cutKnows y c0`, since `c0 ≠ c1`): the mortal moment, and the SAME asymmetric knowing
is the import (`¬ Recoverable (cutLift)`). On the merged carrier each moment is known by the other
(`mergeKnows m1 m0`, `mergeKnows m0 m1`): conservative. Both by `decide`.

## 4. Why the fork is genuine (no fiat, no costume)

Two carriers, one question (is the coarse continuity recoverable), forked WOVEN vs SEVERED, both reachable. The
recoverable continuity relates rank-distinct moments (`ws2_weaker_than_strict`), so it is genuinely weaker than
strict identity — not strict relabelled (no fiat). Neither carrier is forced by the plain structure, so the
continuity is self-relative (audit a). The mortality companion is a genuine fork too: a moment nothing attends
(MORTAL) is reachable, and a carrier where all are attended (CONSERVATIVE) is reachable; the cessation is
attention-relative (non-recoverable from the symmetric relating, the knowing-asymmetry).

## 5. Outcome classes

- **SHAPE-DRAWN (expected):** WOVEN and SEVERED both reachable, neither forced ⇒ the continuity is self-relative,
  the recoverability undecidable from within ⇒ the computed verdict (WS5) is SHAPE-DRAWN.
- **SEVERED (pre-registered):** would obtain if the merged (recoverable) witness fell — no recoverable weak
  continuity, the succession always an import. Reported in its direction.
- **WOVEN (pre-registered):** would obtain if the cut (import) witness fell — the continuity recoverable
  absolutely. Reported in its direction.

## 6. Strip annotation

- `ws4_woven_reachable` → "a `Recoverable` lift exists."
- `ws4_severed_reachable` → "a non-`Recoverable` lift exists."
- `ws4_carrier_relative` → "both a `Recoverable` and a non-`Recoverable` lift exist."
- `ws4_cessation_relative` → "a node no directed edge points to exists; the directed-edge lift is not
  `Recoverable`."
- `ws4_conservative_reachable` → "on a carrier every node is the target of some directed edge."
