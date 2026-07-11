/-
`series-11/formal/Series11/ws2.lean`

WS2 — **Reification rescued from Bookkeeping — REPORTED BOOKKEEPING RE-HIT (series-review-1 S1).**
Series 11, the payoff.

The intended repair was: `Ω_{α+1}` does NOT ATTENTION-embed into `Ω_α` (a finite attention distinguishes
the reified relatum) even as it bisim-embeds at the plain level (Series 10's `ws2_reify_bisim_embeds`).
**That target is NOT built.** Every payoff term (`ws2_attention_embed_fails`, `ws2_rescue_where_bisim_collapses`,
`ws2_reified_real_for_attention`) is `ws4_free_label_is_import` on the FIXED `labelLoop` — a distinction
between two fixed Booleans, NOT between a reified tower relatum and the relata it plain-collapses with.
`reify`/`reifyStep`/`towerN` occur in no payoff term; `ws2_reified_real_for_attention` even takes a
`FiniteAttention` and DISCARDS it. So the payoff is Series 10's `labelLoop` fact relabelled: **Bookkeeping
re-hit**, honestly reported (WS7 verdict `bookkeepingReHit`).

**Honest scope (protocol §0.4).** `ws2_bookkeeping_transcribed` (= Series 10's `ws2_reify_bisim_embeds`,
also re-exported as `Series11.WS7.ws7_tower_collapses`) is the PROVED Bookkeeping antecedent: on the tower
the reified relatum bisim-embeds into every prior `SHNE` relatum. `ws2_plain_collapse_persists` records the
plain collapse. The `labelLoop` free-label facts below are genuine facts about a fixed 2-state field — but
about a different object than the tower, so they do not effect the rescue. The plain collapse is not
overturned and no attention-embed-failure is proved ON the tower: Bookkeeping re-hit.

Depends on WS1. Design doc: `series-11/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws1

universe u

namespace Series11.WS2

open Series11.WS1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **D1 — the Bookkeeping theorem transcribed (the baseline to overturn).** A reified non-empty `SHNE`
pattern yields a relatum bisimilar to every prior `SHNE` relatum: `Ω_{α+1}` bisim-embeds into `Ω_α`. The
plain quotient sees NO growth — Series 10's proved Bookkeeping, unappealed. -/
theorem ws2_bookkeeping_transcribed {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ z ∈ s.1, SHNE dest z)
    (y : X) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R (reify s) y :=
  ws1_atomless_bisim dest (reify s) y (ws3_reify_preserves_SHNE dest reify h s hs hsucc) hy

/-- **D2 — the `labelLoop` free-label fact (S1: NOT the rescue).** On the FIXED `labelLoop`, `⟨true⟩`/`⟨false⟩`
are `plainOf`-bisimilar but not label-bisimilar. This does NOT mention the tower: `Ω`/`reifyStep`/`towerN`
are absent, so it is not "`Ω_{α+1}` does not ATTENTION-embed into `Ω_α`" (the specified target, not built).
It is Series 10's free-label fact, the object of the Bookkeeping re-hit. -/
theorem ws2_attention_embed_fails (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D3 — the distinction is on two fixed Booleans (S1).** `AttentionDistinguishes` holds for the fixed
`labelLoop` pair — a plain-bisimilar pair the label-reading keeps apart. But this is a distinction between
two Booleans on a fixed coalgebra, NOT between a reified tower relatum `reify s` and the prior relata it
bisim-embeds with (`ws2_bookkeeping_transcribed`). "Where the collapse is" is on `labelLoop`, not the tower. -/
theorem ws2_rescue_where_bisim_collapses (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift.{u} Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
    ∧ AttentionDistinguishes (labelLoop hinf) x y :=
  ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1, ws4_free_label_is_import hinf⟩

/-- **D4 — the `FiniteAttention` is INERT here (S1).** The theorem takes a `FiniteAttention att` and a
membership hypothesis `hmem` and DISCARDS both; the proof is the `labelLoop` fact. So "real for a finite
attention" is the fixed-Boolean distinction with an unused attention wrapper — not a hold on real reified
relata. This is the clearest single witness that the payoff is Bookkeeping re-hit. -/
theorem ws2_reified_real_for_attention (hinf : ℵ₀ ≤ κ) (att : FiniteAttention (labelLoop hinf))
    (hmem : (⟨false⟩ : ULift.{u} Bool) ∈ att.reads) :
    AttentionDistinguishes (labelLoop hinf) ⟨true⟩ ⟨false⟩ :=
  ws4_free_label_is_import hinf

/-- **D5 — the plain collapse persists (the honest disclosure).** At the PLAIN level the collapse engine
still merges the reified relatum with its neighbors. The rescue lives at the ATTENDED level, NOT the plain
level — Series 07's floor is not overturned, the reader is. -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩

end Series11.WS2
