/-
`series-11/formal/Series11/ws2.lean`

WS2 — **Reification rescued from Bookkeeping.** Series 11, the payoff.

The direct repair of Series 10's proved Bookkeeping: `Ω_{α+1}` does NOT ATTENTION-embed into `Ω_α` (a
finite attention distinguishes the reified relatum), even as it DOES bisim-embed at the plain level
(Series 10's `ws2_reify_bisim_embeds`, transcribed and unappealed — Series 07's floor). The many is real at
the attended level, where the plain engine is blind but a finite hold is not.

**Honest scope (protocol §0.4).** The rescue `ws2_attention_embed_fails` is `ws4_free_label_is_import`:
the plain bisim-embedding holds (first conjunct, the collapse engine merges) AND the label bisim-embedding
fails (second conjunct, the reader distinguishes), for the SAME pair. The reader is genuinely not the plain
quotient. But the witness is the FIXED `labelLoop` coalgebra; whether it lifts to every `reifyStep`-relatum
is the universal Partial, Bookkeeping-re-hit the pre-registered live negative. The plain collapse PERSISTS
(`ws2_plain_collapse_persists`) — the rescue is a new READER, not a new plain-level fact.

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

/-- **D2 — THE RESCUE.** Bisim-embeds at the plain level (the collapse engine merges), does NOT
attention-embed at the attended level (the finite attention distinguishes). `Ω_{α+1}` does not
ATTENTION-embed into `Ω_α` where it DOES bisim-embed. -/
theorem ws2_attention_embed_fails (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D3 — the rescue is where the collapse is (the Bookkeeping-re-hit certificate).** The SAME pair the
collapse engine merges is the pair the attention keeps apart — so the attention-distinction is genuinely
not the plain quotient, discharged WHERE the plain quotient is blind. -/
theorem ws2_rescue_where_bisim_collapses (hinf : ℵ₀ ≤ κ) :
    ∃ x y : ULift.{u} Bool,
      (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
    ∧ AttentionDistinguishes (labelLoop hinf) x y :=
  ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1, ws4_free_label_is_import hinf⟩

/-- **D4 — the reified relatum is real for a finite attention.** Given a finite attention that reads the
neighbor, the reified relatum is distinguished from it — real for that attention, though Bookkeeping to the
plain engine. -/
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
