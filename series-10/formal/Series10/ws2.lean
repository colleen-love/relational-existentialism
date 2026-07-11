/-
`series-10/formal/Series10/ws2.lean`

WS2 — **Genuine growth, not bookkeeping.** Series 10, the payoff.

**PHASE E RELABEL (series-review-1 S1, SERIOUS). The payoff is BOOKKEEPING, honestly reported.** The
charter (§2 Consequence 1, §4.3, §5.5, Success Criterion 2) demanded the specified target: `Ω_{α+1}` does
NOT bisimulation-embed into `Ω_α`, proved via freeness of an actually-adjoined `reify s`. **That target
provably RESISTS on the plain `PkObj κ` carrier**, and the resistance is the charter's pre-registered
Bookkeeping antecedent: the collapse engine `ws1_atomless_bisim` (`hneRel_isBisim`) makes ANY two
hereditarily-non-empty relata bisimilar, so a reified relatum `reify s` (which `ws3_reify_preserves_SHNE`
shows is `SHNE`) is bisimilar to every prior `SHNE` relatum. Hence `Ω_{α+1}` DOES bisim-embed into `Ω_α`
— growth is cardinality-only, not up to bisimulation. This is Series 09's moving hole re-hit one level
up: `reify` (a plain section) grows the carrier as a SET but not its bisimulation quotient. Per protocol
§0.2 / Phase E the honest terminus is **Bookkeeping** (a first-class success, charter §7), demonstrated
rigorously by `ws2_growth_is_bookkeeping` / `ws2_reify_bisim_embeds`, NOT a fourth `labelLoop` theorem.

The `labelLoop` facts below (`ws2_free_label_survives`, `ws2_label_free_import`, `ws2_history_labels`)
are the transcribed Series 09/08 import-test facts about a FIXED two-state coalgebra. They are TRUE but
they are NOT tower growth: they do not mention `reify`, `reifyStep`, `towerN`, or `prec`, and are retained
only as the honest record of what the labelled level does say (and does not: it says nothing about the
tower). The strict-internal-growth claim is RETRACTED.

Depends on WS1/WS3. Design doc: `series-10/spec/ws2-design.md` (payoff relabelled Bookkeeping, S1).

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws3

universe u

namespace Series10.WS2

open Series10.WS1 Series10.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The payoff, relabelled: growth is BOOKKEEPING (S1) -/

/-- **D1 — the Bookkeeping demonstration (S1, the honest terminus).** On the plain carrier ANY two
hereditarily-non-empty relata are bisimilar (the collapse engine `ws1_atomless_bisim`). So the tower's
bisimulation quotient is a single point on the `SHNE` field: adjoining reified relata grows the carrier as
a SET but leaves the quotient unchanged. Growth is cardinality-only, NOT strict-internal — Series 09's
moving hole re-hit at the carrier level. This is the pre-registered Bookkeeping antecedent (charter §5.5),
now a theorem. -/
theorem ws2_growth_is_bookkeeping {X : Type u} (dest : X → PkObj κ X)
    (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y :=
  ws1_atomless_bisim dest x y hx hy

/-- **D2 — the reified relatum bisim-embeds (S1, the moving-hole re-hit, made precise).** A reified
non-empty hereditarily-non-empty pattern yields a relatum bisimilar to every prior `SHNE` relatum: the
adjoined `reify s` does NOT differentiate up to bisimulation, so `Ω_{α+1}` bisim-embeds into `Ω_α`. The
specified non-embedding target is FALSE on this carrier; the payoff is Bookkeeping. -/
theorem ws2_reify_bisim_embeds {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ z ∈ s.1, SHNE dest z)
    (y : X) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R (reify s) y :=
  ws1_atomless_bisim dest (reify s) y (ws3_reify_preserves_SHNE dest reify h s hs hsucc) hy

/-! ## The labelled-level facts, retained as transcription (NOT tower growth) -/

/-- **The transcribed import-test fact (NOT tower growth).** On the FIXED two-state `labelLoop` coalgebra,
`⟨true⟩` and `⟨false⟩` stay apart at the labelled level (`ws4_label_survives_quotient`). This is Series
09/08 machinery about a fixed field; it mentions no tower object and is NOT the strict internal growth the
charter asked for (that is Bookkeeping, D1/D2). Retained only as the honest record of the labelled level. -/
theorem ws2_free_label_survives (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ws4_label_survives_quotient hinf

/-- **The import-test dichotomy on the fixed coalgebra (NOT tower growth).** `⟨true⟩`/`⟨false⟩` are
plain-bisimilar but not label-bisimilar — the `ws4_free_label_is_import` horn. A fact about a fixed
2-state field, not about the reification tower. -/
theorem ws2_label_free_import (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **The plain collapse persists (the honest disclosure).** At the PLAIN level the collapse engine merges
`⟨true⟩` and `⟨false⟩` — confirming that on the plain carrier (where the tower lives) growth is not strict
up to bisimulation. This is the disclosure that made the Bookkeeping relabel (D1/D2) the honest terminus. -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩

end Series10.WS2
