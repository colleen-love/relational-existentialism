# Blind seed — Phase F (code review), Charter Extension 1 re-run

You are reviewing a built Lean 4 / Mathlib development for whether the CODE proves the claimed signatures, focused on the STRENGTHENED targets of a re-run. The development is already built (`lake build P2S0` succeeds). Judge ONLY against the mathematical contracts below.

## Files you may read

- THIS file (`spec/blind-seed-F2.md`).
- The built Lean sources: `program-2/series-0/formal/P2S0.lean` and `program-2/series-0/formal/P2S0/{ws1,ws2,ws3,ws4,ws5,AxiomCheck}.lean`.
- The imported prior art: `program-2/formal/P1/Core.lean` and `program-2/formal/P1/Reader.lean` (built, axiom-clean). Note especially `P1.Reader.rankLift`, `P1.Reader.AttentionDistinguishes`, `P1.Reader.ws2_many_general`, `P1.Core.ws1_atomless_bisim`, `plainOf`, `IsBisim`, `IsBisimL`, `Recoverable`.

DO NOT READ: `charter.md`, `charter-extension.md`, `charter-status.md`, `spec/README.md`, `spec/*-design.md`, `spec/ext1-design.md`, any `summary*.md`, or any file with motivating prose. The Lean docstrings contain interpretive words ("the self," "the first other," "the mint") — those are PROSE (the object of the names-not-terms grep), not the object of your correctness review. If you open a forbidden file, say so and stop.

## Background (what changed in this re-run)

An earlier build proved reification only as an inert existence lemma on an isolated carrier, and stated the passive/active asymmetry as a bare conjunction. This re-run rebuilds WS1 and WS3 on ONE shared witness (`s0`, `s1`, `s2 : Fin 3` in `ws1.lean`), where reification CREATES the first other and the asymmetry is stated over it. WS2, WS4, and `ws3_direction_not_recoverable` are unchanged and must still stand.

## The strengthened claims under review

**WS1 — `ws1_first_other` (`ws1.lean`).** The unified witness: `attendsU s0 = {s0}` (self-loop), `attendsU s1 = {s0}`, `reifyU {s0} = s1`, `rankU s0 = 0`, `rankU s1 = 1`.
```
ws1_first_other (hinf : ℵ₀ ≤ κ) :        -- κ : Cardinal.{0}
    reifyU {s0} = s1
  ∧ attendsU (reifyU {s0}) = {s0}          -- reify SECTIONS the self-relation (pointwise)
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0
```
CHECK: (1) is the first other genuinely CREATED by reification (`reifyU {s0} = s1`, and `attendsU (reifyU {s0}) = {s0}` a real section)? (2) is the separation NON-VACUOUS and NON-RECOVERABLE — `s1` plain-bisimilar to `s0` over the bare relating (`plainOf (rankLift …) = outDest …`, both `SHNE`) yet NOT label-bisimilar (tower levels 1 vs 0 differ)? (3) THE TEETH: the first other must be NON-recoverable (an import), NOT recoverable — if the distinction were recoverable from the bare relating it would be no distinction (Series 07). Confirm the second `AttentionDistinguishes` conjunct is `¬ ∃ R, IsBisimL … R ∧ R s1 s0`, genuinely proved.

**WS3 — rebuilt, load-bearing not bare conjunction (`ws3.lean`).**
```
ws3_passive_constitution (hinf) (o : Fin 3) (hreify : reifyU {s0} = o) (hattend : s0 ∈ attendsU o) :
    AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) o s0
ws3_active_passive_distinct (hinf) :
    (s1 = reifyU {s0} ∧ s1 ∈ attendedBy attendsU s0 ∧ s1 ∉ attendsU s0)
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0
```
CHECK (the central re-run risk): is `ws3_passive_constitution` a genuine IMPLICATION whose premises DRIVE the separation, or a vacuous/bare statement? Specifically: are `hreify` and `hattend` USED in the proof (not assumed-and-ignored)? Confirm `hreify` yields the tower gap (`rankU s0 < rankU o`) that separates them, and `hattend` is the edge the separation is read on. Is `ws3_active_passive_distinct`'s separation DERIVED from `ws3_passive_constitution` (not independently conjoined)? Does `ws3_direction_not_recoverable` (on the Bool witness `knowLiftD`) still stand unchanged?

**WS5 — re-pointed flag (`ws5.lean`).**
```
ws5_flags_justified (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0 ∧ (¬ Recoverable (knowLiftD hinf)) ∧ (∀ {Q} (f : Bool → Q), f true ≠ f false → ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false)
```
CHECK (R4): is the reification flag now justified by `ws1_first_other` (the first other), NOT the old counting bijection `ws1_reification_exists`? Is `ws5_audit_asymmetry_not_label` re-pointed to the first-other separation? Do `ws5_verdict_eq` / `ws5_verdict_not_*` still compute GROUND-ESTABLISHED and discriminate?

## What must still stand (preserved)

- `ws2_collapse_inherited` (`ws2.lean`) unchanged, the imported engine applied; the first other is a MINTED, self-manufactured, NON-recoverable distinction (an import), NOT multiplicity from relating alone — it must not contradict the inherited collapse. CONFIRM the first other's genuineness rests on `¬ Recoverable`/non-label-bisimilarity, i.e. it is an import, not a claim that relating alone yields plurality.
- `ws1_bound_is_finite_attention` (no cardinal ceiling), `ws4_import_breaks_baseline`/`ws4_import_quantified` (quantified import), `ws3_direction_not_recoverable`, `ws5_verdict_*` all unchanged.

## Mechanical checks (run them)

- Sorry-free: `grep -rnE "\bsorry\b" program-2/series-0/formal` — hits must be prose ("sorry-free") only.
- Axioms: `AxiomCheck.lean` records every headline (incl. `ws1_first_other`) on the standard three (`propext`/`Classical.choice`/`Quot.sound`); `ws5_verdict_*` on none. No `sorryAx`, no custom `axiom`.
- Names-not-terms: `grep -rniE "\b(love|loved|import|god|choice|self|other|knowing|attention)\b" program-2/series-0/formal` — every hit prose or the `import` keyword; `s0`/`s1`/`s2`/`attendsU`/`rankU`/`reifyU`/`knowLiftD`/`impLift` are neutral.

## Strip test

`ws1_first_other` should strip to: "a reified relatum (`reifyU {s0}`) is plain-bisimilar to a base relatum yet not tower-bisimilar — an `AttentionDistinguishes` fact via `rankLift`, with `reifyU` sectioning the pattern." `ws3_passive_constitution` should strip to: "a relatum reifying a pattern and attending a base at a higher tower level is `AttentionDistinguishes`-separated from that base." No name a proof term.

## Grading rubric

- **SERIOUS:** a verdict rests on it; the first other is RECOVERABLE (no distinction) or vacuous; reification creates nothing that participates; the rebuilt asymmetry is still a bare conjunction / the premises are assumed-and-unused; the collapse is contradicted (multiplicity from relating alone); a `sorry`/custom axiom; a name a proof term; an undisclosed narrowing.
- **REAL:** a genuine gap correctly labelled once fixed (an over-hypothesis actually unused, an overclaimed docstring, a vacuous witness).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return findings with stable IDs `Fn-Sm`: grade, exact location (file + line/signature), precise defect. If a grade level is empty, say so. State explicitly whether `ws1_first_other`, `ws3_passive_constitution`, and `ws3_active_passive_distinct` each genuinely discharge their signatures, whether the rebuilt WS3 is load-bearing (premises used), and whether the first other is non-recoverable. Your final message IS the review report.
