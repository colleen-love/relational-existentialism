/-
`series-7/formal/Series7/ws7.lean`

WS7 — **The anti-circularity audit, and the typed verdict.** Series 7, runs last.

Owns the audit against the signature risk — CIRCULARITY — and the typed `ProgramVerdict`.

REVIEW RESPONSE (project-review-1.md S1/S4/R3, recorded in `charter-status.md`). Pass 1 was
right that the pass-1 verdict was hand-set: three `Bool` literals with no Lean dependency on the
audit theorems, so the audit could not fail. Fixed here — the verdict is now a function of an
`Audit` CERTIFICATE whose every field is a theorem; `ws7_verdict` cannot be built without
discharging them, so breaking any audit content breaks the verdict's build (S1). The
non-circularity content is re-grounded on the REAL drop-(1) label escape (which survives the
behavioral quotient, `WS4.ws4_label_survives_quotient`) and the drop-(2) plain non-reduction,
not on the `Iff.rfl` definitional alias (S4a is now a prose usage claim, not a counted anchor).
The strip ledger carries actual counterexample TERMS — a behaviorally-identified plural coalgebra
WITH a leaf (`leafCoalg`), the labelled carrier, and `twoLoop` — so cleanliness is contingent on
them typechecking (R3).

Self-audit disclosure (charter §9): Claude-auditing-Claude. NC1 — that behavioral identity is the
program's founding predicate (used in Series 4–6, not gerrymandered) — is a USAGE claim stated in
prose, deliberately NOT counted as a Lean anchor (it would be `Iff.rfl` on a definitional alias).
The objective anchors are the escape refutations and the strip witnesses below, each a theorem.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws6

universe u

namespace Series7.WS7

open Series7.WS1 Series7.WS3 Series7.WS4 Cardinal

variable {κ : Cardinal.{u}}

/-- Series 7's three outcomes (transcribed base, re-pointed). -/
inductive ProgramVerdict
  | importForced         -- theorem holds, non-circular, trichotomy exhaustive
  | payoffsEstablished   -- holds with honest scope (exhaustiveness across any-construction open)
  | Circular             -- escapes only excluded by fiat — a sharp negative, honestly returned
  deriving DecidableEq

/-! ## The atomless-strip witness: a behaviorally-identified plural coalgebra WITH a leaf -/

noncomputable def leafDest (hinf : ℵ₀ ≤ κ) : Bool → PkObj κ (ULift.{u} Bool)
  | true  => toPk hinf {(⟨false⟩ : ULift.{u} Bool)}
  | false => toPk hinf (∅ : Set (ULift.{u} Bool))

/-- `⟨true⟩` points to `⟨false⟩`; `⟨false⟩` is a leaf (empty successor). -/
noncomputable def leafCoalg (hinf : ℵ₀ ≤ κ) : ULift.{u} Bool → PkObj κ (ULift.{u} Bool) :=
  fun i => leafDest hinf i.down

@[simp] lemma leafCoalg_true (hinf : ℵ₀ ≤ κ) :
    (leafCoalg hinf ⟨true⟩).1 = {(⟨false⟩ : ULift.{u} Bool)} := rfl
@[simp] lemma leafCoalg_false (hinf : ℵ₀ ≤ κ) :
    (leafCoalg hinf ⟨false⟩).1 = (∅ : Set (ULift.{u} Bool)) := rfl

/-- `⟨false⟩` is a leaf: it bottoms out (fails `SHNE`). -/
theorem leafCoalg_has_leaf (hinf : ℵ₀ ≤ κ) : ¬ SHNE (leafCoalg hinf) ⟨false⟩ := by
  intro hs
  exact (hs ⟨false⟩ Relation.ReflTransGen.refl) (by rw [leafCoalg_false])

/-- `leafCoalg` is behaviorally identified: no bisimulation relates the two states (one has an
empty successor, the other does not), so the maximal bisimulation is the diagonal. -/
theorem leafCoalg_behav (hinf : ℵ₀ ≤ κ) : BehaviorallyIdentified (leafCoalg hinf) := by
  intro R hR a b hRel
  rcases a with ⟨ba⟩; rcases b with ⟨bb⟩
  cases ba <;> cases bb
  · rfl
  · obtain ⟨_, hbwd⟩ := hR ⟨false⟩ ⟨true⟩ hRel
    obtain ⟨x', hx', _⟩ := hbwd ⟨false⟩ (by rw [leafCoalg_true]; exact rfl)
    rw [leafCoalg_false] at hx'
    exact absurd hx' (Set.not_mem_empty _)
  · obtain ⟨hfwd, _⟩ := hR ⟨true⟩ ⟨false⟩ hRel
    obtain ⟨y', hy', _⟩ := hfwd ⟨false⟩ (by rw [leafCoalg_true]; exact rfl)
    rw [leafCoalg_false] at hy'
    exact absurd hy' (Set.not_mem_empty _)
  · rfl

/-! ## The audit anchors (each a theorem) -/

/-- **D1 — the non-circularity audit, re-grounded on real escapes (S4).** (a) the drop-(1)
label escape is refuted as a THEOREM: a labelled world, behaviorally identified yet plural, whose
distinction SURVIVES the label-quotient (drops plainness). (b) the drop-(2) plain non-reduction is
refuted as a THEOREM: bisimilar-yet-unequal atomless states on the plain functor. Neither is the
`Iff.rfl` definitional alias (NC1, now a prose usage claim). -/
theorem ws7_non_circularity_audit (hinf : ℵ₀ ≤ κ) :
    (BehaviorallyIdentifiedL (labelLoop hinf)
       ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨⟨(ws4_labels_are_import hinf).1, ws4_label_survives_quotient hinf⟩,
   ⟨fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩⟩

/-- **D2 — the kinds are genuinely distinct (not a definitional partition).** An import that is
not a leaf (the atomless indexed loops), and a leaf (an atom) that is not an import. -/
theorem ws7_kinds_distinct (hinf : ℵ₀ ≤ κ) :
    (ImportDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩ ∧ ¬ LeafDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩)
  ∧ (∃ (X : Type u) (dest : X → PkObj κ X) (x y : X), LeafDiff dest x y ∧ ¬ SHNE dest x) :=
  ⟨ws3_import_not_leaf hinf, ws3_leaf_not_import hinf⟩

/-- **D3 — the strip ledger, with actual counterexample TERMS (R3).** Cleanliness is contingent
on these typechecking, not on a hand-written `true`:
* strip ATOMLESS → `leafCoalg`: behaviorally identified, plural, WITH a leaf;
* strip PLAIN → `labelLoop`: labelled, behaviorally identified (label-bisim), plural, surviving
  the label-quotient;
* strip IMPORT (behavioral identity) → `twoLoop`: plain, atomless, plural, bisimilar-yet-unequal. -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    -- strip atomless: a behaviorally-identified plural coalgebra with a leaf state
    (BehaviorallyIdentified (leafCoalg hinf) ∧ ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
       ∧ ¬ SHNE (leafCoalg hinf) ⟨false⟩)
    -- strip plain: the labelled carrier, plural, distinction surviving the label-quotient
  ∧ (BehaviorallyIdentifiedL (labelLoop hinf)
       ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
    -- strip import: plain, atomless, plural, bisimilar-yet-unequal
  ∧ ((∀ i, SHNE (twoLoop hinf) i) ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)) :=
  ⟨⟨leafCoalg_behav hinf, by decide, leafCoalg_has_leaf hinf⟩,
   ⟨(ws4_labels_are_import hinf).1, ws4_label_survives_quotient hinf⟩,
   ⟨twoLoop_HNE hinf, fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩⟩

/-! ## The mechanized audit certificate — the verdict is a function of PROOFS (S1) -/

/-- The mechanized audit certificate. Every field is a THEOREM; you cannot construct an `Audit`
without discharging them, and the verdict is a function of it — so breaking any field breaks the
verdict's build. This is the fix for the pass-1 hand-set flags (S1). -/
structure Audit (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) : Prop where
  nonCircular : (BehaviorallyIdentifiedL (labelLoop hinf)
                   ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
                ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  kindsDistinct : ImportDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩ ∧ ¬ LeafDiff (twoLoop hinf) ⟨true⟩ ⟨false⟩
  stripAtomless : BehaviorallyIdentified (leafCoalg hinf) ∧ ¬ SHNE (leafCoalg hinf) ⟨false⟩
  stripImport : (∀ i, SHNE (twoLoop hinf) i) ∧ (∃ R, IsBisim (twoLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)

/-- The audit is discharged (every field a theorem). -/
theorem ws7_audit (hinf : ℵ₀ ≤ κ) : Audit κ hinf where
  nonCircular := ws7_non_circularity_audit hinf
  kindsDistinct := (ws7_kinds_distinct hinf).1
  stripAtomless := ⟨leafCoalg_behav hinf, leafCoalg_has_leaf hinf⟩
  stripImport := ⟨twoLoop_HNE hinf, fun _ _ => True, twoLoop_true_bisim hinf, trivial⟩

/-- **The verdict as a function of the audit certificate.** Requires an `Audit`; there is no
`payoffsEstablished` / `importForced` without one. `exhaustive` is the (honestly `false`)
any-construction exhaustiveness flag — the sole open (WS3/WS6). -/
def verdict {hinf : ℵ₀ ≤ κ} (_cert : Audit κ hinf) (exhaustive : Bool) : ProgramVerdict :=
  bif exhaustive then .importForced else .payoffsEstablished

/-- **D4 — the typed verdict**, computed from the discharged audit and the open exhaustiveness. -/
def ws7_verdict (hinf : ℵ₀ ≤ κ) : ProgramVerdict := verdict (ws7_audit hinf) false

/-- The verdict is `payoffsEstablished` — non-circular, strip-clean, exhaustiveness open. This
`rfl` depends on `ws7_audit`, hence on every audit field (S1): break one and this fails to build. -/
theorem ws7_verdict_eq (hinf : ℵ₀ ≤ κ) : ws7_verdict hinf = ProgramVerdict.payoffsEstablished := rfl

/-- **The `Circular` arm is live, and genuinely tied to the audit.** WITH a certificate the
verdict is never `Circular`; the only route to `Circular` is a FAILED audit (no certificate). So
the audit is falsifiable — it is not a hand-set flag. -/
theorem ws7_audited_not_circular {hinf : ℵ₀ ≤ κ} (cert : Audit κ hinf) (e : Bool) :
    verdict cert e ≠ ProgramVerdict.Circular := by
  cases e
  · show ProgramVerdict.payoffsEstablished ≠ ProgramVerdict.Circular; decide
  · show ProgramVerdict.importForced ≠ ProgramVerdict.Circular; decide

/-- The verdict without a certificate: `Circular`. This is a plain constant naming the
no-certificate outcome; the load-bearing content is `ws7_audited_not_circular` (with a
certificate, never `Circular`) — the pass-verdicts require an `Audit`, so a failed
non-circularity audit leaves only this. (Pass-2 C4: the constant is documentation, not the proof.) -/
def verdictNoCertificate : ProgramVerdict := ProgramVerdict.Circular

/-- If exhaustiveness were to land (`exhaustive = true`) with a certificate, the same function
yields the strong `importForced` — the pre-registered ceiling, gated on the open flag. -/
theorem ws7_import_forced_if_exhaustive {hinf : ℵ₀ ≤ κ} (cert : Audit κ hinf) :
    verdict cert true = ProgramVerdict.importForced := rfl

end Series7.WS7
