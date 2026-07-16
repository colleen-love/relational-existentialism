# Series 11 — Design Index

**The anchor for the seven design docs, the program's terminal series. Fixes, once, every decision the workstreams share: the reifying carrier `(dest, insp, reify)` transcribed from Series 10 (the κ-bounded coalgebra `dest`, the diagonal inspection `insp`, the section `reify`), the reification tower and its ONE endogenous order `≺` (`reifyStep`, `towerN`, `prec`), the collapse engine that makes the tower Bookkeeping (`ws1_atomless_bisim` / `hneRel_isBisim`), the transcribed Series 10 Bookkeeping theorem (`ws2_reify_bisim_embeds`, `ws2_growth_is_bookkeeping`, the thing attention must overturn), the diagonal spine (`ws1_no_self_total_hold`, `ws1_diagonal_not_bisim`), the semantic import test (`Recoverable`, `plainOf`, `ws4_free_label_is_import`), and the two Series-11 additions settled here: FINITE ATTENTION (a hold reading a bounded part of the tower, finitude load-bearing, defined once in WS1 and ambient for all) and the κ-REMOVAL (the large-κ discipline promoted to holding-not-size, performed once in WS1 and propagated).**

*Series 11 is standalone. It carries its own copy of every Series 10/09/08/04 lemma it needs; nothing is imported across series (the closure gate confirms it). The upstream names reproduced (transcribed verbatim into `series-11/formal/Series11/`, re-namespaced `Series11.WSn`) are listed in §6. Series 11's engine is genuinely new Lean: finite attention (`FiniteAttention`, §2.6), the attention-reality spine (`ws1_attention_makes_real`, WS1), the rescue of the Bookkeeping theorem at the attended level (`ws2_attention_embed_fails`, WS2), no-total-attention (`ws3_no_total_attention`, WS3, the diagonal at tower scale), the κ-free endogenous bound (`ws4_no_completed_totality`, WS4), and the crown-vs-tragic fork with its kill condition (WS5). What is transcribed is the reification tower and its order that attention reads (`reifyStep`/`towerN`/`prec`/`ws3_reify_preserves_SHNE`/`ws3_order_endogenous`), the diagonal that no-total-attention IS at tower scale (`ws1_no_self_total_hold`), the collapse engine attention must survive (`ws1_atomless_bisim`), the semantic import test that certifies the attention-distinction free (`ws4_free_label_is_import`, `Recoverable`, `plainOf`), and — as the thing the whole series exists to overturn — the Series 10 Bookkeeping theorem (`ws2_reify_bisim_embeds`). Designs must be honest about which is which, and above all whether the attention-distinction is a reader genuinely NOT the plain quotient (a rescue) or a fresh external label (Bookkeeping re-hit), and whether the bound is holding-not-size (κ removed) or a re-imported cardinality ceiling (κ readmitted).*

---

## 1. The one-paragraph design

Series 10 proved (`ws2_reify_bisim_embeds`, `ws2_growth_is_bookkeeping`) that the reification tower is BOOKKEEPING at the plain level: a reified relatum `reify s` is hereditarily non-empty (`ws3_reify_preserves_SHNE`), so by the collapse engine `ws1_atomless_bisim` (`hneRel_isBisim`, the Series 07 floor) it is bisimilar to every prior `SHNE` relatum, hence `Ω_{α+1}` bisim-embeds into `Ω_α` and the plain quotient sees no growth — even though `reify` genuinely carries its pattern (`IsReify`: `dest (reify s) = s`, injective, `ws1_reify_injective`). The diagnosis: the many lives at the labelled level, but nothing READS the label, so it is formally inert, hence Bookkeeping. Series 11 keeps the tower and the diagonal and adds the one ingredient Series 10 lacked: **finite attention**, a hold that reads a bounded part of the tower and under which a reified relatum is DISTINGUISHED from its plain-bisimilar neighbors. The spine (WS1, attention-reality) is a single positive: a finite attention distinguishes the reified relatum WHERE THE PLAIN BISIMULATION COLLAPSES, and the distinction is FREE — not recoverable from the plain relating (`Recoverable`/`plainOf`, the `ws4_free_label_is_import` horn) — routing through the diagonal residue (the label the attention reads IS the diagonal content `diag insp`, so reading it is reading the self's own incompletability, not an external stamp). So productive blindness completes: the plain engine cannot see the reified relatum (Series 07, unappealed), but a finite attention that is NOT the plain quotient can. From this one fact three consequences follow. **Reification rescued from Bookkeeping** (WS2): `Ω_{α+1}` does not ATTENTION-embed into `Ω_α` (the attention-distinction survives where `ws2_reify_bisim_embeds`'s bisim-embedding holds), so the many is real at the attended level. **The endogenous bound, κ removed** (WS3/WS4): no finite attention holds the whole tower (`ws3_no_total_attention`, a total attention is a self-total hold at tower scale, forbidden by `ws1_no_self_total_hold`), so the tower never assembles into a completed totality and never Russell-explodes despite being unboundedly many — the bound is FINITUDE OF HOLDING, refutable by exhibiting a total attention, NOT a cardinality ceiling (the diagonal `ws1_no_self_total_hold` references no κ). **The unification** (WS1/WS6): Series 08's finite hold IS Series 11's finite attention, and the tower IS what finite attention proliferates by reifying its residues. The engine of all three is finite attention on the tower, on which the two obligations are discharged — **(AR)** attention makes real (WS1) and **(NT)** no total attention (WS3) — and one is the series' terminal open, the **crown** (finite attention as a sufficient endogenous bound), which WS5 *tests* against a pre-committed kill condition (charter §5.4) and never bakes into attention's definition. The honest expectation, pre-registered: the spine is genuine at the WITNESS level (a finite attention distinguishes freely where the plain quotient collapses, the reader Series 10 lacked) with the universal Partial and the Bookkeeping-re-hit arm genuinely live; no-total-attention is a clean Impossibility; the κ-free bound is Discharged on finite stages with the transfinite/carrier-κ open, so the crown is expected **Partial** with the tragic horn pre-registered and live.

---

## 2. Ambient theory (shared by all workstreams) — fixed here once

### 2.1 The carrier home beneath the tower (transcribed from Series 10; ambient for all)

The underlying relating is Series 10's **plain `P_κ`-coalgebra**, transcribed verbatim. It supplies the reaching/atomlessness/bisimulation vocabulary and, above all, the **collapse engine** the attention-distinction must survive.

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}          -- the κ-bounded powerset, F(Ω)
-- a plain coalgebra is  dest : X → PkObj κ X   (the relating)
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅   -- strong hereditary non-emptiness (no leaf)
def IsBisim (dest) (R) : Prop := …                                       -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
def hneRel (dest) : X → X → Prop := fun x y => SHNE dest x ∧ SHNE dest y
lemma hneRel_isBisim (dest) : IsBisim dest (hneRel dest)                  -- THE COLLAPSE ENGINE (Series 07/08)
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                          -- any two atomless states bisimilar
theorem ws2_import_theorem_static (dest) (hbehav : BehaviorallyIdentified dest)
    (hatom : ∀ x, SHNE dest x) : Subsingleton X                          -- THE COLLAPSE (Series 08): monism
```

**This is the home beneath the tower. No workstream may pick a different one.** `ws1_atomless_bisim` / `hneRel_isBisim` is the engine that makes the tower Bookkeeping at the plain level — the reader attention supplies must survive exactly where this engine collapses. **κ-note:** every theorem in this block holds for all `κ ≥ ℵ₀`; none relies on κ being small. This is the large-κ discipline (Series 10 §5) promoted in Series 11 to the **κ-free discipline** (§2.7): no result may rely on a cardinality ceiling.

### 2.2 The diagonal layer and the free residue (transcribed from Series 10 WS1; the engine of no-total-attention)

```lean
def Hold (dest) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }           -- a hold x↾(x,y)
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z } -- what the hold turns toward
def HoldPred (dest) : Type u := Hold dest → Prop                          -- a content
def diag (insp : Hold dest → HoldPred dest) : HoldPred dest := fun h => ¬ insp h h
def SelfTotal (insp) (t : Hold dest) : Prop := ∀ h, insp t h ↔ diag insp h   -- "holds its own complete content"
theorem ws1_no_self_total_hold (dest) (insp) : ¬ ∃ t, SelfTotal insp t    -- THE DIAGONAL (Series 09/10 spine)
theorem ws1_diagonal_not_bisim (dest) (insp) :                            -- and it is INDEPENDENT of relational identity
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ {Y} (d) (i), ¬ ∃ t, SelfTotal i t)
def residue (insp) : HoldPred dest := diag insp
def ResidueRecoverable (insp) : Prop := ∃ h, insp h = residue insp
theorem ws2_residue_free (dest) (insp) : ¬ ResidueRecoverable insp        -- THE FREE RESIDUE
theorem ws2_residue_is_import (dest) (insp) :                             -- recovery reconstructs a self-total hold
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)
```

**`ws1_no_self_total_hold` is the load-bearing κ-free fact of the whole series.** Its proof references only `insp` and propositional logic (`insp t t ↔ ¬ insp t t`); it holds for ANY `dest`, ANY `insp`, ANY κ, and never touches the cardinality bound. This is why no-total-attention (WS3) is κ-free by construction, and why the bound (WS4) is holding-not-size: the incompletability that forbids a total hold is a diagonal fact, not a cardinal fact. The residue (`= diag insp`) is the diagonal content the reified relatum carries and finite attention reads — the routing through the diagonal that keeps the attention-distinction free rather than imported.

### 2.3 The semantic import test (transcribed from Series 10 WS1/Series 04; the certificate the attention-distinction is free)

```lean
def LkObj (κ) (Q X) : Type u := PkObj κ (Q × X)                          -- the LABELLED functor
def IsBisimL (dest : X → LkObj κ Q X) (R) : Prop := …                     -- label-respecting bisimulation
def plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X := fun x => PkMap κ Prod.snd (dest x)  -- forget the label
def Recoverable (dest : X → LkObj κ Q X) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
def labelLoop (hinf) : ULift Bool → LkObj κ (ULift Bool) (ULift Bool) := fun i => toPk hinf {(i, i)}
theorem ws4_free_label_is_import (hinf : ℵ₀ ≤ κ) :                        -- THE IMPORT TEST (positive horn)
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)        --   plain-bisimilar: the plain quotient is BLIND …
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)              --   … but NOT label-bisimilar: the READER distinguishes, FREE
theorem ws4_recoverable_not_import (dest) (hrec : Recoverable dest) … :   -- THE IMPORT TEST (negative horn)
    (recoverable ⇒ the label collapses with the plain relating)
theorem ws4_labelLoop_not_recoverable (hinf) : ¬ Recoverable (labelLoop hinf)   -- the free label is NOT recoverable
```

**`ws4_free_label_is_import` is the exact shape of the attention-distinction (WS1/WS2):** a distinction (the reified relatum's identity, read as its label) that is plain-bisimulation-invisible (the plain quotient — the collapse engine — is BLIND, first conjunct) but label-bisimulation-visible (a reader that is NOT the plain quotient distinguishes it, second conjunct), and `ws4_labelLoop_not_recoverable` certifies that reader is FREE (not recoverable from the plain relating). **The Bookkeeping-re-hit check (charter §4.3, protocol §0.4) is: does the attention-distinction land on the `ws4_free_label_is_import` horn (a genuine reader, rescue) or is it a fresh external label with no plain-invisibility content (Series 10's inert label relabelled, Bookkeeping re-hit)?**

### 2.4 The reification section (transcribed from Series 10 WS1; ambient for all)

```lean
def IsReify (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop := ∀ s, dest (reify s) = s
theorem ws1_reify_injective (dest) (reify) (h : IsReify dest reify) : Function.Injective reify
```

The forward map of `Ω ≅ F(Ω)`: a section of `dest`, injective (a section has a left inverse `dest`). `reify s` is the object whose relating IS the pattern `s`. WS1 transcribes it; no workstream redefines it. It is what the tower is built from and what attention reads the residue-label of.

### 2.5 The reification tower and its ONE endogenous order (transcribed from Series 10 WS3; ambient for all)

```lean
def reifyStep (dest) (reify) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }         -- adjoin every reifiable non-empty pattern
def towerN (dest) (reify) (Ω₀ : Set X) : ℕ → Set X                        -- the ℕ-indexed iterate
  | 0 => Ω₀ | n+1 => reifyStep dest reify (towerN dest reify Ω₀ n)
def prec (dest) (reify) : Set X → Set X → Prop :=                         -- THE ONE ENDOGENOUS ORDER
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)
theorem ws3_reify_preserves_SHNE (dest) (reify) (h : IsReify dest reify) (s) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) : SHNE dest (reify s)                -- (NL) no leaf: a full relatum
theorem ws3_order_endogenous (dest) (reify) (a b) :                       -- the order is `reify`'s reachability, no clock
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b
```

**This is the tower order (protocol §2, second design duty). WS2 (rescue), WS3 (no-total-attention, NL), WS4/WS5 (bound, crown) all consume `prec`; none redefines it, none substitutes an external `Ordinal` index.** The transfinite/limit behavior (which only matters for the crown's universal form) was deferred by Series 10 WS3 to Series 11 and is now faced (charter §5.3): the finite (ℕ-indexed) `towerN` carries the bound's finite-stage form; the transfinite limit is where WS5's kill condition does its work.

### 2.6 FINITE ATTENTION (WS1 fixes it; ambient for all) — THE SERIES 11 READER DECISION

Series 10's tower could express reification but not its reader, so the label was inert (Bookkeeping). Series 11's one new structural ingredient is the reader. The tower is re-based on a **labelled** coalgebra whose label records the reified residue, so that a hold can READ what the plain relating forgets:

```lean
/-- **Finite attention.** A hold on the labelled tower whose reading is FINITE — it holds a bounded part
    of the tower and reads the label (the reified residue) the plain relating forgets. FINITUDE is the
    load-bearing property: the bound the attention imposes is the finiteness of WHAT IT HOLDS, not an
    imported index and not a cardinality ceiling on the tower. -/
structure FiniteAttention {Q X : Type u} (dest : X → LkObj κ Q X) : Type u where
  focus   : X                                          -- where the attention is directed
  reads   : Set X                                      -- the bounded part it holds
  fin     : reads.Finite                               -- FINITUDE, load-bearing (§4.4 guard)
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z   -- reads a genuine part of the tower

/-- **What an attention distinguishes.** `att` distinguishes `x` from `y` iff the plain quotient MERGES them
    (the collapse engine is blind) but no label-bisimulation relates them (the reader keeps them apart) —
    the `ws4_free_label_is_import` shape. This is the reader that is NOT the plain quotient. -/
def AttentionDistinguishes {Q X} (dest : X → LkObj κ Q X) (x y : X) : Prop :=
  (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)

/-- **Real for an attention.** `x` is real for `att` iff `att` distinguishes `x` from a plain-bisimilar
    neighbor — the reified relatum the plain engine merges but the reader holds apart. -/
def RealFor {Q X} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) (x : X) : Prop :=
  ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y
```

**The reader decision, stated once and consumed by WS2–WS6 (protocol §2, first design duty):** the ambient reader is `FiniteAttention` on the labelled tower, with `AttentionDistinguishes` (the `ws4_free_label_is_import` shape) as the distinction and `RealFor` as attention-reality. WS1 fixes it; **no two workstreams may assume different attention notions.** Four properties are load-bearing and each is a WS1/WS3 obligation, none assumed:

- **Attention is FINITE, never total (§4.5, the razor's not-too-strong horn).** `att.fin : att.reads.Finite`. A total attention would read the whole tower, i.e. be a self-total hold at tower scale, which `ws1_no_self_total_hold` forbids (WS3, `ws3_no_total_attention`). Finitude is what makes the bound holding-not-size.
- **Attention is a genuine reader, NOT the plain quotient (§4.3, the razor's not-too-weak horn).** `AttentionDistinguishes` distinguishes exactly where `ws1_atomless_bisim` collapses (`plainOf`-bisimilar) — the reader survives the collapse engine. If it did not, "attention" would be Series 10's inert label and the spine is Bookkeeping re-hit.
- **The distinction is FREE, routing through the diagonal (§4.1).** The label the attention reads is the reified residue (`= diag insp`), and it is not recoverable from the plain relating (`ws4_labelLoop_not_recoverable`, `¬ Recoverable`). Freeness routes through the diagonal, not a fresh stamp.
- **Attention reads full relata, never a leaf (§4.2, NL).** The reified relatum `att` holds is `SHNE` (`ws3_reify_preserves_SHNE`), a full relatum with its own relating, never a bare point.

### 2.7 The κ-removal (WS1 performs it once; propagated to all) — THE SERIES 11 BOUND DECISION

Series 10 imported a cardinal ceiling κ as scaffolding and marked it for removal. Series 11 removes it, and this is the second cardinal duty (charter §4.4, protocol §0.5). **What "κ-removal" means, stated precisely once, because the honesty of the whole series turns on it:**

- **The BOUND is κ-free by construction.** No-total-attention (WS3) IS `ws1_no_self_total_hold`, whose proof references no cardinal — it holds for every `dest`, every `insp`, every κ. The endogenous bound (WS4) is holding-not-size: `¬ ∃ t, SelfTotal insp t`, a fact about what a hold holds, refutable by exhibiting a total attention, with no cardinality ceiling anywhere. **This is the genuine κ-removal: the proliferation bound is a diagonal fact, not a cardinal fact.**
- **The large-κ discipline is promoted to the κ-free discipline.** Every reused theorem must hold for all `κ ≥ ℵ₀`, none relying on κ being small. WS1 re-checks each transcribed theorem (§6) against this; any that relied on small κ is reopened. In fact all of them hold for all large κ (`ws1_no_self_total_hold` uses no κ; `ws1_atomless_bisim`, `ws3_reify_preserves_SHNE`, `ws4_free_label_is_import` hold for all `κ ≥ ℵ₀`).
- **The residual carrier-κ is disclosed, not hidden (the pre-registered tragic/κ-readmitted risk).** The κ in `PkObj κ` is a BRANCHING bound (each pattern has `< κ` successors), and it is what makes the section `reify : PkObj κ Ω → Ω` EXIST (Cantor forbids `reify : Set Ω → Ω` for the full powerset). This branching-κ is a well-formedness condition on each relatum, NOT a ceiling on proliferation or holding. **The honest question WS5/WS7 must settle:** is the branching-κ genuinely not the removed κ (so the removal is real — the bound is the diagonal, holding-not-size), or is a reviewer entitled to judge it κ readmitted at the branching level (so the removal is partial and the horn tilts tragic)? This is designed in as a pre-registered failure mode to be refuted, not a fallback (charter §4.4). Predicted: the proliferation-bound κ-removal is genuine (the diagonal is κ-free), the carrier's branching-κ is scaffolding disclosed as such, and whether that counts as full removal is the crown's Partial/tragic edge.

---

## 3. The verdict type (WS7)

```lean
inductive Series11Verdict
  | attentionEstablished    -- attention-reality routes through the diagonal AND reification (not a fresh label),
                            --   attention distinguishes where the plain quotient collapses (not Bookkeeping),
                            --   no-total-attention is the diagonal at tower scale (an Impossibility), the bound
                            --   is holding-not-size (κ-free), and no result relies on small κ
  | bookkeepingReHit        -- "attention" is a fresh external label / not distinct from the plain quotient:
                            --   Series 10's PROVED Bookkeeping returning while the prose claims a rescue
  | kappaReadmitted         -- the "bound" unfolds to a cardinality ceiling on attention's range (Series 08's
                            --   conservation / Series 10's scaffold returning by the back door) — SERIOUS
  | totalAttentionSmuggled  -- attention defined so some hold captures the whole tower: a self-total hold past
                            --   the diagonal, attention mis-defined (§4.5) — a DESIGN DEFECT, not a bound
  | tragic                  -- the terminal negative: κ-removal re-admits a paradox attention cannot forbid, or
                            --   the attention-distinction is recoverable (an import) so the rescue collapses —
                            --   the many requires an imported bound; self-bounding incoherent; a first-class terminus
  | Circular                -- attention-reality free-by-fiat, the rescue defined-in, or the bound baked into
                            --   attention's definition — a WS7 finding
  deriving DecidableEq
```

`attentionEstablished`: WS1 attention-reality discharged (at least on a witness) AND certified to route through the diagonal (`ws1_no_self_total_hold` / the residue-label) and reification (`IsReify`), with the attention a reader genuinely NOT the plain quotient (distinguishes where `ws1_atomless_bisim` collapses, free by `ws4_labelLoop_not_recoverable`); WS2 rescue (attention-embed fails where `ws2_reify_bisim_embeds`'s bisim-embed holds); WS3 no-total-attention an Impossibility and (NL) preserved; WS4 the bound holding-not-size and κ-free; WS5 the crown settled to one of {Discharged, tragic, Partial} by the kill condition; and every theorem holding for all large κ. `bookkeepingReHit`: the gravest Series-11 negative — the attention-distinction is a fresh external label, so the spine is Series 10's proved Bookkeeping relabelled (charter §5.5, naming it is first-class). `kappaReadmitted`: the bound rests on a cardinality ceiling. `totalAttentionSmuggled`: attention mis-defined so a total hold exists (a design defect). `tragic`: the terminal negative, a first-class honest terminus for the program. `Circular`: a WS7 finding. The verdict is a function of a mechanized `Audit` certificate whose every field is a theorem (transcribing Series 07/08/09/10's `Audit`/`verdict` pattern), so it cannot be hand-set — and its spine field carries the *distinguishes-where-bisimulation-collapses* certificate, its bound field the *holding-not-size, κ-free* certificate.

---

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk |
|---|---|---|---|---|
| WS1 | finite attention + κ-removal + attention-reality spine | `ws1_no_self_total_hold`, `ws4_free_label_is_import`, `ws4_labelLoop_not_recoverable`, `IsReify`, `ws1_atomless_bisim` | `FiniteAttention`, `ws1_attention_makes_real`, `ws1_attention_distinction_free`, `ws1_attention_not_plain_quotient`, `ws1_kappa_free_recheck` | attention a fresh label (Bookkeeping re-hit); freeness not through the diagonal (import); a total hold (violates §4.5) |
| WS2 | reification rescued from Bookkeeping | WS1 attention-reality, `ws2_reify_bisim_embeds`, `ws4_free_label_is_import` | `ws2_attention_embed_fails`, `ws2_bookkeeping_transcribed`, `ws2_rescue_where_bisim_collapses` | the rescue is the labelLoop fact relabelled, not a hold on tower relata (Bookkeeping re-hit) |
| WS3 | no-total-attention (NT) + (NL) + bounded-holding | `ws1_no_self_total_hold`, `ws3_reify_preserves_SHNE`, WS1 `FiniteAttention` | `ws3_no_total_attention` (Impossibility), `ws3_attention_reads_full_relata`, `ws3_bounded_holding_endogenous` | NT asserted / built into attention's def; a reified leaf; bounded-holding an imported index |
| WS4 | the endogenous bound, κ removed | WS3 NT + bounded-holding, `ws1_no_self_total_hold` | `ws4_no_completed_totality`, `ws4_bound_is_holding_not_size`, `ws4_kappa_free` | the bound a re-imported cardinality ceiling (κ readmitted) |
| WS5 | the crown-vs-tragic fork | WS3/WS4 bound, WS1 κ-removal | `ws5_crown_on_finite_stages`, `ws5_kill_condition_shape`, `ws5_crown_verdict` (Discharged/tragic/Partial) | crown assumed; κ re-imported; transfinite limit breaks the bound |
| WS6 | heuristic ceiling + program close | WS1, WS5 scope | `ws6_provable_core`, `ws6_universal_theses`, `ws6_unification`, `ws6_program_close` | universal attention-reality / universal bound not rangeable |
| WS7 | Bookkeeping-re-hit + κ-readmitted + verdict | all | `Series11Verdict`, `ws7_verdict`, the `Audit`, `ws7_bookkeeping_rehit_check`, `ws7_kappa_readmitted_check` | verdict rests on a Bookkeeping-re-hit spine, a κ-readmitted bound, or a smuggled total attention |

---

## 5. Predicted headline

WS1's attention-reality is genuinely new Lean and the whole engine. **Predicted: `ws1_attention_makes_real` Discharged AT THE WITNESS LEVEL — a finite attention (the label-reading hold) distinguishes the reified relatum where the plain quotient collapses (the `ws4_free_label_is_import` horn: `plainOf`-bisimilar, NOT label-bisimilar), and the distinction is FREE (`ws4_labelLoop_not_recoverable`, `¬ Recoverable`), routing through the diagonal residue** — so Series 10's inert label is now READ, by a reader that is provably not the plain quotient. This is the genuine advance over Series 10: Series 10 had no reader; Series 11 supplies one and certifies it free. Its *strip test* will show the mathematical content is the bare `ws4_free_label_is_import` bisimulation-non-embedding fact, with "attention / reads / real" as the earned interpretive layer; the design says so, and surviving the strip AS a free-label-non-embedding routed to the residue is what the charter demands (§4.1). The honest scope hazard (charter §5.3, the gravest risk §5.5): the witness is the fixed `labelLoop`-shaped labelled coalgebra, so whether the attention genuinely reads the reification TOWER's relata (tying `reifyStep`/`prec` in) or is a fresh labelling of a fixed field is the **Bookkeeping-re-hit** edge — pre-registered as the live negative, exactly as Series 10 honestly disclosed its labelLoop facts "do not mention `reify`/`reifyStep`/`prec`." So WS1/WS2's rescue is **Discharged-on-a-witness with the universal Partial and Bookkeeping-re-hit genuinely live**. WS3's **no-total-attention is Discharged as an Impossibility** (a total attention is a self-total hold, `ws1_no_self_total_hold`), the cleanest result of the series and the κ-free engine of the bound. WS4's **κ-free bound is Discharged on finite stages** (no-total-attention + bounded-holding ⟹ no completed totality, and the diagonal references no cardinal), with the branching-κ disclosed as carrier scaffolding (§2.7). The genuinely open workstream is WS5's crown. **Predicted verdict: `attentionEstablished`** with the spine **Discharged-on-witness / Partial in the universal**, no-total-attention **Impossibility**, the κ-free bound **Discharged on finite stages / Partial transfinite**, and the crown **Partial** (finite-stage bound Discharged, transfinite and carrier-κ open), the tragic horn pre-registered and live (if the transfinite limit re-admits a total attention, or the branching-κ is judged κ readmitted, or the attention-distinction is judged recoverable). `bookkeepingReHit` only if WS1/WS2's attention is found to be a fresh label not reading tower relata (the SERIOUS finding the series exists to test, genuinely live); `kappaReadmitted` only if the bound rests on a cardinality ceiling (the holding-not-size definition guards it); `totalAttentionSmuggled` only if attention is mis-defined to hold the whole (the finitude razor guards it); `Circular` only if the audit finds attention-reality/rescue/bound defined-in. This mirrors Series 10's honest terminus (Bookkeeping proved as a theorem, the fold Partial) one level up: Series 11 supplies the reader Series 10 lacked and proves it free, and reports honestly whether that reader genuinely reads the tower (rescue) or is a fresh label (Bookkeeping re-hit), and whether the diagonal bound genuinely removes κ (crown) or the carrier-κ was doing work attention cannot do (tragic).

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-11/formal/Series11/`)

Re-namespaced `Series11.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation + the collapse engine (Series 10 `ws1`):** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `SHNE.ne_empty`, `SHNE.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim` (**the collapse engine**), `ws1_atomless_bisim` (any two atomless states bisimilar), `ws1_recovers_static`, `ws2_import_theorem_static` (**the collapse**, monism).
- **The labelled / import test (Series 10 `ws1` / Series 04 `ws4`):** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `labelLoop`, `ws4_free_label_is_import` (**the import test**, positive horn — the shape of the attention-distinction), `ws4_recoverable_not_import` (negative horn — the shape of Bookkeeping), `ws4_label_survives_quotient`, `ws4_labelLoop_not_recoverable` (**the free label is not recoverable** — the freeness certificate).
- **The diagonal spine and the free residue (Series 10 `ws1`) — the engine of no-total-attention:** `Hold`, `afford`, `ws1_hold_forced`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold` (**the diagonal**, the κ-free fact), `ws1_diagonal_not_bisim` (**its independence**), `ws1_insp_not_surjective`, `ws1_unrestricted_carrier_inconsistent`, `ws1_diagonal_forbids_closure`, `residue`, `ResidueRecoverable`, `ws2_residue_distinct`, `ws2_residue_free` (**the free residue**), `ws2_residue_is_import`.
- **The reification section (Series 10 `ws1`):** `IsReify`, `ws1_reify_injective`, `ws1_free_reification`, `IsTotalityRelatum`, `ws1_close_forbidden_local`, `ws1_reification_is_free_label`.
- **The reification tower and its order (Series 10 `ws3`):** `reifyStep`, `reifyStep_superset`, `reify_mem_reifyStep`, `towerN`, `prec`, `prec_step`, `ws3_reify_preserves_SHNE` (**NL, no leaf**), `ws3_tower_step_subset`, `ws3_tower_monotone`, `ws3_order_endogenous`, `ws3_imported_order_refuted`, `ws3_tower_monotone_family`.
- **The Series 10 Bookkeeping theorem (Series 10 `ws2`) — the thing attention must overturn:** `ws2_growth_is_bookkeeping`, `ws2_reify_bisim_embeds` (**the moving-hole re-hit**: a reified relatum bisim-embeds), `ws2_free_label_survives`, `ws2_label_free_import`, `ws2_plain_collapse_persists`.
- **The coincidence witness — transcribed as a negative touchstone:** `Symmetric`, `ws1_symmetric_states_bisimilar` (kept so WS7 can certify Series 11's payoffs do not launder through it).
- **Verdict (Series 07/08/09/10 `ws7`):** the `Audit`/`verdict` certificate pattern, re-pointed to `Series11Verdict` (§3).

Nothing is `import`ed across series; each is copied into the relevant `series-11/formal/Series11/wsN.lean` and re-namespaced, and the closure gate confirms it. The **genuinely new Series 11 Lean** is finite attention (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`, §2.6), attention-reality (WS1), the rescue at the attended level (WS2), no-total-attention (WS3), the κ-free bound (WS4), and the crown-vs-tragic fork (WS5).

---

*Design index for Series 11, the program's terminal series. Read this before any `wsN-design.md`; the shared objects (the reifying carrier `(dest, insp, reify)`, the diagonal layer, the reification tower and its ONE order `≺`, the collapse engine, finite attention `FiniteAttention`, the κ-removal, the verdict) are defined here once and cited. The two discipline rules — the attention-distinction is a reader genuinely NOT the plain quotient (not Bookkeeping re-hit, PROMOTED to first-class) and the bound is holding-not-size (not κ readmitted, PROMOTED to first-class) — are the spine of the review. Finite attention is finite (never total, §4.5) yet a genuine reader (distinguishes where bisimulation collapses, §4.3), and the crown is refuted-or-proved never assumed. No em dashes in final academic paper copy; this working design index is not final copy.*
