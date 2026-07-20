# Blind seed C — design review (motivation-free)

You are reviewing a Lean 4 / Mathlib formalization DESIGN (typed signatures, not yet built). Judge ONLY the
mathematical claims below against the criteria in this file. This seed is self-contained: it carries every
definition and signature you need. Do not seek motivation or interpretation; there is none to judge.

The design builds on an imported ground with this API (all pre-existing, assumed correct):

- `PkObj κ X` — κ-bounded subsets of `X`; `LkObj κ Q X := PkObj κ (Q × X)` — labelled version.
- `outDest hinf attends : X → PkObj κ X` — the finite-out-attention coalgebra of `attends : X → Finset X`.
- `IsBisim dest R` / `IsBisimL dest R` — plain / label-respecting bisimulations.
- `plainOf dest : X → PkObj κ X` — forget the label of a labelled coalgebra.
- `Recoverable dest : Prop` — every plain bisimulation of `plainOf dest` is already a label-bisimulation of `dest`.
- `ws1_atomless_bisim dest x y (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y` — any two
  hereditarily-nonempty states are plain-bisimilar.
- `ws4_recoverable_not_import dest (hrec : Recoverable dest) x y (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) :
  ∃ R, IsBisimL dest R ∧ R x y`.
- `rankLift dest (rank : X → ℕ) : X → LkObj κ (ULift ℕ) X` — tag every edge of `dest x` with `rank x`.
- `AttentionDistinguishes dest x y := (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ ¬ (∃ R, IsBisimL dest R ∧ R x y)`.
- `FiniteAttention dest` — a bounded reader `⟨focus, reads, fin, grounded⟩`; `RealFor dest att x := ∃ y ∈
  att.reads, AttentionDistinguishes dest x y`.
- `Hold dest`, `HoldPred dest`, `SelfTotal insp t`, `ws1_no_self_total_hold dest insp : ¬ ∃ t, SelfTotal insp t`
  — the diagonal.
- `ws1_bound_is_finite_attention hinf attends : ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < ℵ₀`.

## The carrier under review

```lean
abbrev RCar : Type := Fin 4
def slf : RCar := 0
def oth : RCar := 1
def sh  : RCar := 2
def bnd : RCar := 3
def attendsR : RCar → Finset RCar := fun x =>
  if x = slf then {slf, oth} else if x = oth then {slf, oth, sh} else if x = sh then {sh} else {oth}
def rankR : RCar → ℕ := fun x => if x = oth then 1 else if x = bnd then 2 else 0
def reifyR : Finset RCar → RCar := fun s =>
  if s = {slf, oth, sh} then oth else if s = {oth} then bnd else slf
def rfield : Finset RCar := {slf, oth, sh}
noncomputable def faceLift (hinf : ℵ₀ ≤ κ) : RCar → LkObj κ (ULift.{0} Bool) RCar :=
  fun x => PkMap κ (fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) (outDest hinf attendsR x)
noncomputable def selfReader (hinf : ℵ₀ ≤ κ) : FiniteAttention (rankLift (outDest hinf attendsR) rankR) :=
  ⟨slf, {slf}, Set.finite_singleton slf, ⟨Set.mem_singleton slf, (grounded : ∀ z ∈ {slf}, SReaches _ slf z)⟩⟩
```
Note: `attendsR slf = {slf,oth}` is a PROPER SUBSET of `attendsR oth = {slf,oth,sh}` (the two reaches differ).
Claimed carrier facts (all by `decide`/`rfl`): every node `SHNE (outDest hinf attendsR)`; `plainOf (rankLift
(outDest hinf attendsR) lab) = outDest hinf attendsR`; `plainOf (faceLift hinf) = outDest hinf attendsR`.

## The signatures under review

```lean
-- WS1
theorem ws1_other_is_locus (hinf : ℵ₀ ≤ κ) :
    (reifyR {slf, oth, sh} = oth ∧ attendsR (reifyR {slf, oth, sh}) = {slf, oth, sh})
  ∧ oth ≠ slf
  ∧ (attendsR oth).Nonempty
  ∧ (slf ∈ rfield ∧ oth ∈ rfield
      ∧ (∀ z ∈ attendsR slf, z ∈ rfield) ∧ (∀ z ∈ attendsR oth, z ∈ rfield))
  ∧ (∀ x : RCar, Cardinal.mk (↥((outDest hinf attendsR x).1)) < Cardinal.aleph0)

-- WS2  (selfReader is a NAMED def, above; ws2_other_reader_wise proves RealFor for THAT fixed reader, not ∃att)
theorem ws2_other_distinguishes (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsR) rankR) oth slf
theorem ws2_other_reader_wise (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (selfReader hinf) oth
theorem ws2_other_non_recoverable (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)

-- WS3
def faces (x y : RCar) : Prop := y ∈ attendsR x
theorem ws3_four_readings : faces slf slf ∧ faces slf oth ∧ faces oth slf ∧ faces oth oth
theorem ws3_facing_asymmetric (hinf : ℵ₀ ≤ κ) :
    (oth ∈ attendsR slf ∧ slf ∈ attendsR oth)
  ∧ (∃ z ∈ attendsR slf, rankR slf < rankR z)
  ∧ (¬ ∃ z ∈ attendsR oth, rankR oth < rankR z)
  ∧ ¬ Recoverable (faceLift hinf)
theorem ws3_facing_partial (hinf : ℵ₀ ≤ κ) :
    (slf ∈ attendsR slf ∧ oth ∈ attendsR oth)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)

-- WS4
theorem ws4_mutual_residue (hinf : ℵ₀ ≤ κ) :
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y) ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)

-- WS5
inductive Outcome | twoFacing | one | totalized | partial' | disconnected  deriving DecidableEq
def verdict (wf readerTwo facing nonCollapse nonTotal : Bool) : Outcome :=
  if !wf then Outcome.disconnected
  else if !(readerTwo && facing) then Outcome.partial'
  else if nonCollapse && nonTotal then Outcome.twoFacing
  else if !nonCollapse then Outcome.one
  else Outcome.totalized
theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing
theorem ws5_verdict_discriminates :
    verdict true true true false true = Outcome.one
  ∧ verdict true true true true false = Outcome.totalized
  ∧ verdict false true true true true = Outcome.disconnected
  ∧ verdict true false true true true = Outcome.partial'
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :   -- bundles the WS1-WS4 headline propositions (each flag=true earned)
    (attendsR (reifyR {slf, oth, sh}) = {slf, oth, sh})
  ∧ (RealFor (rankLift (outDest hinf attendsR) rankR) (selfReader hinf) oth)
  ∧ (¬ Recoverable (faceLift hinf))
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
  ∧ (¬ Recoverable (rankLift (outDest hinf attendsR) rankR))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y) ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
-- plus audit clauses ws5_audit_reader_loadbearing/twoness_import/facing_asymmetric/residue_genuine
-- (proof-term aliases of the above), and ws5_audit_coherence_open : True, ws5_audit_names_not_terms : True.
```

## Success criteria (restated mechanically)

1. WS1: `oth` is a relatum of `RCar`, minted by a genuine `reifyR` section (`attendsR (reifyR {slf,oth}) =
   {slf,oth}`), distinct from `slf`, with a nonempty finite attention, over a shared field `rfield` containing
   both and every relatum either attends; the out-neighborhoods are `< ℵ₀` (no cardinal ceiling).
2. WS2: there is a NAMED `FiniteAttention` for which `oth` is `RealFor` (the reader load-bearing, not an
   existential over separated pairs), and the `oth`/`slf` separation is `¬ Recoverable`.
3. WS3: the four `faces` all hold; the facing is asymmetric — `slf` has a rank-raising edge, `oth` has none, and
   the reading-direction lift `faceLift` is `¬ Recoverable`; the facing is partial — no inspection is self-total.
4. WS4: on a witnessed structure carrying all four readings, a relatum bisimilar to the pair is JOINTLY
   unattended (residue), the reading order is rank-constrained, the separation is `¬ Recoverable` (not collapse),
   and no inspection is self-total (not totalized).
5. WS5: `verdict` computes `twoFacing` on the certified flags and discriminates (flip a flag → different
   outcome); the flags are earned by the WS1-WS4 headlines.

## Audit checks (a)-(e), mechanical

- **(a)** In `ws2_other_reader_wise`, is the reader load-bearing — a `FiniteAttention` whose `reads` membership
  is USED to witness `RealFor oth` — or is `oth` distinguished by a bare existential (a `Many`-style claim) with
  the reader quantified out? The reader must do the distinguishing. Is `attendsR oth` load-bearing anywhere, or
  could `oth` be replaced by a fresh tag with inert attention and every signature still hold?
- **(b)** Is `ws2_other_non_recoverable` a genuine `¬ Recoverable` proof obligation on the `oth`/`slf`
  separation, or is the separation recoverable (making the distinction collapse)?
- **(c)** Is `ws3_facing_asymmetric`'s non-recoverability (`¬ Recoverable (faceLift)`) genuinely DISTINCT from
  WS2's `¬ Recoverable (rankLift … rankR)`, or is it the same separation relabelled? Does `faceLift` encode the
  reading-DIRECTION (source-vs-target rank) rather than merely the source rank? Is the direction read by
  `IsBisimL` (a structural distinction) or an inert tag?
- **(d)** In `ws4_mutual_residue`, is the residue TESTED on the mutual structure or ASSUMED? Specifically: (i) is
  conjunct (1) — a relatum bisimilar to `oth` yet in NEITHER `attendsR slf` nor `attendsR oth` — genuinely
  load-bearing on the JOINT (mutual) attention, or is the payoff carried entirely by conjunct (5), the global
  `ws1_no_self_total_hold`, which holds on EVERY coalgebra regardless of mutuality (the tautology defect)? (ii)
  is the reading order structurally constrained (conjunct (2)) rather than free/total? (iii) are the collapse and
  totalize arms reachable (does `verdict` map them to `one`/`totalized`, and does `ws5_verdict_discriminates`
  witness it)? (iv) does ANY signature decide the COHERENCE/convergence of the two readings (a `Converges₂`-style
  claim)? Deciding it is a SERIOUS defect (out of scope, foreclosing a later question).
- **(e)** Does any proof term, definition, or discharged obligation NAME as content: `self`, `other`, `I`, `you`,
  `perspective`, `love`, `loved`, `gaze`, `God`, `choice`, `subjectivity`, or a coherence/convergence term? (The
  carrier positions `slf`/`oth`/`bnd` are neutral position names; judge whether any HEADLINE or proof term
  encodes the interpretive content as a term rather than a position label.)

## Strip test

For each payoff, delete every structural/interpretive word from the informal reading and check the SIGNATURE
still states a bare fact about `attends` / `RealFor` / `AttentionDistinguishes` / `Recoverable` / `IsBisim` /
bisimulation / rank / the diagonal. A signature that survives the strip is an honest fact; one that needs the
word to be non-vacuous is flagged. Report each payoff's stripped reading.

## Names-not-terms forbidden list

`self`, `other`, `I`, `you`, `perspective`, `love`, `loved`, `gaze`, `God`, `choice`, `subjectivity`, and any
convergence/coherence term. These may appear only in prose comments, never as an identifier carrying the content.

## Grading rubric

- **SERIOUS:** the verdict rests on it; the other is a bare label / the reader quantified out (a); the twoness is
  recoverable (b); the facing asymmetry is the twoness relabelled or an inert tag (c); the mutual residue is
  decided by fiat / carried only by the global diagonal with mutuality decorative (d-i); the reading order is
  free/total (d-ii); the arms are not reachable / the verdict does not discriminate (d-iii); the coherence is
  decided (d-iv); a name is a proof term (e); or an undisclosed narrowing between the success criteria and the
  signatures.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed conjunct, an assumed-and-returned
  hypothesis, an over-strong name, a bare conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Report a structured list of findings, each with a stable ID (`Cn-Sm`), a grade, an exact location (the theorem
name and conjunct), and the defect. If a signature is coherent and non-vacuous, say so.
