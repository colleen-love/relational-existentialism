/-
# Inside vs outside: identity is `≈`, and the outside cannot read it (the inversion)

The founding commitment, **restated** (the doctrinal inversion of [03.3](../../docs/spec/03.3-decoherence.md)):
a self's identity **is** its first-person relational unfolding `≈` ([`We.bisim`](We.lean), `νΘ`),
and the third-person observational identity `≅` is a **strictly lossy projection** of it. We do not
try to prove full abstraction (`≈ = ≅`) — that would *contradict* the theory's own limitative core
(you cannot completely view from outside what you relate to: `Relating`, `Seam`). Instead we adopt
and **prove** the inequality:

* `≅` — **observational (trace) equivalence**, `ObsEq`: the *outside* view. Two states are
  `≅`-equal iff no external observer, recording sequences of observations, can tell them apart.
* **Soundness `≈ ⊆ ≅`** (`bisim_le_obsEq`): if two states are the same *inside* (bisimilar), no
  outside observation separates them. Lived sameness ⇒ observed sameness. `[proved]`
* **Strictness `≈ ⊊ ≅`** (`bisim_ne_obsEq`, with the witness `p0`/`q0`): there are states that are
  *observationally identical from outside yet not bisimilar inside* — the classic "early vs late
  choice." The outside underdetermines the inside. `[proved]`
* **The inside→outside map** (`livedToObserved`): soundness gives a canonical surjection
  `𝔼 = D/≈ ↠ D/≅` — the *forgetting from inside to outside*, the decoherence of identity. It is
  **not injective** (`livedToObserved_not_injective`): distinct lived selves collapse to one
  observed self. Its kernel — `≅`-equal, `≈`-distinct — is the formal address of the **first-person
  surplus**: the part of who you are that exceeds how you appear. `[proved]`

The interpretation (`≈` = lived first-person identity, `≅` = observed projection) is a `[reading]`;
the inequality, the soundness, and the non-injectivity are theorems. *You are your lived relating,
which exceeds how you appear.*

**Notation.** `≈` is bisimulation (`We.bisim`), `≅` is observational equivalence (`ObsEq`, below).
The *finer* relation is `≈`, the coarser `≅` (the model-theoretic / Hennessy–Milner convention —
bisimilarity finer than observational equivalence). We avoid `≡` for `≅`: in Agda `≡` is
propositional equality, the *finest* relation, so reusing it for the coarsest would invert it.

**Scope of `≅`.** A2's prose defines the observational identity *contextually* (`∀ C[-], C[s]=C[t]`).
Here `≅` is realized **concretely as trace equivalence** — one particular observational equivalence,
the bounded "record the observation sequence" observer. Whether trace equivalence equals the full
contextual `≅` is the context-lemma question the theory deliberately leaves open (proving them equal
would be the full abstraction the inversion denies); `≈ ⊊ ≅` is proved for *this* concrete `≅`, and
a fortiori the inside exceeds this bounded outside.
-/
import Scratch.We

namespace RelExist.Identity

open RelExist.We

universe u v
variable {X : Type u} {O : Type v}

/-! ### The outside view: observational (trace) equivalence `≅` -/

/-- A finite **observation-trace** from a state: the sequence of observations recorded along a
path. `single` observes the state and stops; `step'` observes the state and continues from a
successor. This is everything an *external* observer can record. -/
inductive HasTrace (obs : X → O) (step : X → X → Prop) : X → List O → Prop where
  | single (a : X) : HasTrace obs step a [obs a]
  | step' (a a' : X) (w : List O) :
      step a a' → HasTrace obs step a' w → HasTrace obs step a (obs a :: w)

/-- One-step inversion of `HasTrace`: a trace is either the bare observation, or the observation
followed by a trace of a successor. -/
theorem hasTrace_succ_iff {obs : X → O} {step : X → X → Prop} {a : X} {w : List O} :
    HasTrace obs step a w ↔
      w = [obs a] ∨ ∃ a' w', step a a' ∧ w = obs a :: w' ∧ HasTrace obs step a' w' := by
  constructor
  · intro h
    cases h with
    | single a => exact Or.inl rfl
    | step' a a' w hs ht => exact Or.inr ⟨a', w, hs, rfl, ht⟩
  · rintro (rfl | ⟨a', w', hs, rfl, ht⟩)
    · exact HasTrace.single a
    · exact HasTrace.step' a a' w' hs ht

/-- **Observational identity `≅`** — the lossy *outside* view: same set of observation-traces. -/
def ObsEq (obs : X → O) (step : X → X → Prop) (a b : X) : Prop :=
  ∀ w, HasTrace obs step a w ↔ HasTrace obs step b w

theorem obsEq_refl (obs : X → O) (step : X → X → Prop) (a : X) : ObsEq obs step a a :=
  fun _ => Iff.rfl

theorem obsEq_symm {obs : X → O} {step : X → X → Prop} {a b : X}
    (h : ObsEq obs step a b) : ObsEq obs step b a := fun w => (h w).symm

theorem obsEq_trans {obs : X → O} {step : X → X → Prop} {a b c : X}
    (hab : ObsEq obs step a b) (hbc : ObsEq obs step b c) : ObsEq obs step a c :=
  fun w => (hab w).trans (hbc w)

/-! ### Soundness: `≈ ⊆ ≅` — lived sameness implies observed sameness -/

/-- One-step destructor for `≈` (from `bisim_unfold`): equal observation, and matched successors. -/
theorem bisim_dest {obs : X → O} {step : X → X → Prop} {a b : X} (h : bisim obs step a b) :
    obs a = obs b ∧
    (∀ a', step a a' → ∃ b', step b b' ∧ bisim obs step a' b') ∧
    (∀ b', step b b' → ∃ a', step a a' ∧ bisim obs step a' b') := by
  have h' : (Step obs step) (bisim obs step) a b := by rw [bisim_unfold]; exact h
  exact h'

/-- Bisimilar states realize the **same traces** — the forward half of soundness. -/
theorem hasTrace_of_bisim {obs : X → O} {step : X → X → Prop} {a : X} {w : List O}
    (htr : HasTrace obs step a w) :
    ∀ b, bisim obs step a b → HasTrace obs step b w := by
  induction htr with
  | single a =>
    intro b h
    obtain ⟨ho, _, _⟩ := bisim_dest h
    rw [ho]; exact HasTrace.single b
  | step' a a' w hstep _ ih =>
    intro b h
    obtain ⟨ho, hf, _⟩ := bisim_dest h
    obtain ⟨b', hstepb, hb'⟩ := hf a' hstep
    rw [ho]; exact HasTrace.step' b b' w hstepb (ih b' hb')

/-- **Soundness, `≈ ⊆ ≅`.** Two states that are the same *inside* (bisimilar) are indistinguishable
*outside*: no sequence of observations separates them. Lived sameness ⇒ observed sameness. -/
theorem bisim_le_obsEq {obs : X → O} {step : X → X → Prop} {a b : X}
    (h : bisim obs step a b) : ObsEq obs step a b := by
  intro w
  exact ⟨fun htr => hasTrace_of_bisim htr b h,
         fun htr => hasTrace_of_bisim htr a (bisim_symm obs step h)⟩

/-! ### The inside→outside map: the decoherence of identity -/

/-- `≅` as a `Setoid`, so the *observed world* is a quotient. -/
def obsSetoid (obs : X → O) (step : X → X → Prop) : Setoid X where
  r := ObsEq obs step
  iseqv := ⟨obsEq_refl obs step, obsEq_symm, obsEq_trans⟩

/-- **The observed world `D/≅`** — the outside's quotient, coarser than the lived `𝔼 = D/≈`. -/
abbrev ObservedWorld (obs : X → O) (step : X → X → Prop) : Type _ :=
  Quotient (obsSetoid obs step)

/-- **The forgetting from inside to outside**, `𝔼 = D/≈ ↠ D/≅`. Well-defined precisely by
soundness (`bisim_le_obsEq`): every lived self has a well-defined observed shadow. This is the
*decoherence of identity* — the same shape as `ptrace`/`dephase` on states. -/
def livedToObserved (obs : X → O) (step : X → X → Prop) :
    World obs step → ObservedWorld obs step :=
  Quotient.lift (fun a => Quotient.mk (obsSetoid obs step) a)
    (fun _ _ h => Quotient.sound (bisim_le_obsEq h))

/-! ### Strictness `≈ ⊊ ≅` — a witness: observationally identical, not bisimilar

The classic "early vs late choice." Both `p0` and `q0` show `A`, then `M`, then either `B` or `C`
— identical trace languages. But `p0` defers the choice (one `M`-state that can still do both `B`
and `C`), while `q0` commits at the first step (two `M`-states, one only-`B`, one only-`C`). No
outside observer can tell them apart; inside, they are different selves. -/

inductive Obs | oA | oM | oB | oC
  deriving DecidableEq, Repr

inductive St | p0 | p1 | pB | pC | q0 | qL | qR | qLB | qRC
  deriving DecidableEq, Repr

open Obs St

/-- What each state shows to an observer. -/
def obsW : St → Obs
  | p0 => oA | p1 => oM | pB => oB | pC => oC
  | q0 => oA | qL => oM | qR => oM | qLB => oB | qRC => oC

/-- The successors of each state. -/
def succW : St → List St
  | p0 => [p1]
  | p1 => [pB, pC]
  | q0 => [qL, qR]
  | qL => [qLB]
  | qR => [qRC]
  | _ => []

/-- The transition relation of the witness system. -/
def stepW (a b : St) : Prop := b ∈ succW a

/-- Leaf states (no successors) have exactly the single one-observation trace. -/
theorem charLeaf {s : St} (hs : succW s = []) (w : List Obs) :
    HasTrace obsW stepW s w ↔ w = [obsW s] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (h | ⟨a', _, hstep, _, _⟩)
    · exact h
    · exact absurd hstep (by simp [stepW, hs])
  · intro h; exact Or.inl h

theorem charP1 (w : List Obs) :
    HasTrace obsW stepW p1 w ↔ w = [oM] ∨ w = [oM, oB] ∨ w = [oM, oC] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (rfl | ⟨a', w', hstep, rfl, htr⟩)
    · exact Or.inl rfl
    · have hmem : a' = pB ∨ a' = pC := by
        have hm : a' ∈ succW p1 := hstep
        simpa [succW] using hm
      rcases hmem with rfl | rfl
      · rw [(charLeaf (s := pB) rfl w').1 htr]; exact Or.inr (Or.inl rfl)
      · rw [(charLeaf (s := pC) rfl w').1 htr]; exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨pB, [oB], by simp [stepW, succW], rfl, (charLeaf (s := pB) rfl [oB]).2 rfl⟩
    · exact Or.inr ⟨pC, [oC], by simp [stepW, succW], rfl, (charLeaf (s := pC) rfl [oC]).2 rfl⟩

theorem charQL (w : List Obs) :
    HasTrace obsW stepW qL w ↔ w = [oM] ∨ w = [oM, oB] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (rfl | ⟨a', w', hstep, rfl, htr⟩)
    · exact Or.inl rfl
    · have : a' = qLB := by
        have hm : a' ∈ succW qL := hstep
        simpa [succW] using hm
      subst this
      rw [(charLeaf (s := qLB) rfl w').1 htr]; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨qLB, [oB], by simp [stepW, succW], rfl, (charLeaf (s := qLB) rfl [oB]).2 rfl⟩

theorem charQR (w : List Obs) :
    HasTrace obsW stepW qR w ↔ w = [oM] ∨ w = [oM, oC] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (rfl | ⟨a', w', hstep, rfl, htr⟩)
    · exact Or.inl rfl
    · have : a' = qRC := by
        have hm : a' ∈ succW qR := hstep
        simpa [succW] using hm
      subst this
      rw [(charLeaf (s := qRC) rfl w').1 htr]; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨qRC, [oC], by simp [stepW, succW], rfl, (charLeaf (s := qRC) rfl [oC]).2 rfl⟩

theorem charP0 (w : List Obs) :
    HasTrace obsW stepW p0 w ↔
      w = [oA] ∨ w = [oA, oM] ∨ w = [oA, oM, oB] ∨ w = [oA, oM, oC] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (rfl | ⟨a', w', hstep, rfl, htr⟩)
    · exact Or.inl rfl
    · have : a' = p1 := by
        have hm : a' ∈ succW p0 := hstep
        simpa [succW] using hm
      subst this
      rcases (charP1 w').1 htr with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨p1, [oM], by simp [stepW, succW], rfl, (charP1 [oM]).2 (Or.inl rfl)⟩
    · exact Or.inr ⟨p1, [oM, oB], by simp [stepW, succW], rfl, (charP1 _).2 (Or.inr (Or.inl rfl))⟩
    · exact Or.inr ⟨p1, [oM, oC], by simp [stepW, succW], rfl, (charP1 _).2 (Or.inr (Or.inr rfl))⟩

theorem charQ0 (w : List Obs) :
    HasTrace obsW stepW q0 w ↔
      w = [oA] ∨ w = [oA, oM] ∨ w = [oA, oM, oB] ∨ w = [oA, oM, oC] := by
  rw [hasTrace_succ_iff]
  constructor
  · rintro (rfl | ⟨a', w', hstep, rfl, htr⟩)
    · exact Or.inl rfl
    · have hmem : a' = qL ∨ a' = qR := by
        have hm : a' ∈ succW q0 := hstep
        simpa [succW] using hm
      rcases hmem with rfl | rfl
      · rcases (charQL w').1 htr with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases (charQR w').1 htr with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨qL, [oM], by simp [stepW, succW], rfl, (charQL [oM]).2 (Or.inl rfl)⟩
    · exact Or.inr ⟨qL, [oM, oB], by simp [stepW, succW], rfl, (charQL _).2 (Or.inr rfl)⟩
    · exact Or.inr ⟨qR, [oM, oC], by simp [stepW, succW], rfl, (charQR _).2 (Or.inr rfl)⟩

/-- **From outside, `p0` and `q0` are identical** — the same trace language. -/
theorem obsEq_p0_q0 : ObsEq obsW stepW p0 q0 := by
  intro w; rw [charP0, charQ0]

/-- **From inside, `p0` and `q0` are different** — not bisimilar. `p0`'s single `M`-successor can
still do both `B` and `C`; neither of `q0`'s `M`-successors can, so the move cannot be matched. -/
theorem not_bisim_p0_q0 : ¬ bisim obsW stepW p0 q0 := by
  intro h
  obtain ⟨_, hf, _⟩ := bisim_dest h
  obtain ⟨b', hb', hpb'⟩ := hf p1 (by simp [stepW, succW])
  have hmem : b' = qL ∨ b' = qR := by
    have hm : b' ∈ succW q0 := hb'
    simpa [succW] using hm
  rcases hmem with rfl | rfl
  · obtain ⟨_, hf1, _⟩ := bisim_dest hpb'
    obtain ⟨c', hc', hpc'⟩ := hf1 pC (by simp [stepW, succW])
    have : c' = qLB := by
      have hm : c' ∈ succW qL := hc'
      simpa [succW] using hm
    subst this
    obtain ⟨hobs, _, _⟩ := bisim_dest hpc'
    simp [obsW] at hobs
  · obtain ⟨_, hf1, _⟩ := bisim_dest hpb'
    obtain ⟨c', hc', hpc'⟩ := hf1 pB (by simp [stepW, succW])
    have : c' = qRC := by
      have hm : c' ∈ succW qR := hc'
      simpa [succW] using hm
    subst this
    obtain ⟨hobs, _, _⟩ := bisim_dest hpc'
    simp [obsW] at hobs

/-- **The residue, as an existence.** There are states observationally identical yet not bisimilar:
the outside cannot read the inside. -/
theorem obsEq_and_not_bisim :
    ∃ a b : St, ObsEq obsW stepW a b ∧ ¬ bisim obsW stepW a b :=
  ⟨p0, q0, obsEq_p0_q0, not_bisim_p0_q0⟩

/-- **`≈ ⊊ ≅`, as relations.** Lived identity and observed identity provably differ: with soundness
(`bisim_le_obsEq`) this is the strict inclusion — the inside is strictly finer than the outside. -/
theorem bisim_ne_obsEq : bisim obsW stepW ≠ ObsEq obsW stepW := by
  intro h
  apply not_bisim_p0_q0
  rw [h]; exact obsEq_p0_q0

/-- **The forgetting from inside to outside is not injective** — distinct lived selves (`p0`, `q0`)
collapse to one observed self. The kernel `≅`-equal/`≈`-distinct is the **first-person surplus**:
who you are exceeds how you appear. -/
theorem livedToObserved_not_injective :
    ¬ Function.Injective (livedToObserved obsW stepW) := by
  intro hinj
  apply not_bisim_p0_q0
  have heq : Quotient.mk (bisimSetoid obsW stepW) p0
           = Quotient.mk (bisimSetoid obsW stepW) q0 := by
    apply hinj
    show Quotient.mk (obsSetoid obsW stepW) p0 = Quotient.mk (obsSetoid obsW stepW) q0
    exact Quotient.sound obsEq_p0_q0
  exact Quotient.exact heq

/-! ### The headline: the surplus is exactly nondeterminism

The first-person surplus `≈ ⊊ ≅` exists **only** because of branching. We prove the general
theorem: in a **deterministic** system, `≈ = ≅` — the outside trace recovers the lived identity
in full. Equivalently (contrapositive): *a surplus implies branching* — no first-person remainder
without the freedom to have done otherwise. The witness above (which is genuinely nondeterministic,
`not_deterministic_stepW`) shows the hypothesis is necessary; branching is **necessary but not
sufficient** (a system can branch redundantly and still collapse). -/

/-- A transition system is **deterministic** when each state has at most one successor — no
branching, no "could have done otherwise." -/
def Deterministic (step : X → X → Prop) : Prop := ∀ {x y z}, step x y → step x z → y = z

/-- Every trace is nonempty (a system always exhibits *something* now). -/
theorem hasTrace_ne_nil {obs : X → O} {step : X → X → Prop} {x : X} {w : List O}
    (h : HasTrace obs step x w) : w ≠ [] := by
  cases h <;> simp

/-- The only length-one trace of `x` reads off its current observation. -/
theorem hasTrace_single_eq {obs : X → O} {step : X → X → Prop} {x : X} {o : O}
    (h : HasTrace obs step x [o]) : o = obs x := by
  rw [hasTrace_succ_iff] at h
  rcases h with h | ⟨_, _, _, heq, _⟩
  · rw [List.cons.injEq] at h; exact h.1
  · rw [List.cons.injEq] at heq; exact heq.1

/-- Observationally equal states agree on the current observation. -/
theorem obsEq_obs {obs : X → O} {step : X → X → Prop} {a b : X}
    (h : ObsEq obs step a b) : obs a = obs b :=
  hasTrace_single_eq ((h [obs a]).1 (HasTrace.single a))

/-- From the outside you can read off that a successor *exists* and what it shows: if `a ≅ b` and
`a` can step to `a'`, then `b` can step to some `b'` showing the same observation. -/
theorem obsEq_step {obs : X → O} {step : X → X → Prop} {a b a' : X}
    (h : ObsEq obs step a b) (hstep : step a a') :
    ∃ b', step b b' ∧ obs b' = obs a' := by
  have hb2 : HasTrace obs step b [obs a, obs a'] :=
    (h _).1 (HasTrace.step' a a' [obs a'] hstep (HasTrace.single a'))
  rw [obsEq_obs h, hasTrace_succ_iff] at hb2
  rcases hb2 with h1 | ⟨b', w', hs, heq, ht⟩
  · simp at h1
  · rw [List.cons.injEq] at heq; obtain ⟨_, rfl⟩ := heq
    exact ⟨b', hs, (hasTrace_single_eq ht).symm⟩

/-- **The step lemma under determinism.** If `x ≅ y` and each steps (to its *unique* successor),
the successors are again `≅`. This is where branching would break things: with a unique successor,
trace-equality of the wholes forces trace-equality of the tails. -/
theorem deterministic_succ_obsEq {obs : X → O} {step : X → X → Prop}
    {x y x' y' : X} (h : ObsEq obs step x y) (hdet : Deterministic step)
    (hx' : step x x') (hy' : step y y') :
    ObsEq obs step x' y' := by
  intro w
  constructor
  · intro htx'
    have hy2 : HasTrace obs step y (obs x :: w) := (h _).1 (HasTrace.step' x x' w hx' htx')
    rw [obsEq_obs h, hasTrace_succ_iff] at hy2
    rcases hy2 with h1 | ⟨y'', _, hs, heq, ht⟩
    · rw [List.cons.injEq] at h1; exact absurd h1.2 (hasTrace_ne_nil htx')
    · rw [List.cons.injEq] at heq; obtain ⟨_, rfl⟩ := heq
      have : y'' = y' := hdet hs hy'; subst this; exact ht
  · intro hty'
    have hx2 : HasTrace obs step x (obs y :: w) := (h _).2 (HasTrace.step' y y' w hy' hty')
    rw [← obsEq_obs h, hasTrace_succ_iff] at hx2
    rcases hx2 with h1 | ⟨x'', _, hs, heq, ht⟩
    · rw [List.cons.injEq] at h1; exact absurd h1.2 (hasTrace_ne_nil hty')
    · rw [List.cons.injEq] at heq; obtain ⟨_, rfl⟩ := heq
      have : x'' = x' := hdet hs hx'; subst this; exact ht

/-- **The collapse.** In a deterministic system, observational equality `≅` *is* a bisimulation,
so `≅ ⊆ ≈`. (With soundness `≈ ⊆ ≅`, this gives `≈ = ≅`.) -/
theorem deterministic_obsEq_imp_bisim {obs : X → O} {step : X → X → Prop}
    {a b : X} (h : ObsEq obs step a b) (hdet : Deterministic step) : bisim obs step a b := by
  refine bisim_of_bisimulation obs step (R := ObsEq obs step) ?_ h
  intro x y hxy
  refine ⟨obsEq_obs hxy, ?_, ?_⟩
  · intro x' hx'
    obtain ⟨y', hy', _⟩ := obsEq_step hxy hx'
    exact ⟨y', hy', deterministic_succ_obsEq hxy hdet hx' hy'⟩
  · intro y' hy'
    obtain ⟨x', hx', _⟩ := obsEq_step (obsEq_symm hxy) hy'
    exact ⟨x', hx', deterministic_succ_obsEq hxy hdet hx' hy'⟩

/-- **The headline.** In a deterministic system the lived identity and the observed identity
*coincide*: `≈ ⟺ ≅`. The outside recovers the inside in full — there is no surplus. So the surplus,
where it exists, is the trace of **branches not taken**. -/
theorem deterministic_bisim_iff_obsEq {obs : X → O} {step : X → X → Prop}
    (hdet : Deterministic step) (a b : X) : bisim obs step a b ↔ ObsEq obs step a b := by
  constructor
  · intro hb; exact bisim_le_obsEq hb
  · intro ho; exact deterministic_obsEq_imp_bisim ho hdet

/-- The witness system is genuinely **nondeterministic** (`q0` branches to `qL` and `qR`) — so the
hypothesis of the collapse cannot be dropped: determinism is *necessary* for `≈ = ≅`. -/
theorem not_deterministic_stepW : ¬ Deterministic stepW := by
  intro hdet
  have hLR : St.qL = St.qR :=
    @hdet St.q0 St.qL St.qR (by simp [stepW, succW]) (by simp [stepW, succW])
  exact absurd hLR (by decide)

/-! ### The requirements for the surplus: nondeterminism and a relating

The headline isolated one *sufficient* condition for collapse (determinism). Here we pin the
**exact** boundary and read off the **two necessary requirements** for a surplus to exist at all.
A surplus needs (1) **nondeterminism** — branching, "could have done otherwise" — and (2) a
**relating** — two distinct selves whose *appearances coincide* (`a ≅ b`). Crucially, neither alone
*nor both together* forces a surplus: the exact condition is a single fixed-point statement — the
outside view `≅` **fails to be a bisimulation**. The surplus is not a count of selves but a relation
the branching tears. -/

/-- A relation `R` is a **bisimulation** (the back-and-forth shape `≈` is the *greatest* instance
of): related states agree now, and every move of one is matched by a move of the other into
again-related states. -/
def IsBisimulation (obs : X → O) (step : X → X → Prop) (R : X → X → Prop) : Prop :=
  ∀ a b, R a b →
    obs a = obs b ∧
      (∀ a', step a a' → ∃ b', step b b' ∧ R a' b') ∧
      (∀ b', step b b' → ∃ a', step a a' ∧ R a' b')

/-- The lived identity `≈` is a bisimulation — indeed the greatest one. -/
theorem bisim_isBisimulation (obs : X → O) (step : X → X → Prop) :
    IsBisimulation obs step (bisim obs step) :=
  fun _ _ h => bisim_dest h

/-- **No surplus**: every observationally-equal pair is bisimilar (`≅ ⊆ ≈`). With soundness
(`bisim_le_obsEq`, the reverse) this is exactly `≈ = ≅`. -/
def NoSurplus (obs : X → O) (step : X → X → Prop) : Prop :=
  ∀ a b, ObsEq obs step a b → bisim obs step a b

/-- **The exact boundary.** There is no surplus **iff** the outside view `≅` is itself a
bisimulation. (`→`: under no-surplus `≅ = ≈`, and `≈` is a bisimulation, so successors matched up to
`≈` are matched up to `≅` by soundness; `←`: coinduction — any bisimulation is `⊆ ≈`.) This single
fixed-point condition is the whole story: every sufficient condition for collapse must imply it. -/
theorem noSurplus_iff_obsEq_isBisimulation (obs : X → O) (step : X → X → Prop) :
    NoSurplus obs step ↔ IsBisimulation obs step (ObsEq obs step) := by
  constructor
  · intro hns a b hab
    obtain ⟨ho, hf, hb⟩ := bisim_dest (hns a b hab)
    refine ⟨ho, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', hab'⟩ := hf a' ha'
      exact ⟨b', hb', bisim_le_obsEq hab'⟩
    · intro b' hb'2
      obtain ⟨a', ha', hab'⟩ := hb b' hb'2
      exact ⟨a', ha', bisim_le_obsEq hab'⟩
  · intro hbis a b hab
    exact bisim_of_bisimulation obs step (R := ObsEq obs step) hbis hab

/-- **The master characterization.** A surplus exists **iff** `≅` is *not* a bisimulation — iff
there is a related pair `a ≅ b` and a move `a → a'` that no move of `b` can match *up to appearance*.
That is the irreducible requirement: not a number of selves, but a *relating* the branching tears. -/
theorem surplus_iff_obsEq_not_isBisimulation (obs : X → O) (step : X → X → Prop) :
    (∃ a b, ObsEq obs step a b ∧ ¬ bisim obs step a b)
      ↔ ¬ IsBisimulation obs step (ObsEq obs step) := by
  rw [← noSurplus_iff_obsEq_isBisimulation]
  constructor
  · rintro ⟨a, b, hab, hnab⟩ hns; exact hnab (hns a b hab)
  · intro hns; by_contra hcon; push_neg at hcon; exact hns hcon

/-- Determinism is **one** sufficient condition for collapse — it makes `≅` a bisimulation. -/
theorem deterministic_noSurplus {obs : X → O} {step : X → X → Prop}
    (hdet : Deterministic step) : NoSurplus obs step :=
  fun _ _ h => deterministic_obsEq_imp_bisim h hdet

theorem deterministic_obsEq_isBisimulation {obs : X → O} {step : X → X → Prop}
    (hdet : Deterministic step) : IsBisimulation obs step (ObsEq obs step) :=
  (noSurplus_iff_obsEq_isBisimulation obs step).1 (deterministic_noSurplus hdet)

/-- **Requirement 1 — nondeterminism.** A surplus forces branching: if `a ≅ b` yet `¬ a ≈ b`, the
system cannot be deterministic (contrapositive of the headline). -/
theorem surplus_imp_not_deterministic {obs : X → O} {step : X → X → Prop} {a b : X}
    (hab : ObsEq obs step a b) (hnab : ¬ bisim obs step a b) : ¬ Deterministic step :=
  fun hdet => hnab (deterministic_obsEq_imp_bisim hab hdet)

/-- **Requirement 2 — a relating.** A surplus *is*, by its nature, two **distinct selves bound by a
shared appearance**: the witnesses are non-bisimilar (genuinely different lived identities, hence
`a ≠ b`) yet observationally equal (related from outside). The surplus is irreducibly a *relation*
between two selves, never a property of one. -/
theorem surplus_imp_relating {obs : X → O} {step : X → X → Prop} {a b : X}
    (hab : ObsEq obs step a b) (hnab : ¬ bisim obs step a b) :
    a ≠ b ∧ ObsEq obs step a b ∧ ¬ bisim obs step a b :=
  ⟨fun h => hnab (h ▸ bisim_refl obs step a), hab, hnab⟩

/-! #### Neither requirement suffices, even together

A concrete **nondeterministic** system with **distinct selves** and yet **no surplus** — so the two
requirements, even jointly, do not *force* `≈ ⊊ ≅`. What is missing is the *relating*: here every
self wears its own appearance (the observations separate them), so `≅` is trivial and cannot tear. -/

inductive StN | n0 | na | nb
  deriving DecidableEq, Repr

open StN

/-- Three states, each with a *distinct* current observation. -/
def obsN : StN → Obs
  | n0 => oA | na => oM | nb => oB

def succN : StN → List StN
  | n0 => [na, nb]
  | na => [na]
  | nb => [nb]

/-- A genuinely **nondeterministic** system: `n0` branches to two *non*-bisimilar successors. -/
def stepN (a b : StN) : Prop := b ∈ succN a

theorem not_deterministic_stepN : ¬ Deterministic stepN := by
  intro hdet
  have hab : StN.na = StN.nb :=
    @hdet StN.n0 StN.na StN.nb (by simp [stepN, succN]) (by simp [stepN, succN])
  exact absurd hab (by decide)

/-- Distinct selves: `na` and `nb` are not bisimilar (their observations differ). -/
theorem na_not_bisim_nb : ¬ bisim obsN stepN na nb := by
  intro h
  obtain ⟨ho, _, _⟩ := bisim_dest h
  exact absurd ho (by decide)

/-- **No surplus** on `stepN`: the observations are injective on states, so `≅` forces equality and
collapses to `≈` trivially. There is no pair of distinct selves sharing an appearance. -/
theorem stepN_noSurplus : NoSurplus obsN stepN := by
  intro a b hab
  have ho : obsN a = obsN b := obsEq_obs hab
  have heq : a = b := by
    cases a <;> cases b <;> first | rfl | exact absurd ho (by decide)
  subst heq
  exact bisim_refl obsN stepN a

/-- **The two requirements do not suffice.** `stepN` is nondeterministic *and* has distinct selves,
yet has **no surplus**: branching + many selves does not imply `≈ ⊊ ≅`. The missing ingredient is
the *relating* — two selves that share an appearance — exactly the master characterization's
`¬ IsBisimulation ≅`. -/
theorem nondeterminism_and_selves_insufficient :
    ¬ Deterministic stepN ∧ ¬ bisim obsN stepN na nb ∧ NoSurplus obsN stepN :=
  ⟨not_deterministic_stepN, na_not_bisim_nb, stepN_noSurplus⟩

end RelExist.Identity
