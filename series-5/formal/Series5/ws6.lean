/-
`series-5/formal/ws6.lean`

WS6 — **Relating across levels, and attention as grade-shift.** Series 5, the deepest
technical workstream.

Owns: the depth-graded face (grade as an inert `ℤ`-label, GF1); cross-level edges as
graded composite faces; leak-free transport of `ws3_faces_never_annihilate`; a
non-terminating descent; the inherited + new incompleteness; attention as grade-shift; and
the distributive-law obligation (no strict law DL1, transcribed KS diagonal; a graded weak
law DL2, from the grade-shift being a `ℤ`-bijection).

To keep the module graph acyclic while honouring the WS4↔WS6 forward edge, WS6 owns the
cross-level-face objects `ViewAt`, `FaceReaches`, and the core `ws6_tower_unknowable`
(= a view's face misses an object); WS4 imports these and re-exports the no-view payoff
`ws4_no_completing_view`, proving the coincidence `ws4_unknowable_eq_noview` there.

Design doc: `series-5/spec/ws06-design.md`. Sorry-free; axiom-clean beyond Mathlib's
standard three.
-/
import Series5.ws3

universe u

open Cardinal QPF Functor Series5.WS1 Series5.WS2 Series5.WS3

namespace Series5.WS6

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## Part A — the graded face and cross-level leak-freeness (GF1)

The grade is an **inert `ℤ`-label**: the graded carrier is the WS1 labelled carrier at
label set `GLabel Q = ℤ × Q`. Composition (`lcomp`) acts on the *state* coordinate,
untouched by the grade, so leak-freeness transports *verbatim*, and grade-composition is
`ℤ`-addition — no bottom, so no grade is a floor (the payoff of choosing `ℤ` in WS2). -/

/-- A graded label: a quality `q : Q` with a depth grade `d : ℤ`. -/
abbrev GLabel (Q : Type u) : Type u := ULift.{u} ℤ × Q

/-- **Leak-free transport (A).** A cross-level relation composed through arbitrarily many
levels never drains its face to the empty object — `ws3_faces_never_annihilate` at the
graded label set `GLabel Q`, applied *verbatim*. The grade rides along untouched by
`lcomp`; `ℤ` has no bottom, so no grade is a floor. -/
theorem ws6_crosslevel_never_annihilate (t : LkObj κ (GLabel Q) (νLk κ (GLabel Q)))
    (ht : t.1.Nonempty) (hmem : ∀ p ∈ t.1, NonAtomic p.2) :
    NonAtomic (lcomp t) ∧ ∀ p ∈ (Cofix.dest (lcomp t)).1, NonAtomic p.2 :=
  ws3_faces_never_annihilate t ht hmem

/-! ## Part B — non-terminating descent and relating-to = composed-of -/

/-- `x` relates to `y` at grade `d`: `y` is a grade-`d` successor of `x`. -/
def RelatesAtGrade (x y : νLk κ (GLabel Q)) (d : ℤ) : Prop :=
  ∃ q : Q, (((ULift.up d, q) : GLabel Q), y) ∈ (lstr x).1

/-- `x` is composed of `y` at grade `d` (composition side). **HONEST NOTE (project-review-1.md
S2b):** this is *character-for-character the same definition* as `RelatesAtGrade` — there is
no second, independently-motivated composition-side definition. The genuine identification
duty (a composition-side relation built from `lcomp`, proved `↔` the observation side) is
therefore **OPEN**, not "definitional-only." This alias is kept only to name the two readings
of the one relation. -/
def IsComposedOfAtGrade (x y : νLk κ (GLabel Q)) (d : ℤ) : Prop :=
  ∃ q : Q, (((ULift.up d, q) : GLabel Q), y) ∈ (lstr x).1

/-- **Relating-to = being-composed-of, at a grade — `Iff.rfl` on ONE definition, NOT a
coincidence.** The two sides are identical by definition, so this carries no identification
content. The charter's coincidence duty for this payoff is **unmet / open** (see the note on
`IsComposedOfAtGrade`); it is *not* listed as a discharged coincidence. -/
theorem ws6_relating_is_composition (x y : νLk κ (GLabel Q)) (d : ℤ) :
    RelatesAtGrade x y d ↔ IsComposedOfAtGrade x y d := Iff.rfl

/-- A groundless descending spine: state `d` has one successor, state `d-1`, on a
grade-`(d-1)` edge. The state carrier is `ULift.{u} ℤ` (`ℤ : Type 0` cannot be an
`LkObj` carrier). Corecursion never bottoms out — because `ℤ` has no least element. -/
noncomputable def descCoalg (q0 : Q) (hinf : ℵ₀ ≤ κ) :
    ULift.{u} ℤ → LkObj κ (GLabel Q) (ULift.{u} ℤ) :=
  fun d => ⟨{(((⟨d.down - 1⟩ : ULift.{u} ℤ), q0), (⟨d.down - 1⟩ : ULift.{u} ℤ))},
            mk_singleton_lt hinf _⟩

/-- The descending-spine state at grade `d`. -/
noncomputable def descState (q0 : Q) (hinf : ℵ₀ ≤ κ) (d : ℤ) : νLk κ (GLabel Q) :=
  Cofix.corec (descCoalg q0 hinf) ⟨d⟩

/-- The descending spine's grade-`(d-1)` edge to its finer copy. -/
theorem desc_succ (q0 : Q) (hinf : ℵ₀ ≤ κ) (d : ℤ) :
    (((⟨d - 1⟩ : ULift.{u} ℤ), q0), descState q0 hinf (d - 1))
      ∈ (lstr (descState q0 hinf d)).1 := by
  have h := Cofix.dest_corec (descCoalg q0 hinf) (⟨d⟩ : ULift.{u} ℤ)
  show _ ∈ (Cofix.dest (descState q0 hinf d)).1
  rw [descState, h]
  show _ ∈ (LkMap (Cofix.corec (descCoalg q0 hinf)) (descCoalg q0 hinf ⟨d⟩)).1
  simp only [LkMap, descCoalg, PkMap_val, Set.image_singleton, Prod.map_apply, id_eq]
  exact Set.mem_singleton_iff.mpr rfl

/-- **Descent never terminates (B).** For a genuine descending spine, below any grade `d`
there is a strictly finer grade `d' < d` at which it relates to a further object — without
end, because no level is first (`ℤ` has no least element). The finer relatum is itself
non-atomic (it descends again), so the composite face never drains to empty. -/
theorem ws6_descent_nonterminating (q0 : Q) (hinf : ℵ₀ ≤ κ) (d : ℤ) :
    ∃ (finer : νLk κ (GLabel Q)) (d' : ℤ), d' < d ∧ RelatesAtGrade (descState q0 hinf d) finer d' :=
  ⟨descState q0 hinf (d - 1), d - 1, by omega, ⟨q0, desc_succ q0 hinf d⟩⟩

/-! ## Part C — incompleteness: inherited (INC1) + new (INC2) -/

/-- The attention support of `u`: the `< κ`-sized set of relations `u` attends to. -/
abbrev SelfSupport (u : (νPk κ).X) : Type u := ↥((νPk κ).str u).1

/-- **INC1 — the Lawvere/Cantor diagonal (inherited, carrier-independent).** No state's
attention support surjects onto its own space of self-descriptions. -/
theorem ws6_lawvere_incomplete (u : (νPk κ).X) :
    ¬ ∃ e : SelfSupport u → (SelfSupport u → Prop), Function.Surjective e := by
  rintro ⟨e, he⟩
  exact Function.cantor_surjective e he

/-- **INC1 — Ω complete-in-extent yet closed at no finite depth (inherited).** Ω faces all
of itself yet is self-membered. -/
theorem ws6_omega_nonterminating (hinf : ℵ₀ ≤ κ) :
    (face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf))
  ∧ (omegaState hinf ∈ ((νPk κ).str (omegaState hinf)).1) := by
  refine ⟨by rw [omega_face hinf, reachSet_omega hinf], ?_⟩
  rw [omega_selfsingleton hinf]; rfl

/-- A **view** at a level: an object together with its level. Its face is its colimit
successor structure (`FaceReaches`). (Simplified from the design's explicit edge field;
the positioned face is captured by `RelatesInf` on the object.) -/
structure ViewAt (T : Tower Q) where
  level : T.Idx
  obj   : (T.lvl level).carrier

/-- What a view's face reaches across the tower: the colimit successors of its object. -/
def FaceReaches (T : Tower Q) (v : ViewAt T) (y : Winf T) : Prop :=
  RelatesInf T (toColim T v.obj) y

/-- **INC2 — the tower is unknowable from any level.** A view at level `α` sees, through
its face, only `< κ_α` objects; but no level is last, so a higher level over-populates
`W_∞` (`ws3_no_top`), and the view's face misses an object. The epistemic face of
no-view-from-nowhere. **Honest scope (pass-2 R1):** the content is exactly `ws3_no_top`
(`FaceReaches` = `RelatesInf`); this is no-top read positionally, not an independent
face-reach argument — see `ws4_no_completing_view`. -/
theorem ws6_tower_unknowable (T : Tower Q) (hQ : Nonempty Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (v : ViewAt T) :
    ∃ y : Winf T, ¬ FaceReaches T v y := by
  have h := ws3_no_top T hQ hunb (toColim T v.obj)
  unfold FaceReaches
  push_neg at h
  exact h

/-! ## Part D — the bialgebra obligation: no strict law (DL1), graded weak law (DL2) -/

/-- The unit of the composition monad: the one-part whole `{x}`. -/
noncomputable def pkPure (hinf : ℵ₀ ≤ κ) {X : Type u} (x : X) : PkObj κ X :=
  ⟨{x}, mk_singleton_lt hinf x⟩

lemma mk_pair_lt (hinf : ℵ₀ ≤ κ) {X : Type u} (a b : X) :
    Cardinal.mk (↥({a, b} : Set X)) < κ := by
  have hfin : ({a, b} : Set X).Finite := (Set.finite_singleton b).insert a
  exact lt_of_lt_of_le (Cardinal.lt_aleph0_iff_set_finite.mpr hfin) hinf

/-- A strict distributive law of `(P_κ, pure)` over itself (Klin–Salamanca's setting). The
depth grade is an inert coordinate the four-set diagonal ignores, so no *graded* strict law
exists either. -/
structure DistLaw (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) where
  lam : ∀ {X : Type u}, PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)
  natural : ∀ {X Y : Type u} (f : X → Y) (𝒮 : PkObj κ (PkObj κ X)),
    lam (PkMap κ (PkMap κ f) 𝒮) = PkMap κ (PkMap κ f) (lam 𝒮)
  unit_T : ∀ {X : Type u} (t : PkObj κ X), lam (pkPure hinf t) = PkMap κ (pkPure hinf) t
  unit_F : ∀ {X : Type u} (t : PkObj κ X), lam (PkMap κ (pkPure hinf) t) = pkPure hinf t

private abbrev ksBB : Type u := ULift.{u} (Bool × Bool)
private abbrev ksBt : Type u := ULift.{u} Bool
private def ksE (x y : Bool) : ksBB := ⟨(x, y)⟩
private def ksF (p : ksBB) : ksBt := ⟨p.down.1⟩
private def ksG (p : ksBB) : ksBt := ⟨p.down.2⟩
private def ksH (p : ksBB) : ksBt := ⟨xor p.down.1 p.down.2⟩

/-- **DL1 — no strict (graded) distributive law (Impossibility, inherited KS diagonal).**
No strict distributive law of `P_κ` over itself exists; the depth grade is inert, so no
strict graded law exists either. Transcribed from Series 3 `ws3_no_distributive_law`. -/
theorem ws6_no_strict_graded_law (hinf : ℵ₀ ≤ κ) : IsEmpty (DistLaw κ hinf) := by
  refine ⟨fun l => ?_⟩
  let univB : PkObj κ ksBt := ⟨{⟨false⟩, ⟨true⟩}, mk_pair_lt hinf _ _⟩
  let S12 : PkObj κ ksBB := ⟨{ksE false false, ksE false true}, mk_pair_lt hinf _ _⟩
  let S34 : PkObj κ ksBB := ⟨{ksE true false, ksE true true}, mk_pair_lt hinf _ _⟩
  let W : PkObj κ (PkObj κ ksBB) := ⟨{S12, S34}, mk_pair_lt hinf _ _⟩
  have hfS12 : PkMap κ ksF S12 = pkPure hinf (⟨false⟩ : ksBt) := by
    apply Subtype.ext; show ksF '' S12.1 = {(⟨false⟩ : ksBt)}; rw [Set.image_pair]; simp [ksF, ksE]
  have hfS34 : PkMap κ ksF S34 = pkPure hinf (⟨true⟩ : ksBt) := by
    apply Subtype.ext; show ksF '' S34.1 = {(⟨true⟩ : ksBt)}; rw [Set.image_pair]; simp [ksF, ksE]
  have hgS12 : PkMap κ ksG S12 = univB := by
    apply Subtype.ext; show ksG '' S12.1 = univB.1; rw [Set.image_pair]; rfl
  have hgS34 : PkMap κ ksG S34 = univB := by
    apply Subtype.ext; show ksG '' S34.1 = univB.1; rw [Set.image_pair]; rfl
  have hhS12 : PkMap κ ksH S12 = univB := by
    apply Subtype.ext; show ksH '' S12.1 = univB.1; rw [Set.image_pair]; rfl
  have hhS34 : PkMap κ ksH S34 = univB := by
    apply Subtype.ext; show ksH '' S34.1 = univB.1; rw [Set.image_pair]
    show ({(ULift.up true : ksBt), ULift.up false}) = {ULift.up false, ULift.up true}
    rw [Set.pair_comm]
  have cf : PkMap κ (PkMap κ ksF) W = PkMap κ (pkPure hinf) univB := by
    apply Subtype.ext
    show (PkMap κ ksF) '' W.1 = (pkPure hinf) '' univB.1
    rw [show W.1 = {S12, S34} from rfl, Set.image_pair, hfS12, hfS34,
        show univB.1 = {(⟨false⟩ : ksBt), ⟨true⟩} from rfl, Set.image_pair]
  have cg : PkMap κ (PkMap κ ksG) W = pkPure hinf univB := by
    apply Subtype.ext
    show (PkMap κ ksG) '' W.1 = {univB}
    rw [show W.1 = {S12, S34} from rfl, Set.image_pair, hgS12, hgS34]; simp
  have ch : PkMap κ (PkMap κ ksH) W = pkPure hinf univB := by
    apply Subtype.ext
    show (PkMap κ ksH) '' W.1 = {univB}
    rw [show W.1 = {S12, S34} from rfl, Set.image_pair, hhS12, hhS34]; simp
  have If : PkMap κ (PkMap κ ksF) (l.lam W) = pkPure hinf univB := by
    rw [← l.natural ksF W, cf, l.unit_F univB]
  have Ig : PkMap κ (PkMap κ ksG) (l.lam W) = PkMap κ (pkPure hinf) univB := by
    rw [← l.natural ksG W, cg, l.unit_T univB]
  have Ih : PkMap κ (PkMap κ ksH) (l.lam W) = PkMap κ (pkPure hinf) univB := by
    rw [← l.natural ksH W, ch, l.unit_T univB]
  have hne : (l.lam W).1.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hh : (PkMap κ (PkMap κ ksF) (l.lam W)).1 = ∅ := by rw [PkMap_val, hemp]; simp
    rw [If] at hh
    exact absurd (hh ▸ (Set.mem_singleton univB) : univB ∈ (∅ : Set (PkObj κ ksBt)))
      (Set.not_mem_empty univB)
  obtain ⟨S, hS⟩ := hne
  have hfImg : PkMap κ ksF S = univB := by
    have hmem : PkMap κ ksF S ∈ (PkMap κ (PkMap κ ksF) (l.lam W)).1 := ⟨S, hS, rfl⟩
    rw [If] at hmem; exact hmem
  have singOf : ∀ (φ : ksBB → ksBt),
      PkMap κ (PkMap κ φ) (l.lam W) = PkMap κ (pkPure hinf) univB →
      φ '' S.1 = {(ULift.up false : ksBt)} ∨ φ '' S.1 = {(ULift.up true : ksBt)} := by
    intro φ hI
    have hmem : PkMap κ φ S ∈ (PkMap κ (PkMap κ φ) (l.lam W)).1 := ⟨S, hS, rfl⟩
    rw [hI, PkMap_val, show univB.1 = {(ULift.up false : ksBt), ULift.up true} from rfl,
        Set.image_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · left; rw [show φ '' S.1 = (PkMap κ φ S).1 from rfl, h]; rfl
    · right; rw [show φ '' S.1 = (PkMap κ φ S).1 from rfl, h]; rfl
  have hg := singOf ksG Ig
  have hh := singOf ksH Ih
  have hfeq : ksF '' S.1 = {(ULift.up false : ksBt), ULift.up true} := by
    have h := congrArg Subtype.val hfImg; simpa [PkMap_val] using h
  obtain ⟨p, hp, hpf⟩ : (ULift.up false : ksBt) ∈ ksF '' S.1 := by rw [hfeq]; left; rfl
  obtain ⟨q, hq, hqf⟩ : (ULift.up true : ksBt) ∈ ksF '' S.1 := by rw [hfeq]; right; rfl
  have hp1 : p.down.1 = false := by have := congrArg ULift.down hpf; simpa [ksF] using this
  have hq1 : q.down.1 = true := by have := congrArg ULift.down hqf; simpa [ksF] using this
  have hgpq : ksG p = ksG q := by
    rcases hg with h | h <;>
      · have a := (h ▸ Set.mem_image_of_mem ksG hp : _ ∈ ({_} : Set ksBt))
        have b := (h ▸ Set.mem_image_of_mem ksG hq : _ ∈ ({_} : Set ksBt))
        rw [Set.mem_singleton_iff.mp a, Set.mem_singleton_iff.mp b]
  have hhpq : ksH p = ksH q := by
    rcases hh with h | h <;>
      · have a := (h ▸ Set.mem_image_of_mem ksH hp : _ ∈ ({_} : Set ksBt))
        have b := (h ▸ Set.mem_image_of_mem ksH hq : _ ∈ ({_} : Set ksBt))
        rw [Set.mem_singleton_iff.mp a, Set.mem_singleton_iff.mp b]
  have hp2 : p.down.2 = q.down.2 := by have := congrArg ULift.down hgpq; simpa [ksG] using this
  have hx := congrArg ULift.down hhpq
  simp only [ksH] at hx
  rw [hp1, hq1, ← hp2] at hx
  revert hx
  cases p.down.2 <;> decide

/-! ### DL2 — the graded weak distributive law exists (grade-shift is a `ℤ`-bijection) -/

/-- The label grade-shift `d ↦ d + Δ`. -/
def gradeShiftLabel (Δ : ℤ) : GLabel Q → GLabel Q := fun p => (⟨p.1.down + Δ⟩, p.2)

theorem gradeShiftLabel_left (Δ : ℤ) (p : GLabel Q) :
    gradeShiftLabel (-Δ) (gradeShiftLabel Δ p) = p := by
  cases p with | mk d q => cases d with | up n => simp [gradeShiftLabel]

theorem gradeShiftLabel_right (Δ : ℤ) (p : GLabel Q) :
    gradeShiftLabel Δ (gradeShiftLabel (-Δ) p) = p := by
  cases p with | mk d q => cases d with | up n => simp [gradeShiftLabel]

/-- The label grade-shift is a bijection (inverse `gradeShiftLabel (-Δ)`). -/
theorem gradeShiftLabel_bij (Δ : ℤ) :
    Function.Bijective (gradeShiftLabel Δ : GLabel Q → GLabel Q) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨gradeShiftLabel (-Δ), gradeShiftLabel_left Δ, gradeShiftLabel_right Δ⟩

/-- `PkMap` of a bijection is a bijection. -/
theorem PkMap_bij {X Y : Type u} {f : X → Y} (hf : Function.Bijective f) :
    Function.Bijective (PkMap κ f) := by
  obtain ⟨g, hgf, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  refine Function.bijective_iff_has_inverse.mpr ⟨PkMap κ g, ?_, ?_⟩
  · intro s
    have hcomp : g ∘ f = id := funext hgf
    rw [← PkMap_comp, hcomp, PkMap_id]
  · intro s
    have hcomp : f ∘ g = id := funext hfg
    rw [← PkMap_comp, hcomp, PkMap_id]

/-- Grade-shift on a labelled structure (shift every edge's grade by `Δ`). -/
noncomputable def gradeShiftStr (Δ : ℤ) {X : Type u} (s : LkObj κ (GLabel Q) X) :
    LkObj κ (GLabel Q) X := PkMap κ (Prod.map (gradeShiftLabel Δ) id) s

/-- A **graded observation-coherent shift** (pass-2 R4: renamed from `GradedWeakDistLaw`, which
over-claimed). This is NOT a distributive law `λ : T F ⇒ F T` of the composition monad over the
observation functor — it carries none of the `DistLaw` monad laws (`natural`/`unit_T`/`unit_F`;
those live in `DistLaw`, used by the genuine impossibility `ws6_no_strict_graded_law`). It is a
grade-shift on labelled structures that is a bijection (`d ↦ d + Δ` is a `ℤ`-bijection, so
composition/union commute with it) and commutes with observation `LkMap` (the grade acts on
labels, observation on targets). That is the DL2 content actually delivered: grade-shift coheres
with level-wise observation, given the grade is an inert `ℤ`-label (GF1). The genuine graded
weak *distributive law* — an Egli–Milner-style `λ` commuting with observation *and* grade,
carrying the bialgebra laws — is **not** built here; it is open obligation #13. -/
structure GradedObsCoherentShift (κ : Cardinal.{u}) (Q : Type u) where
  shift    : ℤ → ∀ {X : Type u}, LkObj κ (GLabel Q) X → LkObj κ (GLabel Q) X
  bij      : ∀ (Δ : ℤ) {X : Type u}, Function.Bijective (fun s : LkObj κ (GLabel Q) X => shift Δ s)
  comm_obs : ∀ (Δ : ℤ) {X Y : Type u} (f : X → Y) (s : LkObj κ (GLabel Q) X),
               shift Δ (LkMap f s) = LkMap f (shift Δ s)

/-- **DL2 — a graded observation-coherent shift exists** (pass-2 R4: renamed from
`ws6_graded_weak_law_exists`; it is a grade-shift bijection commuting with observation, *not* a
weak distributive law — see `GradedObsCoherentShift`). Witnessed by `gradeShiftStr`: a
`ℤ`-bijection (inverse `gradeShiftStr (-Δ)`) commuting with observation. The same inertness of
the `ℤ`-grade that gives leak-freeness gives grade-commutation. The paired impossibility
`ws6_no_strict_graded_law` *is* about actual `DistLaw`s; the positive partner is this weaker
coherence, and the genuine graded weak distributive law stays open (#13). -/
theorem ws6_graded_obs_coherent_shift_exists (κ : Cardinal.{u}) (Q : Type u) :
    Nonempty (GradedObsCoherentShift κ Q) := by
  refine ⟨{ shift := fun Δ {X} s => gradeShiftStr Δ s, bij := ?_, comm_obs := ?_ }⟩
  · intro Δ X
    exact PkMap_bij ((gradeShiftLabel_bij Δ).prodMap Function.bijective_id)
  · intro Δ X Y f s
    apply Subtype.ext
    show (Prod.map (gradeShiftLabel Δ) (id : Y → Y))
            '' ((Prod.map (id : GLabel Q → GLabel Q) f) '' s.1)
       = (Prod.map (id : GLabel Q → GLabel Q) f)
            '' ((Prod.map (gradeShiftLabel Δ) (id : X → X)) '' s.1)
    rw [Set.image_image, Set.image_image]
    apply Set.image_congr'
    intro p; rfl

/-! ## Attention as grade-shift (AT1 — definable; reported Trivialized) -/

/-- **Attention is grade-shift.** Attending by `Δ` corecursively shifts every edge's grade
by `Δ`. Definable and structurally natural — but its coincidence with an independently
motivated attention notion (the Series 3 replicator AT2, or convergence AT3) is
open/negative on this carrier, so attention-as-grade-shift is reported **Trivialized** (a
success per §7: an honest negative). -/
noncomputable def attend (Δ : ℤ) (x : νLk κ (GLabel Q)) : νLk κ (GLabel Q) :=
  Cofix.corec (fun s => gradeShiftStr Δ (Cofix.dest s)) x

end Series5.WS6
