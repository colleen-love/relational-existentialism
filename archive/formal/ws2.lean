/-
`series-3/formal/ws2.lean`

WS2 (`series-3/spec/ws2/04-charter-design-review.md`): **`νP_κ` and its
bisimulation theory.** Commit `F = P_κ`; assemble Framings 1+3+4+2+5 as the WS2
deliverable, deferring the enrichment fork (Framing 6 / `W_Q`) to WS4.

Built on `ws1.lean` (imported as established, axiom-free theorems): `Coalg`,
`IsTerminalCoalg`, `PkObj`, `PkMap(_id/_comp)`, `exists_terminal_coalg`, `qpfPk`,
`Bisim`, `bisim_eq`, `hom_unique`, `lambek`, `omegaCoalg`, `emptyCoalg`,
`mk_empty_lt`, `mk_singleton_lt`, and the `Cofix` universal-property API.

## What is proved sorry-free

* A  existence, concrete carrier      `νPk`, `νPk_terminal`   (Cofix U.P., not `Classical.choose`)
* B  non-degeneracy                    `ws2_nondegenerate`
* C  bisim = identity (terminal form)  `ws2_bisim_eq`
* D  weak-pullback preservation        `PkRel`, `PkRel_le_comp` (⊆, the new content),
     (Lemma 3.1a, WS2-owned)           `PkRel_comp_le` (⊇), `PkRel_functorial`,
                                        `PkPreservesWeakPullback`, `ws2_weak_pullback`
* D3 composition / behavioural         `bisim_comp`, `ws2_bisim_behavioural`
* E  coinduction                       `ws2_coinduction`, `BisimUpToEquiv`, `ws2_coinduction_upto`
* assembled deliverable                `WS2Characterization`, `ws2_characterization`

## Honest hypothesis accounting (a correction to the design's §-notes)

The design threads `hreg : κ.IsRegular` through Component D "because the product
bound `<κ · <κ = <κ` needs regularity." **That is not so:** `Cardinal.mul_lt_of_lt`
needs only `ℵ₀ ≤ κ` (infinite), since `a·b = max(a,b)` for infinite cardinals — no
regularity. Accordingly this file threads only `hinf` where the product bound is
used (`PkRel_comp_le`, `bisim_comp`), and the SUBSTANTIVE direction `PkRel_le_comp`
(the genuine weak-pullback content) needs no cardinal hypothesis at all — only
`Classical.choice` to select middle points. `ws2_characterization` keeps the
charter's `IsRegular` hypothesis in its signature (for fidelity to the stated
"infinite regular κ"), marked `_hreg` since the proof does not consume it.

Direction note: the design (04 §D3, §"charter-reconciliation fix") states that
`bisim_comp` consumes the ⊆ direction `PkRel_le_comp`. On inspection it is the ⊇
direction `PkRel_comp_le` that `bisim_comp` uses — composing two bisimulation
witnesses over a shared middle *merges* them (⊇), it does not *decompose* one (⊆).
Both directions are proved here, so `bisim_comp` simply cites the correct one.

Everything is axiom-free beyond Mathlib's standard `propext`/`Classical.choice`/
`Quot.sound` (AFA is modeled coalgebraically, per WS2 Phase 1 §"Ambient theory" —
no set-theoretic AFA axiom is imported). `Classical.choice` is inherent to the
Mathlib base and to Component D's middle-selection, as Phase 1 anticipates.
-/
import ws1

universe u

open Cardinal QPF Functor Series3.WS1

namespace Series3.WS2

variable {κ : Cardinal.{u}}

/-- Relation composition (`= Rel.comp`, inlined to avoid `Rel` coercion friction):
`relComp R S x z ↔ ∃ y, R x y ∧ S y z`. -/
def relComp {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop) : X → Z → Prop :=
  fun x z => ∃ y, R x y ∧ S y z

/-! ## Component A — Existence, concrete carrier (Framing 4) -/

/-- The WS2 carrier: the final coalgebra of `P_κ` (`νP_κ`). -/
noncomputable def νPk (κ : Cardinal.{u}) : Coalg κ := ⟨Cofix (PkObj κ), Cofix.dest⟩

/-- Terminality of the *concrete* carrier `νPk`, from the `Cofix` universal
property (anamorphism + its `bisim'` uniqueness) — the corrected Component A,
with no `Classical.choose` and no iso transport. This is the same proof that
discharges WS1's `exists_terminal_coalg`, specialised to the concrete carrier. -/
theorem νPk_terminal (κ : Cardinal.{u}) : IsTerminalCoalg (νPk κ) := by
  intro C
  refine ⟨Cofix.corec C.str, fun x => Cofix.dest_corec C.str x, ?_⟩
  intro h hh
  funext x
  refine Cofix.bisim' (fun _ => True) h (Cofix.corec C.str) ?_ x trivial
  intro y _
  refine ⟨(QPF.repr (C.str y)).1,
          (fun i => h ((QPF.repr (C.str y)).2 i)),
          (fun i => Cofix.corec C.str ((QPF.repr (C.str y)).2 i)), ?_, ?_, ?_⟩
  · calc Cofix.dest (h y)
        = PkMap κ h (C.str y) := hh y
      _ = h <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]; rfl
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst, fun i => h ((QPF.repr (C.str y)).snd i)⟩ := by
            rw [← QPF.abs_map]; rfl
  · calc Cofix.dest (Cofix.corec C.str y)
        = Cofix.corec C.str <$> C.str y := Cofix.dest_corec C.str y
      _ = Cofix.corec C.str <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst,
            fun i => Cofix.corec C.str ((QPF.repr (C.str y)).snd i)⟩ := by rw [← QPF.abs_map]; rfl
  · intro i
    exact ⟨(QPF.repr (C.str y)).2 i, trivial, rfl, rfl⟩

/-! ## Component B — Non-degeneracy (Framing 3) -/

/-- The `νPk` carrier has at least two points: the images of the empty and the
self-singleton one-node coalgebras differ (their structure maps land on `∅` and a
nonempty singleton). Reuses WS1's `omegaCoalg`/`emptyCoalg`. -/
theorem ws2_nondegenerate (hinf : ℵ₀ ≤ κ) : ∃ a b : (νPk κ).X, a ≠ b := by
  obtain ⟨hΩ, hΩnat, -⟩ := νPk_terminal κ (omegaCoalg hinf)
  obtain ⟨hE, hEnat, -⟩ := νPk_terminal κ (emptyCoalg hinf)
  have hsω : ((νPk κ).str (hΩ PUnit.unit)).1 = {hΩ PUnit.unit} := by
    rw [hΩnat PUnit.unit]; simp [PkMap, omegaCoalg]
  have hsE : ((νPk κ).str (hE PUnit.unit)).1 = (∅ : Set (νPk κ).X) := by
    rw [hEnat PUnit.unit]; simp [PkMap, emptyCoalg]
  refine ⟨hE PUnit.unit, hΩ PUnit.unit, ?_⟩
  intro heq
  have hc : ((νPk κ).str (hE PUnit.unit)).1 = {hΩ PUnit.unit} := by rw [heq]; exact hsω
  rw [hsE] at hc
  have hmem : hΩ PUnit.unit ∈ (∅ : Set (νPk κ).X) := by rw [hc]; rfl
  exact Set.not_mem_empty _ hmem

/-! ## Component C — Bisimulation = identity, terminal form (Framing 1) -/

/-- Every `P_κ`-bisimulation on `νPk` is contained in the diagonal (WS1's
`bisim_eq` at the WS2 carrier). -/
theorem ws2_bisim_eq (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R) :
    ∀ x y, R x y → x = y :=
  bisim_eq (νPk_terminal κ) R hR

/-! ## Component D — Weak-pullback preservation (Framing 2, the new content) -/

/-- Barr relation lifting of `P_κ`: two κ-small sets are `PkRel R`-related iff
witnessed by a κ-small subset of the graph of `R` projecting onto both. -/
def PkRel {X Y : Type u} (R : X → Y → Prop) :
    PkObj κ X → PkObj κ Y → Prop := fun s t =>
  ∃ w : PkObj κ {p : X × Y // R p.1 p.2},
    PkMap κ (fun p => p.1.1) w = s ∧ PkMap κ (fun p => p.1.2) w = t

/-- **The SUBSTANTIVE direction (Lemma 3.1a proper): `P_κ` preserves weak
pullbacks.** From one κ-small witness over `graph (R∘S)`, select a middle point
per element (this is the only use of `Classical.choice`) and project to the two
factor graphs. Needs NO cardinal hypothesis: every constructed set is a `PkMap`
image of the given witness, hence `< κ` by inheritance. -/
theorem PkRel_le_comp {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : PkObj κ X) (u : PkObj κ Z) (h : PkRel (relComp R S) s u) :
    ∃ t, PkRel R s t ∧ PkRel S t u := by
  classical
  obtain ⟨w, hws, hwu⟩ := h
  refine ⟨PkMap κ (fun q => q.2.choose) w,
    ⟨PkMap κ (fun q => (⟨(q.1.1, q.2.choose), q.2.choose_spec.1⟩ :
        {p : X × Y // R p.1 p.2})) w, ?_, ?_⟩,
     PkMap κ (fun q => (⟨(q.2.choose, q.1.2), q.2.choose_spec.2⟩ :
        {p : Y × Z // S p.1 p.2})) w, ?_, ?_⟩
  · rw [← PkMap_comp]; exact hws
  · rw [← PkMap_comp]; rfl
  · rw [← PkMap_comp]; rfl
  · rw [← PkMap_comp]; exact hwu

/-- **The FREE direction (⊇).** Merge two witnesses over a shared middle by a
pullback; the κ-bound is the only cost and needs only `ℵ₀ ≤ κ` (product of two
`< κ` cardinals is `< κ`, `Cardinal.mul_lt_of_lt`) — NOT regularity. -/
theorem PkRel_comp_le (hinf : ℵ₀ ≤ κ) {X Y Z : Type u}
    (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : PkObj κ X) (u : PkObj κ Z) (h : ∃ t, PkRel R s t ∧ PkRel S t u) :
    PkRel (relComp R S) s u := by
  classical
  obtain ⟨t, ⟨wR, hRs, hRt⟩, ⟨wS, hSt, hSu⟩⟩ := h
  -- The pullback of the two witnesses over the shared middle `t`.
  let M := {ab : (↥wR.1) × (↥wS.1) //
      ((ab.1 : {p : X × Y // R p.1 p.2})).1.2 = ((ab.2 : {p : Y × Z // S p.1 p.2})).1.1}
  have hMlt : Cardinal.mk M < κ :=
    lt_of_le_of_lt (Cardinal.mk_subtype_le _)
      (by rw [Cardinal.mk_prod]; simpa using Cardinal.mul_lt_of_lt hinf wR.2 wS.2)
  -- The map into `graph (R∘S)`.
  let g : M → {p : X × Z // relComp R S p.1 p.2} := fun ab =>
    ⟨(((ab.1.1 : {p : X × Y // R p.1 p.2})).1.1, ((ab.1.2 : {p : Y × Z // S p.1 p.2})).1.2),
     ⟨((ab.1.1 : {p : X × Y // R p.1 p.2})).1.2,
      ((ab.1.1 : {p : X × Y // R p.1 p.2})).2,
      by rw [ab.2]; exact ((ab.1.2 : {p : Y × Z // S p.1 p.2})).2⟩⟩
  refine ⟨⟨Set.range g, lt_of_le_of_lt Cardinal.mk_range_le hMlt⟩, ?_, ?_⟩
  · -- first leg = s
    apply Subtype.ext
    show (fun p => p.1.1) '' Set.range g = s.1
    rw [← hRs]
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨_, ⟨ab, rfl⟩, rfl⟩
      exact ⟨(ab.1.1 : {p : X × Y // R p.1 p.2}), ab.1.1.2, rfl⟩
    · rintro x ⟨a, ha, rfl⟩
      have hmid : a.1.2 ∈ t.1 := by rw [← hRt]; exact ⟨a, ha, rfl⟩
      rw [← hSt] at hmid
      obtain ⟨b, hb, hba⟩ := hmid
      exact ⟨g ⟨(⟨a, ha⟩, ⟨b, hb⟩), hba.symm⟩, ⟨_, rfl⟩, rfl⟩
  · -- second leg = u
    apply Subtype.ext
    show (fun p => p.1.2) '' Set.range g = u.1
    rw [← hSu]
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨_, ⟨ab, rfl⟩, rfl⟩
      exact ⟨(ab.1.2 : {p : Y × Z // S p.1 p.2}), ab.1.2.2, rfl⟩
    · rintro z ⟨b, hb, rfl⟩
      have hmid : b.1.1 ∈ t.1 := by rw [← hSt]; exact ⟨b, hb, rfl⟩
      rw [← hRt] at hmid
      obtain ⟨a, ha, hab⟩ := hmid
      exact ⟨g ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, ⟨_, rfl⟩, rfl⟩

/-- Functoriality of the lifting on `Rel` — the equality both inclusions assemble
to. `P_κ` preserves weak pullbacks in the full (equational) sense. -/
theorem PkRel_functorial (hinf : ℵ₀ ≤ κ) {X Y Z : Type u}
    (R : X → Y → Prop) (S : Y → Z → Prop) :
    PkRel (relComp R S)
      = fun (s : PkObj κ X) (u : PkObj κ Z) => ∃ t, PkRel R s t ∧ PkRel S t u := by
  funext s u
  apply propext
  constructor
  · exact PkRel_le_comp R S s u
  · exact PkRel_comp_le hinf R S s u

/-- Weak-pullback preservation for `P_κ`, packaged as the WS2 predicate (the
substantive reflection-of-composition direction). -/
def PkPreservesWeakPullback (κ : Cardinal.{u}) : Prop :=
  ∀ {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : PkObj κ X) (u : PkObj κ Z),
    PkRel (relComp R S) s u → ∃ t, PkRel R s t ∧ PkRel S t u

theorem ws2_weak_pullback : PkPreservesWeakPullback κ :=
  fun R S s u h => PkRel_le_comp R S s u h

/-! ## Component D3 / behavioural, and the diagonal bisimulation -/

/-- The diagonal is a bisimulation on any coalgebra: push the structure map along
the diagonal `z ↦ (z, z)`. -/
def diagBisim (U : Coalg κ) : Bisim U (fun a b => a = b) where
  ζ := fun p => PkMap κ (fun z => (⟨(z, z), rfl⟩ : {q : U.X × U.X // q.1 = q.2})) (U.str p.1.1)
  nat_fst := fun p => by
    have : PkMap κ (fun q : {q : U.X × U.X // q.1 = q.2} => q.1.1)
        (PkMap κ (fun z => (⟨(z, z), rfl⟩ : {q : U.X × U.X // q.1 = q.2})) (U.str p.1.1))
        = U.str p.1.1 := by rw [← PkMap_comp]; exact PkMap_id _
    exact this.symm
  nat_snd := fun p => by
    have hp : p.1.1 = p.1.2 := p.2
    have : PkMap κ (fun q : {q : U.X × U.X // q.1 = q.2} => q.1.2)
        (PkMap κ (fun z => (⟨(z, z), rfl⟩ : {q : U.X × U.X // q.1 = q.2})) (U.str p.1.1))
        = U.str p.1.1 := by rw [← PkMap_comp]; exact PkMap_id _
    rw [← hp]; exact this.symm

/-- **Composition of bisimulations is a bisimulation** (transitivity — the D3
consequence of weak-pullback preservation). Given witnessing coalgebra structures
for `R` and `S` sharing a middle, the composed witness for each pair is *merged*
by `PkRel_comp_le`; this is the ⊇ direction (merge two witnesses), which is where
`hinf` (the product bound) enters. [Direction correction vs. the design's §D3: it
is the ⊇ inclusion, not ⊆, that a *merge* uses.] -/
noncomputable def bisim_comp (hinf : ℵ₀ ≤ κ) {R S : (νPk κ).X → (νPk κ).X → Prop}
    (hR : Bisim (νPk κ) R) (hS : Bisim (νPk κ) S) :
    Bisim (νPk κ) (relComp R S) := by
  classical
  have hwit : ∀ q : {p : (νPk κ).X × (νPk κ).X // relComp R S p.1 p.2},
      PkRel (relComp R S) ((νPk κ).str q.1.1) ((νPk κ).str q.1.2) := by
    intro q
    obtain ⟨y, hRy, hSy⟩ := q.2
    refine PkRel_comp_le hinf R S _ _ ⟨(νPk κ).str y, ?_, ?_⟩
    · exact ⟨hR.ζ ⟨(q.1.1, y), hRy⟩, (hR.nat_fst _).symm, (hR.nat_snd _).symm⟩
    · exact ⟨hS.ζ ⟨(y, q.1.2), hSy⟩, (hS.nat_fst _).symm, (hS.nat_snd _).symm⟩
  exact ⟨fun q => (hwit q).choose,
         fun q => ((hwit q).choose_spec.1).symm,
         fun q => ((hwit q).choose_spec.2).symm⟩

/-- **Behavioural equivalence = identity** on the terminal carrier: two states are
related by *some* bisimulation iff they are equal. (→) is `ws2_bisim_eq`; (←) is
the diagonal bisimulation. -/
theorem ws2_bisim_behavioural (x y : (νPk κ).X) :
    (∃ R, Nonempty (Bisim (νPk κ) R) ∧ R x y) ↔ x = y := by
  constructor
  · rintro ⟨R, ⟨hR⟩, hxy⟩
    exact ws2_bisim_eq R hR x y hxy
  · rintro rfl
    exact ⟨(fun a b => a = b), ⟨diagBisim (νPk κ)⟩, rfl⟩

/-! ## Component E — Coinduction, usable form (Framing 5) -/

/-- Plain coinduction principle: to prove `x = y`, exhibit a bisimulation. -/
theorem ws2_coinduction (R : (νPk κ).X → (νPk κ).X → Prop) (hR : Bisim (νPk κ) R)
    {x y} : R x y → x = y := ws2_bisim_eq R hR x y

/-- Reflexive–symmetric–transitive (equivalence) closure of a relation. -/
inductive EqvClosure {α : Type u} (R : α → α → Prop) : α → α → Prop
  | rel {a b} : R a b → EqvClosure R a b
  | refl (a) : EqvClosure R a a
  | symm {a b} : EqvClosure R a b → EqvClosure R b a
  | trans {a b c} : EqvClosure R a b → EqvClosure R b c → EqvClosure R a c

/-- Bisimulation up to equivalence: the equivalence closure of `R` is a
bisimulation. Establishing this for a concrete `R` is exactly where Component D is
consumed — `diagBisim` for `refl`, a swap for `symm`, and `bisim_comp` (⊇, needing
`hinf`) for `trans` — so the up-to principle inherits weak-pullback preservation,
as the design requires. The soundness theorem itself is then immediate. -/
def BisimUpToEquiv (U : Coalg κ) (R : U.X → U.X → Prop) : Prop :=
  Nonempty (Bisim U (EqvClosure R))

/-- **Soundness of coinduction up to equivalence.** If the equivalence closure of
`R` is a bisimulation, then `R`-related states are equal (`R ⊆ EqvClosure R ⊆ Δ`
by `ws2_bisim_eq`). This is the usable up-to proof principle WS3/WS5 consume. -/
theorem ws2_coinduction_upto (R : (νPk κ).X → (νPk κ).X → Prop)
    (hR : BisimUpToEquiv (νPk κ) R) {x y} (hxy : R x y) : x = y := by
  obtain ⟨hB⟩ := hR
  exact ws2_bisim_eq _ hB x y (EqvClosure.rel hxy)

/-! ## The assembled deliverable -/

/-- The WS2 characterization of `νP_κ` (Framings 1+3+4+2+5 assembled). -/
structure WS2Characterization (κ : Cardinal.{u}) where
  carrier        : Coalg κ
  terminal       : IsTerminalCoalg carrier
  nondegenerate  : ∃ a b : carrier.X, a ≠ b
  bisim_eq       : ∀ R : carrier.X → carrier.X → Prop, Bisim carrier R → ∀ x y, R x y → x = y
  weak_pullback  : PkPreservesWeakPullback κ
  behavioural    : ∀ x y : carrier.X, (∃ R, Nonempty (Bisim carrier R) ∧ R x y) ↔ x = y
  coinduction    : ∀ R : carrier.X → carrier.X → Prop, Bisim carrier R → ∀ x y, R x y → x = y

/-- **The WS2 deliverable.** For every infinite regular `κ`, `νP_κ` is a
non-degenerate terminal coalgebra on which bisimulation is identity, `P_κ`
preserves weak pullbacks, and behavioural equivalence coincides with identity.
`hinf` is consumed for non-degeneracy; `_hreg` is unused (see the header note). -/
theorem ws2_characterization (hinf : ℵ₀ ≤ κ) (_hreg : κ.IsRegular) :
    Nonempty (WS2Characterization κ) :=
  ⟨{ carrier := νPk κ
   , terminal := νPk_terminal κ
   , nondegenerate := ws2_nondegenerate hinf
   , bisim_eq := fun R hR => ws2_bisim_eq R hR
   , weak_pullback := ws2_weak_pullback
   , behavioural := ws2_bisim_behavioural
   , coinduction := fun R hR => ws2_bisim_eq R hR }⟩

end Series3.WS2
