/-
`series-3/formal/ws3.lean`

WS3 (`series-3/spec/ws3/04-charter-design-review.md`): **discharging Commitment 4
/ criterion (iv)** — bidirectional whole/part constitution — as a *two-part
theorem*, built on `ws1.lean`/`ws2.lean`.

* **Part A — the gate, as a theorem.** The strict Beck distributive law of `§3.4`
  (`λ : P_κP_κ ⇒ P_κP_κ`) does NOT exist. This is Klin–Salamanca (MFPS 2018,
  Thm 2.4); `P_κ` meets both hypotheses (preimage-preservation, a nontrivial
  idempotent term `{x,y}`), and every object in their diagonal proof has ≤ 4
  elements `< κ`, so the `P_f` scope note transfers verbatim. We carry it as the
  sanctioned single external import `KlinSalamanca_no_law` (design Part A route 2),
  flagged as the sole non-Mathlib axiom, and derive `ws3_no_distributive_law`.
* **Part B — the content, via the weak law.** The bidirectional constitution
  criterion (iv) names is delivered by the Egli–Milner *weak* distributive law:
  a composition operator `alg : P_κ(νP_κ) → νP_κ` with `dest (alg t) = ⋃_{x∈t}
  dest x`, defined through the Lambek inverse. It satisfies the weak-law
  multiplication coherence (`alg_pentagon`, `alg_join`), the `T`-unit law on
  singletons (`alg_unit_idem`), part-reflection (`reflects_part`, upward
  constitution — `dest` is downward), the `Ω` fixed point (`omega_fix`), and
  non-triviality (`alg_nontrivial`). Assembled as `WeakBialgebra` /
  `ws3_weak_bialgebra`, which carries `noStrictLaw` (Part A) as a field so the
  substitution can never be read as a relabeling.

## Hypothesis accounting

`hreg : κ.IsRegular` is **genuinely load-bearing** here (unlike WS2): the bounded
union `pkJoin` is `< κ` only for regular `κ` — a `< κ`-indexed sup of `< κ`
cardinals is `< κ` exactly by regularity (`Cardinal.iSup_lt_of_isRegular`); `hinf`
alone fails for singular `κ`. `hinf = hreg.aleph0_le` is used for singletons/pairs.

## Axioms

Everything is Mathlib-standard (`propext`/`Classical.choice`/`Quot.sound`) EXCEPT
the one sanctioned import `KlinSalamanca_no_law` (Part A). No AFA-encoding axiom is
introduced — AFA is modeled coalgebraically (νP_κ = the final coalgebra), per WS3
Phase 1 §"Ambient theory". `#print axioms` is expected to show exactly:
`propext`, `Classical.choice`, `Quot.sound`, `KlinSalamanca_no_law`.
-/
import ws2

universe u

open Cardinal Series3.WS1 Series3.WS2

namespace Series3.WS3

variable {κ : Cardinal.{u}}

/-! ## The bounded-union monad structure on `P_κ` -/

/-- The unit of the composition monad: the one-part whole `{x}`. -/
noncomputable def pkPure (hinf : ℵ₀ ≤ κ) {X : Type u} (x : X) : PkObj κ X :=
  ⟨{x}, mk_singleton_lt hinf x⟩

/-- The bounded big-union (`join`/`μ`). The `< κ` bound is where **regularity is
load-bearing**: a `< κ`-indexed sup of `< κ` cardinals is `< κ` only for regular
`κ` (`Cardinal.iSup_lt_of_isRegular`); `hinf` alone fails for singular `κ`. -/
noncomputable def pkJoin (hreg : κ.IsRegular) {X : Type u} (tt : PkObj κ (PkObj κ X)) :
    PkObj κ X :=
  ⟨⋃ w ∈ tt.1, w.1, by
    refine lt_of_le_of_lt (Cardinal.mk_biUnion_le (fun w => w.1) tt.1) ?_
    exact Cardinal.mul_lt_of_lt hreg.aleph0_le tt.2
      (Cardinal.iSup_lt_of_isRegular hreg tt.2 (fun w => w.1.2))⟩

@[simp] lemma pkJoin_val (hreg : κ.IsRegular) {X : Type u} (tt : PkObj κ (PkObj κ X)) :
    (pkJoin hreg tt).1 = ⋃ w ∈ tt.1, w.1 := rfl

lemma mem_pkJoin (hreg : κ.IsRegular) {X : Type u} (tt : PkObj κ (PkObj κ X)) (z : X) :
    z ∈ (pkJoin hreg tt).1 ↔ ∃ w ∈ tt.1, z ∈ w.1 := by
  simp only [pkJoin_val, Set.mem_iUnion, exists_prop]

/-- A two-element set is `< κ` for infinite `κ`. -/
lemma mk_pair_lt (hinf : ℵ₀ ≤ κ) {X : Type u} (a b : X) :
    Cardinal.mk (↥({a, b} : Set X)) < κ := by
  have h2 : Cardinal.mk (↥({a, b} : Set X)) ≤ 2 := by
    calc Cardinal.mk (↥({a, b} : Set X))
          ≤ Cardinal.mk (↥({b} : Set X)) + 1 := Cardinal.mk_insert_le
      _ = 1 + 1 := by rw [Cardinal.mk_singleton]
      _ = 2 := by norm_num
  refine lt_of_le_of_lt h2 (lt_of_lt_of_le ?_ hinf)
  exact_mod_cast Cardinal.nat_lt_aleph0 2

/-! ## The composition algebra `alg` on `νP_κ`, via the Lambek inverse -/

/-- `dest = (νPk κ).str` is a bijection (Lambek), packaged as an equiv. -/
noncomputable def destEquiv (κ : Cardinal.{u}) : (νPk κ).X ≃ PkObj κ (νPk κ).X :=
  Equiv.ofBijective (νPk κ).str (lambek (νPk_terminal κ))

/-- **The composition operator.** `alg t` is the object whose immediate parts are
the Egli–Milner union of the parts' observations: `dest (alg t) = ⋃_{x∈t} dest x`.
Defined directly through the Lambek inverse (equivalently the terminal
corecursion of the weak-law lifted coalgebra). -/
noncomputable def alg (hreg : κ.IsRegular) (t : PkObj κ (νPk κ).X) : (νPk κ).X :=
  (destEquiv κ).symm (pkJoin hreg (PkMap κ (νPk κ).str t))

/-- **The weak-bialgebra coherence square** (the `λ_w` multiplication pentagon,
Egli–Milner form): `dest (alg t) = ⋃_{x∈t} dest x`. -/
theorem alg_pentagon (hreg : κ.IsRegular) (t : PkObj κ (νPk κ).X) :
    (νPk κ).str (alg hreg t) = pkJoin hreg (PkMap κ (νPk κ).str t) := by
  show (destEquiv κ) ((destEquiv κ).symm (pkJoin hreg (PkMap κ (νPk κ).str t))) = _
  exact (destEquiv κ).apply_symm_apply _

lemma pkJoin_map_pure (hreg : κ.IsRegular) (x : (νPk κ).X) :
    pkJoin hreg (PkMap κ (νPk κ).str (pkPure hreg.aleph0_le x)) = (νPk κ).str x := by
  apply Subtype.ext
  simp only [pkJoin_val, PkMap_val, pkPure, Set.image_singleton, Set.biUnion_singleton]

/-- **`T`-unit coherence** `alg ∘ pure = id`. (For the Egli–Milner union this holds
on all singletons, of which every `pure x = {x}` is one.) -/
theorem alg_unit_idem (hreg : κ.IsRegular) (x : (νPk κ).X) :
    alg hreg (pkPure hreg.aleph0_le x) = x := by
  show (destEquiv κ).symm (pkJoin hreg (PkMap κ (νPk κ).str (pkPure hreg.aleph0_le x))) = x
  rw [pkJoin_map_pure hreg x]
  exact (destEquiv κ).symm_apply_apply x

/-- **Part-reflection (upward constitution).** Composition never loses a part's
observable structure. -/
theorem reflects_part (hreg : κ.IsRegular) (t : PkObj κ (νPk κ).X) {x : (νPk κ).X}
    (hx : x ∈ t.1) : ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg hreg t)).1 := by
  rw [alg_pentagon hreg t, pkJoin_val]
  intro z hz
  exact Set.mem_biUnion (Set.mem_image_of_mem _ hx) hz

/-- **`Ω` fixed point.** The groundless inhabitant is fixed by self-composition. -/
theorem omega_fix (hreg : κ.IsRegular) (ω : (νPk κ).X)
    (_hω : ((νPk κ).str ω).1 = {ω}) : alg hreg (pkPure hreg.aleph0_le ω) = ω :=
  alg_unit_idem hreg ω

/-- **Multiplication coherence** `alg ∘ join = alg ∘ P_κ(alg)` — the coherence the
weak distributive law retains. Reduces to associativity of the bounded union. -/
theorem alg_join (hreg : κ.IsRegular) (tt : PkObj κ (PkObj κ (νPk κ).X)) :
    alg hreg (pkJoin hreg tt) = alg hreg (PkMap κ (alg hreg) tt) := by
  apply (lambek (νPk_terminal κ)).injective
  rw [alg_pentagon, alg_pentagon]
  apply Subtype.ext
  apply Set.ext
  intro z
  rw [mem_pkJoin, mem_pkJoin]
  constructor
  · rintro ⟨w, hw, hzw⟩
    rw [PkMap_val, Set.mem_image] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [mem_pkJoin] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    refine ⟨(νPk κ).str (alg hreg s), ?_, ?_⟩
    · rw [PkMap_val, Set.mem_image]
      exact ⟨alg hreg s, by rw [PkMap_val, Set.mem_image]; exact ⟨s, hs, rfl⟩, rfl⟩
    · rw [alg_pentagon, mem_pkJoin]
      exact ⟨(νPk κ).str x, by rw [PkMap_val, Set.mem_image]; exact ⟨x, hxs, rfl⟩, hzw⟩
  · rintro ⟨w, hw, hzw⟩
    rw [PkMap_val, Set.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [PkMap_val, Set.mem_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [alg_pentagon, mem_pkJoin] at hzw
    obtain ⟨w', hw', hzw'⟩ := hzw
    rw [PkMap_val, Set.mem_image] at hw'
    obtain ⟨x, hxs, rfl⟩ := hw'
    refine ⟨(νPk κ).str x, ?_, hzw'⟩
    rw [PkMap_val, Set.mem_image]
    exact ⟨x, by rw [mem_pkJoin]; exact ⟨s, hs, hxs⟩, rfl⟩

/-! ## Part A — the gate as a theorem: no strict distributive law -/

/-- A distributive law of the pointed functor `(P_κ, pure)` over itself: a natural
family `P_κP_κ ⇒ P_κP_κ` satisfying both pointed-functor unit laws. This is the
`§3.4` strict-`λ` instrument, in exactly Klin–Salamanca's setting. -/
structure DistLaw (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) where
  lam : ∀ {X : Type u}, PkObj κ (PkObj κ X) → PkObj κ (PkObj κ X)
  natural : ∀ {X Y : Type u} (f : X → Y) (𝒮 : PkObj κ (PkObj κ X)),
    lam (PkMap κ (PkMap κ f) 𝒮) = PkMap κ (PkMap κ f) (lam 𝒮)
  unit_T : ∀ {X : Type u} (t : PkObj κ X), lam (pkPure hinf t) = PkMap κ (pkPure hinf) t
  unit_F : ∀ {X : Type u} (t : PkObj κ X), lam (PkMap κ (pkPure hinf) t) = pkPure hinf t

/-- **Klin–Salamanca (2018), Theorem 2.4**, instantiated at `T = F = P_κ` — the one
sanctioned external import (design Part A, route 2). `P_κ` preserves preimages and
has the nontrivial idempotent term `β_X(x,y) = {x,y}`, so no distributive law of
`(P_κ, pure)` over itself exists. Every set in their diagonal proof has ≤ 4
elements `< κ`, so the `P_f` scope note transfers verbatim. Flagged as the sole
non-Mathlib axiom on the WS3 critical path. -/
axiom KlinSalamanca_no_law (hinf : ℵ₀ ≤ κ) : IsEmpty (DistLaw κ hinf)

/-- **The WS3 gate result (Impossibility proved = success, §5/§7).** No strict
distributive law of `P_κ` over itself exists. -/
theorem ws3_no_distributive_law (hinf : ℵ₀ ≤ κ) : IsEmpty (DistLaw κ hinf) :=
  KlinSalamanca_no_law hinf

/-! ## Part B.3(C) — non-triviality: incomparable witnesses -/

/-- A two-step coalgebra `true ↦ {false}`, `false ↦ ∅`, used to build an object
whose sole part is an empty object — giving observations incomparable to `Ω`. -/
noncomputable def twoStepCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨ULift.{u} Bool,
   fun b => bif b.down then ⟨{ULift.up false}, mk_singleton_lt hinf _⟩ else ⟨∅, mk_empty_lt hinf⟩⟩

/-- **Non-triviality (the strong form).** There are `a ≠ b` whose composite `{a,b}`
reflects both (`reflects_part`) yet equals neither — witnessed by `Ω` (with
`dest Ω = {Ω}`) and an object `z` whose sole part is an empty object, so their
observations are genuinely incomparable. -/
theorem alg_nontrivial (hreg : κ.IsRegular) :
    ∃ a b : (νPk κ).X, a ≠ b ∧
      (let t : PkObj κ (νPk κ).X := ⟨{a, b}, mk_pair_lt hreg.aleph0_le a b⟩;
        ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
        ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg hreg t)).1 ∧
        alg hreg t ≠ a ∧ alg hreg t ≠ b) := by
  have hinf := hreg.aleph0_le
  obtain ⟨hΩ, hΩnat, -⟩ := νPk_terminal κ (omegaCoalg hinf)
  obtain ⟨h, hnat, -⟩ := νPk_terminal κ (twoStepCoalg hinf)
  set Ω := hΩ PUnit.unit with hΩdef
  set e0 := h (ULift.up false) with he0def
  set z := h (ULift.up true) with hzdef
  -- observations
  have hΩfix : ((νPk κ).str Ω).1 = {Ω} := by
    rw [hΩdef, hΩnat PUnit.unit]; simp [PkMap, omegaCoalg]
  have he0 : ((νPk κ).str e0).1 = (∅ : Set (νPk κ).X) := by
    rw [he0def, hnat (ULift.up false)]; simp [PkMap, twoStepCoalg]
  have hzfix : ((νPk κ).str z).1 = {e0} := by
    rw [hzdef, hnat (ULift.up true)]; simp [PkMap, twoStepCoalg, he0def]
  -- e0 ≠ Ω  (empty vs nonempty observation)
  have hne0Ω : e0 ≠ Ω := by
    intro he; apply (Set.not_mem_empty Ω); rw [← he0, he]; rw [hΩfix]; rfl
  -- Ω ≠ z
  have hab : Ω ≠ z := by
    intro he
    apply hne0Ω
    have : ({e0} : Set (νPk κ).X) = {Ω} := by rw [← hzfix, ← he, hΩfix]
    have hmem : e0 ∈ ({Ω} : Set (νPk κ).X) := by rw [← this]; rfl
    exact hmem
  refine ⟨Ω, z, hab, ?_, ?_, ?_, ?_⟩
  · -- reflects Ω
    exact reflects_part hreg _ (Set.mem_insert Ω {z})
  · -- reflects z
    exact reflects_part hreg _ (Set.mem_insert_of_mem Ω rfl)
  · -- alg t ≠ Ω
    intro he
    -- e0 ∈ dest(alg t) via reflects z, but dest(alg t) = dest Ω = {Ω}
    have he0mem : e0 ∈ ((νPk κ).str (alg hreg ⟨{Ω, z}, mk_pair_lt hinf Ω z⟩)).1 :=
      reflects_part hreg _ (Set.mem_insert_of_mem Ω rfl) (by rw [hzfix]; rfl)
    rw [he, hΩfix] at he0mem
    exact hne0Ω he0mem
  · -- alg t ≠ z
    intro he
    have hΩmem : Ω ∈ ((νPk κ).str (alg hreg ⟨{Ω, z}, mk_pair_lt hinf Ω z⟩)).1 :=
      reflects_part hreg _ (Set.mem_insert Ω {z}) (by rw [hΩfix]; rfl)
    rw [he, hzfix] at hΩmem
    exact hne0Ω (by rw [← Set.mem_singleton_iff.mp hΩmem])

/-! ## The assembled deliverable -/

/-- The WS3 weak bialgebra on `νP_κ` (Part B), carrying the Part A impossibility as
the `noStrictLaw` field so the substitution is transparent. -/
structure WeakBialgebra (κ : Cardinal.{u}) (hreg : κ.IsRegular) where
  alg          : PkObj κ (νPk κ).X → (νPk κ).X
  pentagon     : ∀ t, (νPk κ).str (alg t) = pkJoin hreg (PkMap κ (νPk κ).str t)
  algUnitIdem  : ∀ x, alg (pkPure hreg.aleph0_le x) = x
  algJoin      : ∀ tt, alg (pkJoin hreg tt) = alg (PkMap κ alg tt)
  reflectsPart : ∀ t {x}, x ∈ t.1 → ((νPk κ).str x).1 ⊆ ((νPk κ).str (alg t)).1
  omegaFix     : ∀ ω, ((νPk κ).str ω).1 = {ω} → alg (pkPure hreg.aleph0_le ω) = ω
  nontrivial   : ∃ a b, a ≠ b ∧
                   (let t : PkObj κ (νPk κ).X := ⟨{a, b}, mk_pair_lt hreg.aleph0_le a b⟩;
                     ((νPk κ).str a).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     ((νPk κ).str b).1 ⊆ ((νPk κ).str (alg t)).1 ∧
                     alg t ≠ a ∧ alg t ≠ b)
  noStrictLaw  : IsEmpty (DistLaw κ hreg.aleph0_le)

/-- **The WS3 deliverable.** For every regular `κ`, `νP_κ` carries a weak bialgebra
realizing bidirectional constitution (Commitment 4 / criterion (iv)), and no strict
distributive law of the `§3.4` form exists. -/
theorem ws3_weak_bialgebra (hreg : κ.IsRegular) : Nonempty (WeakBialgebra κ hreg) :=
  ⟨{ alg          := alg hreg
   , pentagon     := alg_pentagon hreg
   , algUnitIdem  := alg_unit_idem hreg
   , algJoin      := alg_join hreg
   , reflectsPart := reflects_part hreg
   , omegaFix     := omega_fix hreg
   , nontrivial   := alg_nontrivial hreg
   , noStrictLaw  := ws3_no_distributive_law hreg.aleph0_le }⟩

end Series3.WS3
