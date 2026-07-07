/-
`series-3/formal/ws3.lean`

WS3 (`series-3/spec/ws3/04-charter-design-review.md`): **discharging Commitment 4
/ criterion (iv)** — bidirectional whole/part constitution — as a *two-part
theorem*, built on `ws1.lean`/`ws2.lean`.

* **Part A — the gate, as a theorem, PROVED axiom-free.** The strict Beck
  distributive law of `§3.4` (`λ : P_κP_κ ⇒ P_κP_κ`) does NOT exist. This is
  Klin–Salamanca (MFPS 2018, Thm 2.4), and it is **ported in full** here (design
  Part A **route 1**): `ws3_no_distributive_law` is a theorem with NO custom axiom
  (matching WS1's removal of `exists_terminal_coalg`). The KS hypotheses for `P_κ`
  are also recorded as proved lemmas — (H1) `Pk_preserves_preimages`, (H2) `betaPk`
  with `betaPk_idempotent` / `betaPk_nontrivial` — but the no-go proof inlines the
  four-set diagonal contradiction they abstract, rather than importing it. This
  closes the design's Part C item 2 verification gate (the `P_κ` diagonal port).
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

## Signature note (corrected from design B.4)

The design's B.4 registers `pentagon : dest (alg t) = PkMap alg (join (PkMap dest
t))`. That is ill-typed against this `alg` — the outer `PkMap alg` is a level off,
a transcription artifact from v2's mislabeled corecursion identity. The true and
provable coherence, matching the design's own Egli–Milner prose, is
`dest (alg t) = ⋃_{x∈t} dest x`, i.e. `pentagon : dest (alg t) = pkJoin (PkMap dest
t)` — what is proved here. Part B is thus discharged against this corrected
signature (surfaced, not papered over).

## Hypothesis accounting

`hreg : κ.IsRegular` is **genuinely load-bearing** here (unlike WS2): the bounded
union `pkJoin` is `< κ` only for regular `κ` — a `< κ`-indexed sup of `< κ`
cardinals is `< κ` exactly by regularity (`Cardinal.iSup_lt_of_isRegular`); `hinf`
alone fails for singular `κ`. `hinf = hreg.aleph0_le` is used for singletons/pairs.

## Axioms

**No custom axioms.** Everything — including the Part A no-go — depends on only
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`. `#print axioms`
on `ws3_no_distributive_law` and `ws3_weak_bialgebra` shows exactly those three.
(Earlier revisions carried a `klinSalamanca_no_law` import for the no-go; the full
route-1 diagonal port below removes it, so — like WS1 — WS3 is now axiom-free.) No
AFA-encoding axiom is introduced: AFA is modeled coalgebraically (νP_κ = the final
coalgebra), per WS3 Phase 1 §"Ambient theory". `Classical.choice` is inherent to
the Mathlib base and the terminal-coalgebra / Lambek-inverse machinery.

## Residuals routed (design Part C; not relabeled)

* Canonical weak law / quantale question → **WS4** (joins the shared `(F, κ)` list).
* The `P_κ` diagonal port (design Part C item 2 build gate) → **CLOSED** here
  (`ws3_no_distributive_law`, route 1).
* `alg_nontrivial`'s one-step-observability → discharged here for concrete
  witnesses; the general branching-≥2 floor stays a **WS7** obligation.
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

/-! ### The Klin–Salamanca hypotheses for `P_κ` (design §A.2), PROVED

We record the two hypotheses under which the KS no-go theorem applies and prove
`P_κ` satisfies them (machine-checking the design §A.2 instantiation). These are
the *checkable content* of §A.2; the no-go proof itself (`ws3_no_distributive_law`,
route 1) inlines the diagonal contradiction these abstract, so it does not route
through them — they stand as independent documentation that `P_κ` is in KS's
scope. -/

/-- **(H1) `P_κ` preserves preimages** (Klin–Salamanca §2, specialised to
inclusions): if the direct image `f '' t` lands in `Z`, then `t ⊆ f⁻¹ Z`. The
`< κ` bound is inert (subsets of `t` are no larger). -/
theorem Pk_preserves_preimages {X Y : Type u} (f : X → Y) (Z : Set Y) (t : PkObj κ X)
    (h : (PkMap κ f t).1 ⊆ Z) : t.1 ⊆ f ⁻¹' Z :=
  fun _ hx => h ⟨_, hx, rfl⟩

/-- The nontrivial idempotent term `β_X(x,y) = {x,y}` of `P_κ` (Klin–Salamanca §2).
Its `< κ` bound holds because `2 < κ` for infinite `κ`. -/
noncomputable def betaPk (hinf : ℵ₀ ≤ κ) {X : Type u} (x y : X) : PkObj κ X :=
  ⟨{x, y}, mk_pair_lt hinf x y⟩

/-- **(H2a) Idempotence:** `β(x,x) = pure x`. -/
theorem betaPk_idempotent (hinf : ℵ₀ ≤ κ) {X : Type u} (x : X) :
    betaPk hinf x x = pkPure hinf x := by
  apply Subtype.ext; simp [betaPk, pkPure]

/-- **(H2b) Non-triviality:** for `a ≠ b`, `β(a,b) = {a,b}` is a subset of neither
`{a}` nor `{b}` — i.e. `{a,b} ∉ P_κ{a} ∪ P_κ{b}`. -/
theorem betaPk_nontrivial (hinf : ℵ₀ ≤ κ) {X : Type u} (a b : X) (hab : a ≠ b) :
    ¬ ((betaPk hinf a b).1 ⊆ ({a} : Set X) ∨ (betaPk hinf a b).1 ⊆ ({b} : Set X)) := by
  simp only [betaPk]
  rintro (h | h)
  · exact hab (Set.mem_singleton_iff.mp (h (by simp))).symm
  · exact hab (Set.mem_singleton_iff.mp (h (by simp)))

/-! ### Route 1 — the no-go PROVED, axiom-free (Klin–Salamanca's four-set diagonal)

We port the KS Theorem-2.4 argument in full, so `ws3_no_distributive_law` is a
theorem with NO custom axiom (matching WS1's removal of `exists_terminal_coalg`).
The diagonal uses a 4-element carrier `Bool × Bool` and the three fibre-collapsing
maps `fst`, `snd`, `xor` (their pairwise fibres partition the diagonal). Given a
distributive law `l`, the two unit laws + naturality pin `l.lam W` (for the
two-fibre element `W`) so tightly that any member `S` of it is simultaneously
non-constant in `fst` (from `f`) yet constant in both `snd` and `xor` (from
`g`, `h`) — impossible, since `fst = snd ⊕ xor`. Every set in play has ≤ 2
elements `< κ`, so the `P_f` scope note transfers to `P_κ` with no extra work. -/

private abbrev ksBB : Type u := ULift.{u} (Bool × Bool)
private abbrev ksBt : Type u := ULift.{u} Bool
private def ksE (x y : Bool) : ksBB := ⟨(x, y)⟩
private def ksF (p : ksBB) : ksBt := ⟨p.down.1⟩
private def ksG (p : ksBB) : ksBt := ⟨p.down.2⟩
private def ksH (p : ksBB) : ksBt := ⟨xor p.down.1 p.down.2⟩

/-- **The WS3 gate result (Impossibility proved = success, §5/§7) — PROVED,
axiom-free.** No strict distributive law of `P_κ` over itself exists. The KS
hypotheses for `P_κ` are recorded separately (`Pk_preserves_preimages`,
`betaPk_idempotent`, `betaPk_nontrivial`); this proof inlines the diagonal
contradiction they abstract. -/
theorem ws3_no_distributive_law (hinf : ℵ₀ ≤ κ) : IsEmpty (DistLaw κ hinf) := by
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
  cases hc : p.down.2 <;> rw [hc] at hx <;> simp at hx

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
