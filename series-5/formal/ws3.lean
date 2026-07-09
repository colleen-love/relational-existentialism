/-
`series-5/formal/ws3.lean`

WS3 — **Boundlessness without a wall.** Series 5.

Owns: no object in `W_∞` relates to everything, with the bound *endogenous* — each
object's `< κ_α` relating is the grain of its level, and no level is last, so no global
cap is imposed. Carries the coincidence duty that on any single level the bound is still
the imposed cardinal wall.

The load-bearing new machinery here: bisimulation-is-identity / Lambek for the **labelled**
carrier `νLk` (Series 4 never needed it), giving the carrier lower bound
`nuLk_card_ge : κ ≤ #(νLk κ Q)` (for `Nonempty Q`); and per-level injectivity of the
colimit legs `toColim`. The escaping object in `ws3_no_top` lives at a *higher level* `β`
that exists precisely because no level is last — so no-last-level is load-bearing (it
survives the WS7 strip test).

Design doc: `series-5/spec/ws03-design.md` (candidate B2). Deliverables: `RelatesInf`
(from WS1), `reindex_preserves_count`, `ws4_no_top_cardinal_at`, `ws3_no_global_cap` (B1),
`ws3_no_top` (B2), `ws3_bound_is_grain` (B3), `ws3_wall_vs_grain` (coincidence),
`ws3_faces_cannot_bound` (B4, inherited impossibility).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws2

universe u

open Cardinal QPF Functor Series5.WS1 Series5.WS2

namespace Series5.WS3

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## Terminality and Lambek for the labelled carrier `νLk` -/

@[simp] lemma LkMap_id {X : Type u} (s : LkObj κ Q X) : LkMap (id : X → X) s = s := by
  show PkMap κ (Prod.map id id) s = s
  rw [Prod.map_id]; exact PkMap_id s

lemma LkMap_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) (s : LkObj κ Q X) :
    LkMap (g ∘ f) s = LkMap g (LkMap f s) := by
  show PkMap κ (Prod.map (id : Q → Q) (g ∘ f)) s
     = PkMap κ (Prod.map (id : Q → Q) g) (PkMap κ (Prod.map (id : Q → Q) f) s)
  have hfun : Prod.map (id : Q → Q) (g ∘ f)
      = (Prod.map (id : Q → Q) g) ∘ (Prod.map (id : Q → Q) f) := by funext p; rfl
  rw [hfun, PkMap_comp]

/-- A labelled `P_κ(Q × ·)`-coalgebra. -/
structure LkCoalg (κ : Cardinal.{u}) (Q : Type u) where
  X : Type u
  str : X → LkObj κ Q X

/-- Terminality of a labelled coalgebra. -/
def IsTerminalLkCoalg (U : LkCoalg κ Q) : Prop :=
  ∀ C : LkCoalg κ Q, ∃! h : C.X → U.X, ∀ x, U.str (h x) = LkMap h (C.str x)

lemma hom_uniqueLk {U : LkCoalg κ Q} (hU : IsTerminalLkCoalg U) (C : LkCoalg κ Q)
    {h₁ h₂ : C.X → U.X}
    (n₁ : ∀ x, U.str (h₁ x) = LkMap h₁ (C.str x))
    (n₂ : ∀ x, U.str (h₂ x) = LkMap h₂ (C.str x)) : h₁ = h₂ :=
  (hU C).unique n₁ n₂

lemma endo_eq_idLk {U : LkCoalg κ Q} (hU : IsTerminalLkCoalg U) (h : U.X → U.X)
    (hh : ∀ x, U.str (h x) = LkMap h (U.str x)) : h = id :=
  hom_uniqueLk hU U hh (fun x => by simp)

/-- Lambek's lemma for the labelled carrier: the structure map is a bijection. -/
theorem lambekLk {U : LkCoalg κ Q} (hU : IsTerminalLkCoalg U) : Function.Bijective U.str := by
  obtain ⟨g, hg, -⟩ := hU ⟨LkObj κ Q U.X, LkMap U.str⟩
  have hgU : (fun x => g (U.str x)) = id := by
    apply endo_eq_idLk hU
    intro x
    calc U.str ((fun x => g (U.str x)) x)
        = U.str (g (U.str x)) := rfl
      _ = LkMap g (LkMap U.str (U.str x)) := hg (U.str x)
      _ = LkMap (fun x => g (U.str x)) (U.str x) := (LkMap_comp g U.str (U.str x)).symm
  have left : Function.LeftInverse g U.str := fun x => congrFun hgU x
  have right : Function.RightInverse g U.str := by
    intro y
    calc U.str (g y)
        = LkMap g (LkMap U.str y) := hg y
      _ = LkMap (fun x => g (U.str x)) y := (LkMap_comp g U.str y).symm
      _ = LkMap id y := by rw [hgU]
      _ = y := LkMap_id y
  exact ⟨left.injective, right.surjective⟩

/-- The `νLk` coalgebra. -/
noncomputable def nuLkCoalg (κ : Cardinal.{u}) (Q : Type u) : LkCoalg κ Q := ⟨νLk κ Q, lstr⟩

/-- **`νLk` is terminal** (mirrors the plain `νPk_terminal`, for the labelled QPF). -/
theorem nuLk_terminal (κ : Cardinal.{u}) (Q : Type u) : IsTerminalLkCoalg (nuLkCoalg κ Q) := by
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
        = LkMap h (C.str y) := hh y
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

/-- Lambek for `νLk`: `lstr` is a bijection. -/
theorem lstr_bij (κ : Cardinal.{u}) (Q : Type u) :
    Function.Bijective (lstr : νLk κ Q → LkObj κ Q (νLk κ Q)) :=
  lambekLk (nuLk_terminal κ Q)

/-- **Carrier lower bound for the labelled carrier.** `κ ≤ #(νLk κ Q)` when `Q` is
nonempty: either `κ ≤ #Q` (and the distinct loops give the bound) or `#Q < κ` and Lambek
+ Cantor force `#νLk = 2^#(Q×νLk) > #νLk`, a contradiction. This is the labelled analogue
of `carrier_card_ge`, needed so that a higher level over-populates `W_∞`. -/
theorem nuLk_card_ge (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) (Q : Type u) (hQ : Nonempty Q) :
    κ ≤ Cardinal.mk (νLk κ Q) := by
  have hloop_inj : Function.Injective (fun q : Q => loopState q hinf) := by
    intro q1 q2 h; by_contra hne; exact ws3_loopface_ne hinf hne h
  have hQle : Cardinal.mk Q ≤ Cardinal.mk (νLk κ Q) := Cardinal.mk_le_of_injective hloop_inj
  by_cases hcase : κ ≤ Cardinal.mk Q
  · exact le_trans hcase hQle
  · push_neg at hcase
    by_contra hlt
    push_neg at hlt
    have hmuleq : Cardinal.mk (Q × νLk κ Q) = Cardinal.mk Q * Cardinal.mk (νLk κ Q) := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    have hprod : Cardinal.mk (Q × νLk κ Q) < κ := by
      rw [hmuleq]; exact Cardinal.mul_lt_of_lt hinf hcase hlt
    have hall : ∀ s : Set (Q × νLk κ Q), Cardinal.mk (↥s) < κ :=
      fun s => lt_of_le_of_lt (Cardinal.mk_subtype_le _) hprod
    have e1 : LkObj κ Q (νLk κ Q) ≃ Set (Q × νLk κ Q) := Equiv.subtypeUnivEquiv hall
    have hc : Cardinal.mk (νLk κ Q) = 2 ^ Cardinal.mk (Q × νLk κ Q) :=
      calc Cardinal.mk (νLk κ Q)
          = Cardinal.mk (LkObj κ Q (νLk κ Q)) := Cardinal.mk_congr (Equiv.ofBijective _ (lstr_bij κ Q))
        _ = Cardinal.mk (Set (Q × νLk κ Q)) := Cardinal.mk_congr e1
        _ = 2 ^ Cardinal.mk (Q × νLk κ Q) := Cardinal.mk_set
    have hge : Cardinal.mk (νLk κ Q) ≤ Cardinal.mk (Q × νLk κ Q) := by
      rw [hmuleq]
      obtain ⟨q0⟩ := hQ
      calc Cardinal.mk (νLk κ Q) = 1 * Cardinal.mk (νLk κ Q) := (one_mul _).symm
        _ ≤ Cardinal.mk Q * Cardinal.mk (νLk κ Q) :=
            mul_le_mul_right' (Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr ⟨q0⟩)) _
    have hcantor := Cardinal.cantor (Cardinal.mk (Q × νLk κ Q))
    rw [← hc] at hcantor
    exact absurd (lt_of_le_of_lt hge hcantor) (lt_irrefl _)

/-! ## Colimit-leg injectivity -/

/-- **The colimit legs are injective on each level.** Two level-`a` states with equal
colimit image are equal — because the connecting maps are injective (`ι_inj`). -/
theorem toColim_level_inj (T : Tower Q) (a : T.Idx) :
    Function.Injective (fun x : (T.lvl a).carrier => toColim T x) := by
  intro x y h
  have hrel : TowerColimRel T ⟨a, x⟩ ⟨a, y⟩ :=
    (Equivalence.eqvGen_iff (ws1_colim_equiv T)).mp (Quot.eqvGen_exact h)
  obtain ⟨c, h1, _, heq⟩ := hrel
  exact T.ι_inj h1 heq

/-- **Reindexing up the tower preserves the successor count.** The connecting maps relax
the bound but do not add edges (they are injective), so the count is unchanged — the WS1
fact behind the coincidence. -/
theorem reindex_preserves_count (T : Tower Q) {a b : T.Idx} (h : T.le a b) (x : (T.lvl a).carrier) :
    Cardinal.mk ↥(lstr (T.ι h x)).1 = Cardinal.mk ↥(lstr x).1 := by
  have hset : (lstr (T.ι h x)).1 = (Prod.map id (T.ι h)) '' (lstr x).1 := by
    rw [T.ι_dest h x]; simp only [LkRelax, PkRelax_val, LkMap, PkMap_val]
  rw [hset]
  exact Cardinal.mk_image_eq (Function.injective_id.prodMap (T.ι_inj h))

/-! ## The single-level no-top wall (the fiat half of the coincidence) -/

/-- **The single-level no-top wall.** On any one level `νLk κ_a Q`, no state relates to
every labelled successor — the imposed cardinal wall `#succ < κ_a ≤ #carrier`
(`nuLk_card_ge` at `κ_a`). This is the fiat wall the tower is earned against. -/
theorem ws4_no_top_cardinal_at (T : Tower Q) (hQ : Nonempty Q) (a : T.Idx)
    (x : (T.lvl a).carrier) : ¬ ∀ y, y ∈ (lstr x).1 := by
  intro hall
  have huniv : (Set.univ : Set (Q × (T.lvl a).carrier)) ⊆ (lstr x).1 := fun y _ => hall y
  have hle : Cardinal.mk (Q × (T.lvl a).carrier) ≤ Cardinal.mk ↥(lstr x).1 := by
    have h := Cardinal.mk_le_mk_of_subset huniv; rwa [Cardinal.mk_univ] at h
  have hb : Cardinal.mk ↥(lstr x).1 < (T.lvl a).card := (lstr x).2
  have hge : (T.lvl a).card ≤ Cardinal.mk (Q × (T.lvl a).carrier) := by
    obtain ⟨q0⟩ := hQ
    calc (T.lvl a).card
        ≤ Cardinal.mk (T.lvl a).carrier := nuLk_card_ge _ (T.lvl a).hinf Q ⟨q0⟩
      _ ≤ Cardinal.mk (Q × (T.lvl a).carrier) :=
          Cardinal.mk_le_of_injective (f := fun z => (q0, z)) (fun _ _ h => (Prod.ext_iff.mp h).2)
  exact absurd (lt_of_le_of_lt (le_trans hge hle) hb) (lt_irrefl _)

/-! ## B1 — No global cardinal bounds the tower -/

/-- **B1 — no global cap.** For every candidate cap some level's carrier already exceeds
it. An index/cardinal fact (WS2's unbounded cardinals), kept as a feeding lemma. -/
theorem ws3_no_global_cap (T : Tower Q) (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :
    ∀ c : Cardinal.{u}, ∃ (a : T.Idx), c < (T.lvl a).card := hunb

/-! ## B2 — No object of `W_∞` relates to everything (the headline) -/

/-- **B2 — no object relates to everything.** Given a representative of `x` at level `α`
with `< κ_α` successors, the objects `x` relates to form a set of cardinality `< κ_α`.
But no level is last (`hunb`), so there is a level `β` with `κ_β > κ_α`, whose carrier
injects into `W_∞` with `≥ κ_β` elements. Hence `W_∞` has an object `x` does not relate
to. **No-last-level is load-bearing**: the escaping object lives at level `β`, which
exists only because the index has no greatest element (delete it and B2 falls to the
single-carrier cardinal wall). -/
theorem ws3_no_top (T : Tower Q) (hQ : Nonempty Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (x : Winf T) :
    ¬ ∀ y : Winf T, RelatesInf T x y := by
  intro hall
  obtain ⟨α, y, hxrep, hyb⟩ := ws1_local_bound T x
  obtain ⟨β, hβ⟩ := hunb (T.lvl α).card
  -- If `x` relates to every object, each level-β object `w` satisfies `toColim w = toColim z`
  -- for some `(q,z) ∈ lstr y`. Choice gives an injection `carrier β ↪ (lstr y).1` — both
  -- `Type u`, so the whole contradiction stays in `Cardinal.{u}` (no cross-universe lift).
  have hg : ∀ w : (T.lvl β).carrier,
      ∃ p : ↥(lstr y).1, toColim T p.1.2 = toColim T w := by
    intro w
    obtain ⟨q, hqw⟩ := hall (toColim T w)
    rw [hxrep, succSet_toColim] at hqw
    obtain ⟨p, hp, hpe⟩ := hqw
    exact ⟨⟨p, hp⟩, congrArg Prod.snd hpe⟩
  choose g hgspec using hg
  have hginj : Function.Injective g := by
    intro w w' hww
    have h : toColim T w = toColim T w' := by rw [← hgspec w, ← hgspec w', hww]
    exact toColim_level_inj T β h
  -- κ_β ≤ #(carrier β) ≤ #(lstr y).1 < κ_α < κ_β — a contradiction in `Cardinal.{u}`.
  have hle : Cardinal.mk (T.lvl β).carrier ≤ Cardinal.mk ↥(lstr y).1 :=
    Cardinal.mk_le_of_injective hginj
  have hκβ : (T.lvl β).card ≤ Cardinal.mk (T.lvl β).carrier :=
    nuLk_card_ge _ (T.lvl β).hinf Q hQ
  exact absurd (lt_trans hβ (lt_of_le_of_lt (le_trans hκβ hle) hyb)) (lt_irrefl _)

/-! ## B3 — The bound is the grain (interpretive corollary) -/

/-- **B3 — the bound is the grain.** Each object is bounded by its own level's cardinal
(`ws1_local_bound`) and the tower is bounded by no cardinal (`hunb`): the bound is
level-local, the world's size does not enter. (Simplified from the design's
`IsGlobalCapOf` plumbing to the conjunction it packages.) -/
theorem ws3_bound_is_grain (T : Tower Q) (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card)
    (x : Winf T) :
    (∃ (a : T.Idx) (y : (T.lvl a).carrier), x = toColim T y ∧
        Cardinal.mk ↥(lstr y).1 < (T.lvl a).card)
  ∧ (∀ c : Cardinal.{u}, ∃ (a : T.Idx), c < (T.lvl a).card) :=
  ⟨ws1_local_bound T x, hunb⟩

/-! ## The coincidence: single-level fiat wall vs tower grain -/

/-- **The coincidence theorem.** Boundlessness-without-a-wall is bought *exactly* by
stratifying: on any single level the no-top fact is the imposed cardinal wall
(`ws4_no_top_cardinal_at`), while on the colimit no object relates to everything *because
no level is last* (`ws3_no_top`), with no single κ imposed. The exact analogue of Series
4's `ws3_same_succ_diff_face`. -/
theorem ws3_wall_vs_grain (T : Tower Q) (hQ : Nonempty Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (a : T.Idx) :
    (∀ x : (T.lvl a).carrier, ¬ ∀ y, y ∈ (lstr x).1)
  ∧ (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y) :=
  ⟨fun x => ws4_no_top_cardinal_at T hQ a x, fun x => ws3_no_top T hQ hunb x⟩

/-! ## Settling the colimit gate: the bound-relaxing connecting maps EXIST (charter §9)

`ws1_bisim_eq_colim` proves the gate for an *abstract* `Tower`, whose connecting-map fields
(`ι_dest`, `ι_inj`, `ι_refl`, `ι_trans`) are assumed; `constTower` only witnesses them with
`ι = id` (degenerate — all levels at one cardinal). The charter (§9) flags the *existence* of
genuine connecting maps — **bound-relaxing injective coalgebra morphisms between
different-cardinal `νLk` carriers** — as "the most likely single point of failure." Here we
**construct** them (`boundRelax`, via terminality of the larger carrier) and assemble a genuine
non-degenerate tower (`growingTower`, strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < ⋯`), so the
gate is settled with a real witness rather than assumed fields. -/

/-- `LkMap` and `LkRelax` commute (they act on disjoint coordinates: targets vs. the bound). -/
theorem LkMap_LkRelax_comm {X Y : Type u} {κ₁ κ₂ : Cardinal.{u}} (f : X → Y) (hle : κ₁ ≤ κ₂)
    (t : LkObj κ₁ Q X) : LkMap f (LkRelax hle t) = LkRelax hle (LkMap f t) := by
  apply Subtype.ext; rfl

/-- View `νLk κ₁ Q` as a `κ₂`-level coalgebra by relaxing the bound (`κ₁ ≤ κ₂`). -/
noncomputable def boundRelaxCoalg {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) : LkCoalg κ₂ Q :=
  ⟨νLk κ₁ Q, fun x => LkRelax hle (lstr x)⟩

/-- **The bound-relaxing connecting map** `νLk κ₁ Q → νLk κ₂ Q` (`κ₁ ≤ κ₂`): the unique
coalgebra morphism into the terminal `κ₂`-carrier. This is C2's "reindex a `< κ₁`-successor
set as a `< κ₂` one," constructed. -/
noncomputable def boundRelax {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) : νLk κ₁ Q → νLk κ₂ Q :=
  (nuLk_terminal κ₂ Q (boundRelaxCoalg hle)).choose

theorem boundRelax_spec {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (x : νLk κ₁ Q) :
    lstr (boundRelax hle x) = LkMap (boundRelax hle) (LkRelax hle (lstr x)) :=
  (nuLk_terminal κ₂ Q (boundRelaxCoalg hle)).choose_spec.1 x

/-- `boundRelax` is a coalgebra morphism in the `ι_dest` form (bound relaxation carried). -/
theorem boundRelax_dest {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (x : νLk κ₁ Q) :
    lstr (boundRelax hle x) = LkRelax hle (LkMap (boundRelax hle) (lstr x)) := by
  rw [boundRelax_spec, LkMap_LkRelax_comm]

/-- The successor set of `boundRelax hle x` is the `boundRelax`-image of `x`'s. -/
theorem boundRelax_dest_val {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) (x : νLk κ₁ Q) :
    (lstr (boundRelax hle x)).1 = (Prod.map id (boundRelax hle)) '' (lstr x).1 := by
  rw [boundRelax_dest]; rfl

/-- **`boundRelax` is injective** — the load-bearing gate fact. The relation
`R a b := boundRelax a = boundRelax b` is a `νLk`-bisimulation: `boundRelax` factors as
`ψ ∘ Quot.mk R` for an injective `ψ`, so `R`-related states have equal one-step unfoldings
after quotienting, hence are equal by `nuLk_bisim_eq`. -/
theorem boundRelax_injective {κ₁ κ₂ : Cardinal.{u}} (hle : κ₁ ≤ κ₂) :
    Function.Injective (boundRelax (Q := Q) hle) := by
  intro x y hxy
  refine nuLk_bisim_eq (fun a b => boundRelax hle a = boundRelax hle b) ?_ x y hxy
  intro a b hab
  -- ψ : Quot R → νLk κ₂ Q, injective, with ψ ∘ Quot.mk R = boundRelax hle
  let ψ : Quot (fun a b => boundRelax hle a = boundRelax hle b) → νLk κ₂ Q :=
    Quot.lift (boundRelax hle) (fun _ _ h => h)
  have hψ : Function.Injective ψ := by
    intro p q hpq
    obtain ⟨c, rfl⟩ := Quot.exists_rep p
    obtain ⟨d, rfl⟩ := Quot.exists_rep q
    exact Quot.sound hpq
  have hfact : Prod.map (id : Q → Q) (boundRelax hle)
      = (Prod.map (id : Q → Q) ψ)
        ∘ (Prod.map (id : Q → Q) (Quot.mk (fun a b => boundRelax hle a = boundRelax hle b))) := by
    funext p; obtain ⟨q, z⟩ := p; rfl
  have himg : (Prod.map (id : Q → Q) (boundRelax hle)) '' (lstr a).1
      = (Prod.map (id : Q → Q) (boundRelax hle)) '' (lstr b).1 := by
    rw [← boundRelax_dest_val, ← boundRelax_dest_val, hab]
  rw [hfact, Set.image_comp, Set.image_comp] at himg
  apply Subtype.ext
  show (Prod.map (id : Q → Q) (Quot.mk (fun a b => boundRelax hle a = boundRelax hle b))) '' (lstr a).1
     = (Prod.map (id : Q → Q) (Quot.mk (fun a b => boundRelax hle a = boundRelax hle b))) '' (lstr b).1
  exact Set.image_injective.mpr ((@Function.injective_id Q).prodMap hψ) himg

/-- `boundRelax` of a bound `κ ≤ κ` is the identity (terminal-morphism uniqueness). -/
theorem boundRelax_refl {κ : Cardinal.{u}} (hle : κ ≤ κ) (x : νLk κ Q) :
    boundRelax hle x = x := by
  have hid : boundRelax hle = id :=
    hom_uniqueLk (nuLk_terminal κ Q) (boundRelaxCoalg hle)
      (fun y => boundRelax_spec hle y)
      (fun y => by simp only [id_eq]; rw [LkMap_id]; apply Subtype.ext; rfl)
  rw [hid]; rfl

/-- `boundRelax` composes (terminal-morphism uniqueness): the connecting maps are functorial. -/
theorem boundRelax_trans {κ₁ κ₂ κ₃ : Cardinal.{u}} (hab : κ₁ ≤ κ₂) (hbc : κ₂ ≤ κ₃)
    (hac : κ₁ ≤ κ₃) (x : νLk κ₁ Q) :
    boundRelax hbc (boundRelax hab x) = boundRelax hac x := by
  have hcomp : (boundRelax hbc ∘ boundRelax hab) = boundRelax hac :=
    hom_uniqueLk (nuLk_terminal κ₃ Q) (boundRelaxCoalg hac)
      (fun y => by
        show lstr (boundRelax hbc (boundRelax hab y))
           = LkMap (boundRelax hbc ∘ boundRelax hab) (LkRelax hac (lstr y))
        rw [boundRelax_spec hbc, boundRelax_spec hab, LkMap_comp]
        congr 1)
      (fun y => boundRelax_spec hac y)
  exact congrFun hcomp x

/-! ### A genuine non-degenerate tower with strictly increasing cardinals -/

/-- Strictly increasing cardinals `ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ⋯`. -/
noncomputable def growCard : ℕ → Cardinal.{u}
  | 0 => Cardinal.aleph0
  | (n + 1) => 2 ^ growCard n

theorem growCard_hinf : ∀ n, Cardinal.aleph0 ≤ growCard n
  | 0 => le_refl _
  | (n + 1) => le_trans (growCard_hinf n) (le_of_lt (Cardinal.cantor _))

theorem growCard_lt_succ (n : ℕ) : growCard n < growCard (n + 1) := Cardinal.cantor _

theorem growCard_mono : Monotone growCard :=
  monotone_nat_of_le_succ (fun n => le_of_lt (growCard_lt_succ n))

/-- **A genuine doubly-connected tower.** Levels `ℕ` at strictly increasing cardinals
`growCard`, connected by the constructed bound-relaxing injective coalgebra morphisms
`boundRelax`. Its cardinals are *not* cofinal in `Cardinal.{u}` (an `ℕ`-index walls, §4.1) —
that is the separate index question — but the **connecting maps are genuine, non-identity,
injective coalgebra morphisms**, so the colimit gate holds of a real, non-degenerate object. -/
noncomputable def growingTower (Q : Type u) : Tower Q where
  Idx := ULift.{u} ℕ
  le := fun a b => a.down ≤ b.down
  le_refl := fun a => le_refl a.down
  le_trans := fun h1 h2 => le_trans h1 h2
  directed := fun a b => ⟨⟨max a.down b.down⟩, le_max_left _ _, le_max_right _ _⟩
  lvl := fun n => ⟨growCard n.down, growCard_hinf n.down⟩
  mono := fun h => growCard_mono h
  ι := fun h x => boundRelax (growCard_mono h) x
  ι_dest := fun h x => boundRelax_dest (growCard_mono h) x
  ι_refl := fun x => boundRelax_refl _ x
  ι_trans := fun _ _ x => boundRelax_trans _ _ _ x
  ι_inj := fun _ => boundRelax_injective _

/-- **The colimit gate is settled (charter §9).** A genuine non-degenerate tower exists: its
levels have strictly increasing cardinals and its connecting maps are constructed injective
coalgebra morphisms (not the degenerate `id` of `constTower`). So `ws1_bisim_eq_colim`'s
hypotheses are non-vacuously satisfiable, and the colimit carries the coalgebra structure with
bisimulation-is-identity for a real object — the program's "most likely single point of
failure" discharged, independent of the (separate) proper-class-index question. -/
theorem ws1_gate_settled (Q : Type u) :
    ∃ (T : Tower.{u, u} Q) (a b : T.Idx) (h : T.le a b),
      (T.lvl a).card < (T.lvl b).card ∧ Function.Injective (T.ι h) := by
  refine ⟨growingTower Q, ⟨0⟩, ⟨1⟩, (by norm_num : (0 : ℕ) ≤ 1), ?_, ?_⟩
  · exact growCard_lt_succ 0
  · exact boundRelax_injective _

/-! ### The doubly-unbounded tower: a proper-class (universe-bumped) index (charter §9)

`growingTower` settles the *gate* (genuine injective connecting maps) but its `ℕ` index is
`u`-small, so its cardinals are not cofinal in `Cardinal.{u}` (`ws7_setindexed_walls`): it is
not doubly-unbounded. The pre-registered fix (C2 / charter §9) is a **proper-class index**,
realized here as the universe-bumped `Cardinal.{u} × ℤ : Type (u+1)` under the lexicographic
order — the `Cardinal` coordinate gives no greatest element and cofinal cardinals, the `ℤ`
coordinate gives no least element. Transported onto the same `boundRelax` connecting maps, it
is a genuine `Tower.{u, u+1}` that **does** satisfy `DoubleUnboundedness`, so the flagship
payoffs hold of a real object with no open antecedent. -/

/-- Lexicographic order on the proper-class index `Cardinal.{u} × ℤ`: compare the cardinal
first, then the `ℤ` descent coordinate. -/
noncomputable def cardIdxLe : (Cardinal.{u} × ℤ) → (Cardinal.{u} × ℤ) → Prop :=
  fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- The level cardinal of index `(c, n)`: `max ℵ₀ c` (always `≥ ℵ₀`, so a legal `Level`). -/
noncomputable def cardIdxCard (a : Cardinal.{u} × ℤ) : Cardinal.{u} := max Cardinal.aleph0 a.1

theorem cardIdxLe_refl (a : Cardinal.{u} × ℤ) : cardIdxLe a a := Or.inr ⟨rfl, le_refl _⟩

theorem cardIdxLe_trans {a b c : Cardinal.{u} × ℤ} (hab : cardIdxLe a b) (hbc : cardIdxLe b c) :
    cardIdxLe a c := by
  rcases hab with h1 | ⟨h1, h1'⟩
  · rcases hbc with h2 | ⟨h2, _⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (h2 ▸ h1)
  · rcases hbc with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, le_trans h1' h2'⟩

theorem cardIdx_mono {a b : Cardinal.{u} × ℤ} (h : cardIdxLe a b) :
    cardIdxCard a ≤ cardIdxCard b := by
  have h1 : a.1 ≤ b.1 := by rcases h with h | ⟨h, _⟩; exacts [le_of_lt h, le_of_eq h]
  exact max_le_max (le_refl _) h1

/-- **The doubly-unbounded tower.** Proper-class index `Cardinal.{u} × ℤ`, levels at cardinal
`max ℵ₀ c`, connected by the constructed bound-relaxing injective coalgebra morphisms
`boundRelax`. Non-degenerate exactly as `growingTower`, but now with an index that has no
greatest element *and* cofinal cardinals (via `Cardinal`) and no least element (via `ℤ`). -/
noncomputable def cardinalTower (Q : Type u) : Tower.{u, u+1} Q where
  Idx := Cardinal.{u} × ℤ
  le := cardIdxLe
  le_refl := cardIdxLe_refl
  le_trans := cardIdxLe_trans
  directed := fun a b => ⟨(max a.1 b.1, max a.2 b.2), by
      rcases lt_or_eq_of_le (le_max_left a.1 b.1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, le_max_left a.2 b.2⟩, by
      rcases lt_or_eq_of_le (le_max_right a.1 b.1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, le_max_right a.2 b.2⟩⟩
  lvl := fun a => ⟨cardIdxCard a, le_max_left _ _⟩
  mono := fun h => cardIdx_mono h
  ι := fun h x => boundRelax (cardIdx_mono h) x
  ι_dest := fun h x => boundRelax_dest (cardIdx_mono h) x
  ι_refl := fun x => boundRelax_refl _ x
  ι_trans := fun _ _ x => boundRelax_trans _ _ _ x
  ι_inj := fun _ => boundRelax_injective _

/-! ## B4 — the inherited impossibility: faces cannot bound branching -/

/-- **B4 (inherited impossibility).** Faces cannot supply the bound: the carrier is still
`≥ κ` (`carrier_card_ge`), so a face-counting wall is unavailable *at each level*, hence
on the colimit. Series 5 does not solve Series 4's face-bounding problem; it **dissolves**
it by relocating the bound between levels (B2). -/
theorem ws3_faces_cannot_bound (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X :=
  carrier_card_ge κ

end Series5.WS3
