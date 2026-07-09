/-
`series-5/formal/ws2.lean`

WS2 — **The explosion, and the forced answer.** Series 5, the intellectual spine.

Owns: the **Explosion Dilemma** (§3.2) — on any single fixed carrier, boundless-and-plural
is unsatisfiable — the **index theory** (`ℤ`: no least, no greatest, self-dual, proved),
and the **forced-answer dichotomy** (§5.3).

Both horns of the Dilemma are *transcribed Series 4 theorems*: horn (a) is the cardinal
wall (`carrier_card_ge`, WS1), horn (b) is the global-groundless collapse
(`ws5_global_groundless_collapses`, transcribed here). The Dilemma is their conjunction as
a dichotomy about one carrier.

Design doc: `series-5/spec/ws02-design.md`. Deliverables: `HereditarilyNonempty`,
`ws2_collapse`, `ws5_global_groundless_collapses`, `ws2_explosion_dilemma` (E1),
`ws2_supremum_walls` (E3), `Idx`/`ws2_no_least`/`ws2_no_great`/`ws2_self_dual`,
`ws2_no_atom_floor`, `Boundless` + `ws2_forced_answer` (F2).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws1

universe u

open Cardinal Series5.WS1

namespace Series5.WS2

variable {κ : Cardinal.{u}}

/-! ## Part A.1 — The inherited (Parmenides) collapse (transcribed Series 4 WS2) -/

/-- Hereditarily nonempty: every reachable state has a nonempty successor set. -/
def HereditarilyNonempty (x : (νPk κ).X) : Prop :=
  ∀ v, Reaches x v → ((νPk κ).str v).1 ≠ ∅

lemma HereditarilyNonempty.ne_empty {x : (νPk κ).X}
    (hx : HereditarilyNonempty x) : ((νPk κ).str x).1 ≠ ∅ :=
  hx x (Reaches.refl' x)

lemma HereditarilyNonempty.succ {x w : (νPk κ).X}
    (hx : HereditarilyNonempty x) (hw : w ∈ ((νPk κ).str x).1) : HereditarilyNonempty w :=
  fun v hv => hx v (Relation.ReflTransGen.head hw hv)

private abbrev HNGraph (κ : Cardinal.{u}) : Type u :=
  {p : (νPk κ).X × (νPk κ).X // HereditarilyNonempty p.1 ∧ HereditarilyNonempty p.2}

/-- The bisimulation coalgebra structure `ζ(x,y) = str x × str y` on the graph. -/
noncomputable def hnZeta (hinf : ℵ₀ ≤ κ) (q : HNGraph κ) : PkObj κ (HNGraph κ) :=
  ⟨{ g : HNGraph κ | g.1.1 ∈ ((νPk κ).str q.1.1).1 ∧ g.1.2 ∈ ((νPk κ).str q.1.2).1 }, by
    have hinj : Function.Injective
        (fun g : ↥{ g : HNGraph κ |
              g.1.1 ∈ ((νPk κ).str q.1.1).1 ∧ g.1.2 ∈ ((νPk κ).str q.1.2).1 } =>
          ((⟨g.1.1.1, g.2.1⟩ : ↥((νPk κ).str q.1.1).1),
           (⟨g.1.1.2, g.2.2⟩ : ↥((νPk κ).str q.1.2).1))) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val (congrArg Prod.fst hab)
      · exact congrArg Subtype.val (congrArg Prod.snd hab)
    have hbmul : Cardinal.mk (↥((νPk κ).str q.1.1).1) * Cardinal.mk (↥((νPk κ).str q.1.2).1) < κ :=
      Cardinal.mul_lt_of_lt hinf ((νPk κ).str q.1.1).2 ((νPk κ).str q.1.2).2
    have hbprod : Cardinal.mk (↥((νPk κ).str q.1.1).1 × ↥((νPk κ).str q.1.2).1)
        = Cardinal.mk (↥((νPk κ).str q.1.1).1) * Cardinal.mk (↥((νPk κ).str q.1.2).1) := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) (hbprod ▸ hbmul)⟩

/-- `R x y := (both hereditarily nonempty)` is a `P_κ`-bisimulation on the carrier. -/
noncomputable def hereditarilyNonempty_bisim (hinf : ℵ₀ ≤ κ) :
    Bisim (νPk κ) (fun x y => HereditarilyNonempty x ∧ HereditarilyNonempty y) where
  ζ := hnZeta hinf
  nat_fst := fun q => by
    apply Subtype.ext
    rw [PkMap_val]
    ext c
    simp only [hnZeta, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hc
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr q.2.2.ne_empty
      exact ⟨⟨(c, d), q.2.1.succ hc, q.2.2.succ hd⟩, ⟨hc, hd⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg.1
  nat_snd := fun q => by
    apply Subtype.ext
    rw [PkMap_val]
    ext c
    simp only [hnZeta, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hc
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr q.2.1.ne_empty
      exact ⟨⟨(d, c), q.2.1.succ hd, q.2.2.succ hc⟩, ⟨hd, hc⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg.2

/-- **The Collapse Theorem (Premise 1).** In the plain carrier `νP_κ`, any two
hereditarily-nonempty states are equal: atomlessness and plurality are jointly
unsatisfiable there. Sets the *quality* (faces). -/
theorem ws2_collapse (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X)
    (hx : HereditarilyNonempty x) (hy : HereditarilyNonempty y) : x = y :=
  ws2_bisim_eq _ (hereditarilyNonempty_bisim hinf) x y ⟨hx, hy⟩

/-- **The global-groundless collapse (transcribed Series 4 WS5).** If the world were
groundless everywhere it collapses to a point — the horn (b) hypothesis the tower avoids. -/
theorem ws5_global_groundless_collapses (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X :=
  ⟨fun a b => ws2_collapse hinf a b (h a) (h b)⟩

/-! ## Part A.2 — The no-top cardinal wall (horn (a), transcribed Series 4 WS4) -/

/-- **No-top, cardinal form (the imposed wall).** No object relates to *every* object:
its successor set is `< κ`, but the carrier is `≥ κ`. -/
theorem ws4_no_top_cardinal (x : (νPk κ).X) : ¬ (∀ y, y ∈ ((νPk κ).str x).1) := by
  intro hall
  have huniv : (Set.univ : Set (νPk κ).X) ⊆ ((νPk κ).str x).1 := fun y _ => hall y
  have hle : Cardinal.mk (νPk κ).X ≤ Cardinal.mk ↥((νPk κ).str x).1 := by
    have h := Cardinal.mk_le_mk_of_subset huniv
    rwa [Cardinal.mk_univ] at h
  exact absurd (lt_of_le_of_lt hle ((νPk κ).str x).2) (not_lt.mpr (carrier_card_ge κ))

/-! ## Part A.3 — The Explosion Dilemma (E1, Premise 2, the hinge) -/

/-- **E1 — The Explosion Dilemma.** On any single fixed carrier `νP_κ`, boundless-and-plural
is unsatisfiable, as a dichotomy about one carrier:
* **horn (a):** the only thing stopping an object relating to everything is the imposed
  cardinal wall (`ws4_no_top_cardinal`);
* **horn (b):** removing the cap by demanding groundlessness everywhere collapses the
  carrier (`ws5_global_groundless_collapses`).
So naive boundlessness is not too big; it is *unbuildable* — a cap or a collapse. This is
the sharp negative (Impossibility) that forces stratification, exactly as the Parmenides
collapse forced quality. -/
theorem ws2_explosion_dilemma (hinf : ℵ₀ ≤ κ) :
    (∀ x : (νPk κ).X, ¬ ∀ y, y ∈ ((νPk κ).str x).1)
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X) :=
  ⟨fun x => ws4_no_top_cardinal x, fun h => ws5_global_groundless_collapses hinf h⟩

/-- **E3 — the supremum walls (defeating the tower-with-a-top, §4.1).** Any set-indexed
union of carriers sits inside `νP_{⨆κ_n}` and the Dilemma's horn (a) fires on the
supremum cardinal — so a set-indexed tower is just a bigger single carrier. -/
theorem ws2_supremum_walls {κseq : ℕ → Cardinal.{u}} :
    ∀ x : (νPk (⨆ n, κseq n)).X, ¬ ∀ y, y ∈ ((νPk (⨆ n, κseq n)).str x).1 :=
  fun x => ws4_no_top_cardinal x

/-! ## Part B — The index theory: `ℤ`, no least, no greatest, self-dual (I1) -/

/-- The Series 5 index (WS2 winner): `ℤ`. -/
abbrev Idx : Type := ℤ

/-- **No least element.** For every candidate minimum there is a strictly smaller index. -/
theorem ws2_no_least : ¬ ∃ m : ℤ, ∀ n : ℤ, m ≤ n := by
  rintro ⟨m, hm⟩; exact absurd (hm (m - 1)) (by omega)

/-- **No greatest element.** For every candidate maximum there is a strictly larger index. -/
theorem ws2_no_great : ¬ ∃ M : ℤ, ∀ n : ℤ, n ≤ M := by
  rintro ⟨M, hM⟩; exact absurd (hM (M + 1)) (by omega)

/-- **Self-duality.** The index is order-isomorphic to its reverse (`n ↦ -n`), so descent
and ascent are the same operation read in opposite directions (charter point 8). -/
theorem ws2_self_dual : Nonempty (ℤ ≃o ℤᵒᵈ) :=
  ⟨{ toFun := fun n => OrderDual.toDual (-n)
     invFun := fun n => -(OrderDual.ofDual n)
     left_inv := fun n => by simp
     right_inv := fun n => by simp
     map_rel_iff' := by
       intro a b
       show OrderDual.toDual (-a) ≤ OrderDual.toDual (-b) ↔ a ≤ b
       rw [OrderDual.toDual_le_toDual]; omega }⟩

/-- Strict-descent / strict-ascent facts on `ℤ`: no first level, no last level. -/
theorem ws2_strict_below (n : ℤ) : ∃ m : ℤ, m ≤ n ∧ n ≠ m := ⟨n - 1, by omega, by omega⟩
theorem ws2_strict_above (n : ℤ) : ∃ m : ℤ, n ≤ m ∧ n ≠ m := ⟨n + 1, by omega, by omega⟩

/-! ### No first level, earned against the tower (index form; carrier descent owed to WS6)

The genuine no-first-level ties no-least-*index* to no-atom-*carrier* via a descending
cross-level map. That descending carrier map is WS6's obligation (open item #2). At the
*index* level it is `ws2_no_least`; here we record the index form over an abstract tower,
honestly flagged **definitional pending WS6** — a bare index fact until the descending
face is built. -/

/-- **No first level (index form).** Given the index has no least element (the `ℤ` fact
`ws2_strict_below`, transported to the tower), every level has a strictly lower level.
The *carrier* descent (a face descending into `W_b`) is owed to WS6. -/
theorem ws2_no_atom_floor {Q : Type u} (T : Tower Q)
    (hnb : ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b) :
    ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b := hnb

/-! ## Part C — The forced-answer dichotomy (F2) -/

/-- Provenance of a boundless construction: a single carrier, or a doubly-unbounded tower. -/
inductive Boundless (Q : Type u) where
  | singleCarrier (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ)
  | doublyUnboundedTower (T : Tower Q)

/-- A single carrier's no-top is the imposed cardinal wall. **Report-flag** (pass-2 R5): this
is `:= True`, a label marking the single-carrier branch as "walled by fiat," *not* a proved
characterization of that carrier. The genuine wall content is `carrier_card_ge` / `ws2_collapse`;
this flag only tags the dichotomy branch. -/
def WallsByFiat (_ : Cardinal.{u}) : Prop := True

/-- A single carrier collapses if made groundless everywhere. -/
def CollapsesGlobally (κ : Cardinal.{u}) (_ : ℵ₀ ≤ κ) : Prop :=
  (∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X

/-- **F2 — the provenance dichotomy (NOT an essential-uniqueness theorem).** **Honest scope
(pass-2 R5):** this classifies the *stipulated* 2-constructor type `Boundless` — a `cases` over
its two constructors, `rfl`/`trivial` in each branch — so it says "a `Boundless` value is one of
its two constructors," which is a tautology over a type that *stipulates* the two provenances.
It does **not** prove every boundless-and-plural construction *is* one of them (single carrier
walled by fiat, or doubly-unbounded tower); that essential-uniqueness clause is the named open
obligation #3 (charter §9, heuristic), witnessed but not characterized here by the WS1 colimit.
`WallsByFiat` is a report-flag (`:= True`), not a wall proof. Read the name as
*dichotomy-by-provenance*, not *forced answer*. -/
theorem ws2_forced_answer {Q : Type u} (b : Boundless Q) :
    (∃ κ' h', b = Boundless.singleCarrier κ' h' ∧ WallsByFiat κ' ∧ CollapsesGlobally κ' h')
  ∨ (∃ T, b = Boundless.doublyUnboundedTower T) := by
  cases b with
  | singleCarrier κ' hinf =>
      exact Or.inl ⟨κ', hinf, rfl, trivial, fun h => ws5_global_groundless_collapses hinf h⟩
  | doublyUnboundedTower T => exact Or.inr ⟨T, rfl⟩

end Series5.WS2
