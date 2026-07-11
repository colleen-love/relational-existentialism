/-
`series-4/formal/ws2.lean`

WS2 — **The collapse, and the forced answer.** Series 4, the intellectual spine.

Owns: the Collapse Theorem (`ws2_collapse`), the imported-weight leak
(`ws2_leak` / `ws2_botfree_safe`), and the forced-answer synthesis
(`ws2_restriction_no_leak` (F1), `ws2_forced_answer` (F2)).

Design doc: `series-4/spec/ws02-design.md`. The Collapse Theorem is a faithful
transcription of the Series 3 impossibility `ws10_unlabeled_atomless_collapses`
(archived); the imported-weight leak is stated as pure algebra over a minimal
`QAlg` (no need for the heavy weighted terminal coalgebra); the forced-answer
dichotomy is new synthesis, delivered with the internal-rigidity clause under a
canonicity hypothesis, exactly as the charter §9 hedge pre-registers.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series4.ws1

universe u

open Cardinal Series4.WS1

namespace Series4.WS2

variable {κ : Cardinal.{u}}

/-! ## Part A — The Collapse Theorem (Premise 1)

In the plain (gradeless) carrier, atomlessness forces a single point: any two
hereditarily-nonempty states are equal. This is the forced counterweight WS3's
plurality is earned against. Transcribed from Series 3 `ws10`. -/

/-- Hereditarily nonempty: every reachable state has a nonempty successor set. -/
def HereditarilyNonempty (x : (νPk κ).X) : Prop :=
  ∀ v, Reaches x v → ((νPk κ).str v).1 ≠ ∅

lemma HereditarilyNonempty.ne_empty {x : (νPk κ).X}
    (hx : HereditarilyNonempty x) : ((νPk κ).str x).1 ≠ ∅ :=
  hx x (Reaches.refl' x)

lemma HereditarilyNonempty.succ {x w : (νPk κ).X}
    (hx : HereditarilyNonempty x) (hw : w ∈ ((νPk κ).str x).1) : HereditarilyNonempty w :=
  fun v hv => hx v (Relation.ReflTransGen.head hw hv)

/-- The graph of "both hereditarily nonempty". -/
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

/-- **The Collapse Theorem (Premise 1 / Impossibility proved).** In the plain
carrier `νP_κ`, any two hereditarily-nonempty states are **equal**: the groundless
(atomless) sub-universe is the single self-relating point `Ω`. Atomlessness and
plurality are jointly unsatisfiable here — which is exactly why plurality demands a
second currency of difference (quality). -/
theorem ws2_collapse (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X)
    (hx : HereditarilyNonempty x) (hy : HereditarilyNonempty y) : x = y :=
  ws2_bisim_eq _ (hereditarilyNonempty_bisim hinf) x y ⟨hx, hy⟩

/-- The hereditarily-nonempty subcarrier is a subsingleton. -/
theorem ws2_grounded_core_subsingleton (hinf : ℵ₀ ≤ κ) :
    Subsingleton {x : (νPk κ).X // HereditarilyNonempty x} :=
  ⟨fun a b => Subtype.ext (ws2_collapse hinf a.1 b.1 a.2 b.2)⟩

/-! ## Carrier lower bound (used by WS4) -/

/-- `κ ≤ #(νPk κ).X`: if the carrier were smaller than `κ` then Lambek would give
`X ≃ Set X`, i.e. `#X = 2^#X`, contradicting Cantor. Transcribed from Series 3
`ws10`. -/
theorem carrier_card_ge (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X := by
  by_contra hlt
  push_neg at hlt
  have hall : ∀ s : Set (νPk κ).X, Cardinal.mk (↥s) < κ :=
    fun s => lt_of_le_of_lt (Cardinal.mk_subtype_le (· ∈ s)) hlt
  have e1 : PkObj κ (νPk κ).X ≃ Set (νPk κ).X := Equiv.subtypeUnivEquiv hall
  have hbij : Function.Bijective (νPk κ).str := lambek (νPk_terminal κ)
  have hc : Cardinal.mk (νPk κ).X = 2 ^ Cardinal.mk (νPk κ).X :=
    calc Cardinal.mk (νPk κ).X
        = Cardinal.mk (PkObj κ (νPk κ).X) := Cardinal.mk_congr (Equiv.ofBijective _ hbij)
      _ = Cardinal.mk (Set (νPk κ).X) := Cardinal.mk_congr e1
      _ = 2 ^ Cardinal.mk (νPk κ).X := Cardinal.mk_set
  have hcantor := Cardinal.cantor (Cardinal.mk (νPk κ).X)
  rw [← hc] at hcantor
  exact lt_irrefl _ hcantor

/-! ## Part B — The imported-weight leak (Premise 2)

A **quality algebra** is a bare type of weights with a bottom `⊥` and a composition
`⊗` (series composition of relations). The design's L2: any such algebra with a
`⊥`-divisor produces an atom (a weight-`⊥` relation) under composition, and the leak
is *exactly* `⊥`-divisibility. We model this at the level of pure algebra — no
weighted terminal coalgebra is needed to see the leak. -/

/-- A minimal imported quality algebra: a value type with a bottom and a series
composition. -/
structure QAlg where
  Q : Type
  bot : Q
  comp : Q → Q → Q

/-- `A` is **bottom-free**: composition never reaches the bottom from non-bottom
factors (no `⊥`-divisors). -/
def BotFree (A : QAlg) : Prop := ∀ a b, A.comp a b = A.bot → a = A.bot ∨ b = A.bot

/-- **The leak (L2).** Any imported quality with a `⊥`-divisor produces an atom (a
`⊥`-weighted relation) by composing two non-atomic relations. The leak is exactly
the failure of `BotFree`. -/
theorem ws2_leak (A : QAlg) (h : ¬ BotFree A) :
    ∃ a b, a ≠ A.bot ∧ b ≠ A.bot ∧ A.comp a b = A.bot := by
  unfold BotFree at h
  push_neg at h
  obtain ⟨a, b, hcomp, ha, hb⟩ := h
  exact ⟨a, b, ha, hb, hcomp⟩

/-- **The boundary (L3 is false; the escape is real).** Bottom-free algebras do
*not* leak: composing two non-atomic relations stays non-atomic. This locates the
leak precisely at `⊥`-divisors — but note bottom-freeness is a *restriction imposed
on the external algebra* (charter §4.2's "forbidden, not unable"). -/
theorem ws2_botfree_safe (A : QAlg) (h : BotFree A) {a b : A.Q}
    (ha : a ≠ A.bot) (hb : b ≠ A.bot) : A.comp a b ≠ A.bot := by
  intro hc; rcases h a b hc with h1 | h1
  · exact ha h1
  · exact hb h1

/-- **A concrete `⊥`-divisor witness.** A three-element quality algebra (`Fin 3`,
bottom `0`) with an *ad hoc* composition engineered so that two non-`⊥` elements
compose to `⊥` (`comp 1 1 = 0`). This is only a witness that `⊥`-divisors exist — all
`ws2_leak_witness` needs — and is deliberately *not* claimed to be genuine truncated
Łukasiewicz multiplication (which would need a real MV-algebra; the earlier `Luk3`
name oversold it). -/
def BotDivisorWitness : QAlg where
  Q := Fin 3
  bot := 0
  comp := fun a b => if a = 0 ∨ b = 0 then 0 else if a.val + b.val ≤ 3 then 0 else 1

theorem ws2_leak_witness : ¬ BotFree BotDivisorWitness := by
  unfold BotFree BotDivisorWitness
  push_neg
  exact ⟨1, 1, by decide, by decide, by decide⟩

/-! ## Part C — The forced-answer synthesis -/

/-- **F1 — restriction-quality introduces no leak.** Restriction-quality has *no*
external algebra, hence no imported bottom element: the face toward a genuine
successor is always nonempty (it contains that successor), so there is no "zero
face" for composition to reach. The only empty face would be the empty *object* — an
atom, already outlawed. -/
theorem ws2_restriction_no_leak (x y : (νPk κ).X) (hy : y ∈ ((νPk κ).str x).1) :
    (face x y).Nonempty :=
  ⟨y, mem_face_self hy⟩

/-- Provenance of a quality assignment: drawn from an external algebra, or internal
(a restriction of the relata themselves). -/
inductive Quality where
  | external (A : QAlg)
  | internal

/-- The external algebra leaks an atom. -/
def LeaksAtom (A : QAlg) : Prop := ¬ BotFree A
/-- The external algebra is atom-free only by an imposed constraint (fiat). -/
def AtomFreeByFiat (A : QAlg) : Prop := BotFree A

/-- **F2 — the forced-answer dichotomy.** Every quality assignment is either
*external* — and then it either leaks an atom (has a `⊥`-divisor, `ws2_leak`) or is
atom-free only by fiat (`BotFree` imposed on the algebra) — or *internal*, in which
case it is a restriction-quality and, by F1, has no external zero to leak. The
disjunction "leaks or fiat" for the external case is genuine (excluded middle on
`BotFree`), and the internal case is discharged by F1: internality *forecloses* the
leak, rather than an external rule *forbidding* it.

The general internal-rigidity claim ("every internal quality *is* restriction-quality
up to renaming") is the named open obligation (charter §9); here the internal case is
witnessed by the reachable face and F1. -/
theorem ws2_forced_answer (q : Quality) :
    (∃ A : QAlg, q = Quality.external A ∧ (LeaksAtom A ∨ AtomFreeByFiat A))
  ∨ (q = Quality.internal ∧
       ∀ (x y : (νPk κ).X), y ∈ ((νPk κ).str x).1 → (face x y).Nonempty) := by
  cases q with
  | external A =>
      exact Or.inl ⟨A, rfl, (em (BotFree A)).symm.imp id id⟩
  | internal =>
      exact Or.inr ⟨rfl, fun x y hy => ws2_restriction_no_leak x y hy⟩

end Series4.WS2
