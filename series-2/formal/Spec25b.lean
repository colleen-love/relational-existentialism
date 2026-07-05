/-
Spec 2.5b — T7 (identity as the limit of observer-local equalities), the T4 close-out, the
depth-family bridge, and the Stage 4–5 attempts of the closing contract.

Normative source: `series-2/2-5.md` (§5 the formal targets, T7 / FP-D5; §6 FP-D7) and the work
order `2-5-mechanization-a.md` Stages 3–5. Continues `Spec25a.lean` (the D19 pack). Specs win.

STANDING DISCIPLINE (2-5-mechanization-a): no proof term below depends on D19 for its mathematics.
The D25 verb emendation (`know`, not observe) is in force doc-side; legacy identifiers keep their
names (see the Spec25a glossary header). `ApproxW w x y` reads "x and y are known alike by w".

THE HEADLINE (T7, Stage 3): **identity is the limit of observer-local equalities.** The framework's
oldest strong claim (2.0 §2.6 as corrected, A3's strong form) lands in full over Ω_C, and it lands
on BOTH sorts:
  * relation sort — *an object is its unfolding*: bisimilarity ⟺ equality (`bisimC_iff_eq`, the
    coinductive core, `Cofix.bisim` re-exported for the corrected functor);
  * object sort — *identity is the limit of observer-local equalities*: `∀ w, ApproxW w x y ⟺ x = y`
    (`identity_is_limitC`), the substantive direction discharged by the **self-observer** (`w := x`,
    `w := y`) — the limit point of the observer family is the being itself.
The depth-family reading (`EqDepthR`) is bridged by reflexivity (`eqDepth_of_eq`); the ω-limit
`(∀ n, EqDepthR n r s) → r = s` is a corollary of the coinductive core and is not load-bearing —
the observer-local route already secures identity outright.
-/
import Spec25a

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 3 — T7, relation sort: the coinductive core (2.5 §5, FP-D5)

*An object is its unfolding.* Bisimilarity ⟺ equality over Ω_R, the corrected analogue of
Spec21d's `identity_by_unfolding`, re-exporting `QPF.Cofix.bisim` at the corrected functor's door. -/

/-- Relation lifting is reflexive on the diagonal: `Functor.Liftr (=) z z` for every `z : HC Ω_R`.
The witness is `repr z` used on both sides (`abs_repr` closes the reconstruction). -/
theorem liftr_eq_refl (z : HC ΩR) : Functor.Liftr (· = · : ΩR → ΩR → Prop) z z := by
  rw [QPF.liftr_iff (F := HC)]
  exact ⟨(QPF.repr z).1, (QPF.repr z).2, (QPF.repr z).2,
    (QPF.abs_repr z).symm, (QPF.abs_repr z).symm, fun _ => rfl⟩

/-- A (coalgebraic) bisimulation on Ω_R: a relation whose related pairs have relation-lifted
unfoldings. The corrected `Bisim`. -/
def BisimC (r s : ΩR) : Prop :=
  ∃ R : ΩR → ΩR → Prop, R r s ∧
    ∀ a b, R a b → Functor.Liftr R (QPF.Cofix.dest (F := HC) a) (QPF.Cofix.dest (F := HC) b)

/-- **T7, coinductive core** — 2.5 §5, FP-D5: two relations of Ω_R related by any bisimulation are
equal. `QPF.Cofix.bisim` re-exported for the corrected functor (the analogue of Spec21d's
`identity_by_unfolding`). This is the representation-layer half of identity-as-limit. -/
theorem identity_by_unfoldingC (R : ΩR → ΩR → Prop)
    (H : ∀ x y, R x y →
      Functor.Liftr R (QPF.Cofix.dest (F := HC) x) (QPF.Cofix.dest (F := HC) y)) :
    ∀ x y, R x y → x = y :=
  QPF.Cofix.bisim R H

/-- **T7, relation sort (full biconditional)** — bisimilarity IS equality on Ω_R: equality is the
greatest bisimulation. Forward is `identity_by_unfoldingC`; the diagonal is a bisimulation by
`liftr_eq_refl`. *An object is its unfolding, ad infinitum* — machine-checked over Ω_C. -/
theorem bisimC_iff_eq (r s : ΩR) : BisimC r s ↔ r = s := by
  constructor
  · rintro ⟨R, hrs, hbis⟩
    exact identity_by_unfoldingC R hbis r s hrs
  · rintro rfl
    exact ⟨(· = ·), rfl, fun a b hab => by subst hab; exact liftr_eq_refl _⟩

/-! ## Stage 3 — T7, object sort: identity as the limit of observer-local equalities (FP-D5)

The substantive direction the framework has carried since 2.0 §2.6: `∀ w, ApproxW w x y → x = y`.
The route is the **self-observer** — instantiate the observer family at `w := x` and `w := y`. The
limit point of "known alike by every w" is the being itself; there, local agreement forces equality
of patterns, and (for Ω_C, where an object IS its pattern) equality outright. -/

/-- The self-observer lemma: if two objects are known alike by *every* observer, their patterns are
equal. Instantiating at `w := x` gives `pat x ⊆ pat y`; at `w := y`, the reverse. -/
theorem approxW_all_imp_pat (A : RawC) (x y : A.O) (h : ∀ w, ApproxW A w x y) :
    A.pat x = A.pat y := by
  have hx := h x
  have hy := h y
  rw [ApproxW, Set.inter_self] at hx    -- hx : A.pat x = A.pat y ∩ A.pat x
  rw [ApproxW, Set.inter_self] at hy    -- hy : A.pat x ∩ A.pat y = A.pat y
  apply Set.Subset.antisymm
  · rw [hx]; exact Set.inter_subset_left
  · rw [← hy]; exact Set.inter_subset_left

/-- **T7 — THE HEADLINE**, 2.5 §5, FP-D5: over Ω_C, `identity is the limit of observer-local
equalities`. Two objects are equal iff every observer knows them alike. Forward is reflexivity of
`ApproxW`; the substantive `←` is `approxW_all_imp_pat` (the self-observer) plus `Subtype.ext` (an
object of Ω_C IS its pattern). A3's strong form, 2.0 §2.6 as corrected — landed in full over the
constructed, plural universe. -/
theorem identity_is_limitC (x y : ΩO) : (∀ w, ApproxW ZΩC w x y) ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (approxW_all_imp_pat ZΩC x y h)
  · rintro rfl w
    exact approxW_refl ZΩC w x

/-! ## Stage 3 — T4 close-out (2.5 §5): the profile/π reconciliation, O8 ratified

The order's remaining T4 item: reconcile the profile-over-`pat(w)` reading with the `ApproxW`
definition. It is definitional — `ApproxW w x y` is exactly `π(x,w) = π(y,w)`, the equality of the
two shared parts. O8's all-finite-depths default is ratified-by-default (owner has not objected;
recorded here per the order, pointer to 2.5 §5). -/

/-- T4 close-out — the profile/π reconciliation: `x ≈w y` is exactly the equality of the two
observer-shared parts `π(x,w) = π(y,w)`. Definitional; the profile reading and the `ApproxW`
definition are the same statement. -/
theorem approxW_iff_piC (A : RawC) (w x y : A.O) :
    ApproxW A w x y ↔ piC A x w = piC A y w := Iff.rfl

/-! ## Stage 3 — the depth-family bridge (2.5 §5): EqDepth reflexivity, forward direction -/

/-- `SumLiftC` of reflexive relations is reflexive (sort-respecting diagonal). -/
theorem sumLiftC_refl (Ro : ΩO → ΩO → Prop) (Rr : ΩR → ΩR → Prop)
    (hO : ∀ x, Ro x x) (hR : ∀ r, Rr r r) : ∀ z : ΩO ⊕ ΩR, SumLiftC Ro Rr z z
  | Sum.inl x => hO x
  | Sum.inr r => hR r

mutual
  /-- `EqDepthR n` is reflexive at every depth (the corrected `eqDepth_refl`, relation sort). -/
  theorem eqDepthR_refl : ∀ (n : ℕ) (r : ΩR), EqDepthR n r r
    | 0, _ => trivial
    | n + 1, r => by
        show RelEx.TwoSorted.Sym2Lift (SumLiftC (EqDepthO n) (EqDepthR n))
              (ZΩC.endpoints r) (ZΩC.endpoints r)
        exact RelEx.TwoSorted.sym2Lift_refl _
          (sumLiftC_refl _ _ (eqDepthO_refl n) (eqDepthR_refl n)) _
  /-- `EqDepthO n` is reflexive at every depth (object sort, Egli–Milner diagonal). -/
  theorem eqDepthO_refl : ∀ (n : ℕ) (x : ΩO), EqDepthO n x x
    | 0, _ => trivial
    | n + 1, x => by
        show RelEx.TwoSorted.SetLift (EqDepthR n) x.1 x.1
        exact ⟨fun p hp => ⟨p, hp, eqDepthR_refl n p⟩,
               fun q hq => ⟨q, hq, eqDepthR_refl n q⟩⟩
end

/-- The forward depth-family bridge: equal relations agree to *every* finite depth. The metric-free
face of "identity is the limit of depth-wise agreement" (2.0 §2.6). The reverse ω-limit
`(∀ n, EqDepthR n r s) → r = s` follows from the coinductive core (`bisimC_iff_eq`) and is not
load-bearing — `identity_is_limitC` already secures identity on the observer family. -/
theorem eqDepth_of_eq {r s : ΩR} (h : r = s) : ∀ n, EqDepthR n r s :=
  fun n => h ▸ eqDepthR_refl n r

/-! ## Stage 4 — reach_infinite (2.5 §5, T10 partial; SHOULD)

The seeds' universe reaches infinitely many relations along a constitutive-descent spine. The tower
family (Spec24e) is an infinite injective spine, and each `tower (n+1)` has `tower n` one
constitutive step inside it (`DescC`), so the range is an infinite descending chain. Full
`ReachableFromSeeds` (the depth-density of the seeds' orbit) stays OPEN, exactly as anchored in
Spec24d — this is the infinity of the spine, not the closure of the orbit. -/

/-- The descent spine: `tower n` is one constitutive step inside `tower (n+1)` (a relation endpoint
of its unfolding). The corrected `Desc` along the tower. -/
theorem tower_succ_desc (n : ℕ) : DescC (tower n) (tower (n + 1)) := by
  show Sum.inr (tower n) ∈ ZΩC.endpoints (tower (n + 1))
  rw [dest_tower_succ]
  exact Sym2.mem_iff.mpr (Or.inl rfl)

/-- T10 partial — `reach_infinite`: the tower spine reaches INFINITELY many distinct relations. The
range of `tower` is infinite (FP-C1's injectivity), and by `tower_succ_desc` it is a genuine
constitutive-descent chain — infinitely many elements, each named inside the next. -/
theorem reach_infinite : (Set.range tower).Infinite :=
  Set.infinite_range_of_injective (fun {m n} => tower_eq_imp m n)

/-! ## Stage 5 — C2-strong, hostile (2.5 §6, FP-D7; SHOULD)

FP-D7 predicts C2-strong (any two objects share a relation, `π ≠ ∅`) FALSE over Ω_C. Confirmed:
two honest objects of the constructed universe with EMPTY shared part. -/

/-- The object whose sole known relation is the bearing seed `elt2`. -/
noncomputable def objElt2 : ΩO := ⟨{elt2}, Set.finite_singleton _, Set.singleton_nonempty _⟩
/-- The object whose sole known relation is the self-witnessing loop `elt3`. -/
noncomputable def objElt3 : ΩO := ⟨{elt3}, Set.finite_singleton _, Set.singleton_nonempty _⟩

/-- Their shared part is empty (`elt2 ≠ elt3`, the anti-Mirror). -/
theorem piC_objElt_empty : piC ZΩC objElt2 objElt3 = ∅ := by
  show ({elt2} : Set ΩR) ∩ {elt3} = ∅
  rw [Set.singleton_inter_eq_empty, Set.mem_singleton_iff]
  exact elt2_ne_elt3

/-- **FP-D7 — CONFIRMED (hostile): C2-strong is FALSE over Ω_C.** Two distinct honest objects of the
constructed universe share no relation — `π = ∅`. Recorded against 2.2 §1.2: the strong overlap
law does not hold on the plural universe; disjoint acquaintance is a citizen. -/
theorem not_C2_strong : ∃ x y : ΩO, piC ZΩC x y = ∅ ∧ x ≠ y :=
  ⟨objElt2, objElt3, piC_objElt_empty,
   fun h => elt2_ne_elt3 (Set.singleton_injective (congrArg Subtype.val h))⟩

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms bisimC_iff_eq
#print axioms identity_is_limitC
#print axioms approxW_iff_piC
#print axioms eqDepth_of_eq
#print axioms reach_infinite
#print axioms not_C2_strong
end AxiomAudit

/-
================================================================================
2-5-mechanization-a Stages 3–5 ↔ this file
================================================================================
-- Stage 3 (MUST)  T7 relation sort  → liftr_eq_refl, BisimC, identity_by_unfoldingC,
--                                      bisimC_iff_eq                                    DELIVERED
--                 T7 object sort    → approxW_all_imp_pat, identity_is_limitC (HEADLINE) DELIVERED
--                 T4 close-out      → approxW_iff_piC (profile/π reconciliation);
--                                      O8 all-finite-depths ratified-by-default (doc)    DELIVERED
--                 depth bridge      → sumLiftC_refl, eqDepthR_refl/eqDepthO_refl,
--                                      eqDepth_of_eq (forward)                           DELIVERED
-- Stage 4 (SHOULD) reach_infinite   → tower_succ_desc, reach_infinite                   DELIVERED (partial)
--                  closing_denseC   → still DEFERRED (drop clause, 3rd use): the
--                                      truncation/density assembly remains out of the
--                                      depth machinery in hand; no sorry, logged OPEN.  deferred
-- Stage 5 (SHOULD) FP-D7 C2-strong  → objElt2/3, piC_objElt_empty, not_C2_strong        CONFIRMED (false)
--                  T13 full         → per-step bound `receivedC_bound`/`residue_
--                                      nontransmissible` (Spec25a) in hand; the length
--                                      induction carries to Series 3.                    deferred
--                  D14(b)           → needs EqDepth antitonicity (a real lemma); the
--                                      instrument (EqDepthR) is in hand, the monotone
--                                      stabilization carries to Series 3.                deferred
--                  T14d (MAY)       → dropped (final call, per order).                   dropped
--
-- The ω-limit `(∀ n, EqDepthR n r s) → r = s` is a corollary of bisimC_iff_eq and is not
-- load-bearing: identity_is_limitC secures T7 on the observer family outright. Nothing here
-- consults §8 as a mathematical hypothesis; D25 is doc-side only.
-/
