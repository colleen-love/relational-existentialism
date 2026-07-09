/-
`series-5/formal/ws4.lean`

WS4 — **No first, no last: the doubly-open tower, its poles, and the view from nowhere.**
Series 5.

Owns: unboundedness above and below; global groundlessness without collapse; the pole
coincidence (self-duality) or its honest lopsided alternative; and no-view-from-nowhere,
with the severe anti-laundering discipline that separates the *earned* payoff (V3, the
face's reach is load-bearing) from the *laundering* form (V2, a bare index fact).

Imports WS6 for the cross-level face objects `ViewAt`, `FaceReaches`, `ws6_tower_unknowable`
(the WS4↔WS6 forward edge, resolved by having WS6 own them and WS4 re-export the no-view
payoff). Design doc: `series-5/spec/ws04-design.md` (A2 + P1/P2 + V1/V3, V2 recorded as
laundering).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws6

universe u

open Cardinal Series5.WS1 Series5.WS2 Series5.WS3 Series5.WS6

namespace Series5.WS4

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## Part A — unbounded above/below, and groundless without collapse (A2) -/

/-- **A1 — unbounded above** (a bare index fact, kept as a lemma; fails the strip test by
design). For the `ℤ` index this is `ws2_no_great`. -/
theorem ws4_unbounded_above (T : Tower Q) (hna : ∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b) :
    ∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b := hna

/-- **A1 — unbounded below** (a bare index fact, kept as a lemma). -/
theorem ws4_unbounded_below (T : Tower Q) (hnb : ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b) :
    ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b := hnb

/-- The `ℤ`-index witnesses, concretely (no-last / no-first as strict ascent / descent). -/
theorem ws4_unbounded_above_int : ∀ n : ℤ, ∃ m, n ≤ m ∧ n ≠ m := ws2_strict_above
theorem ws4_unbounded_below_int : ∀ n : ℤ, ∃ m, m ≤ n ∧ n ≠ m := ws2_strict_below

/-- **The coincidence anchor: a singly-bounded ("one carrier") world collapses.** The
transcribed `ws5_global_groundless_collapses`: a "tower" that is really one carrier meets
the global-groundless hypothesis and dies. So `W_∞`'s survival is *earned against* the
single-carrier collapse, not stipulated. -/
theorem ws4_singly_bounded_collapses (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X :=
  ws5_global_groundless_collapses hinf h

/-- **A2 — groundless without collapse.** Two halves:
* **non-degenerate (earned, survives the strip test):** plurality survives the colimit —
  two distinct faced loops at a level stay distinct in `W_∞` (WS1 injectivity + WS3
  distinctness). Delete the carrier and there is nothing to be distinct.
* **the coincidence:** the global-collapse hypothesis fires only *within one carrier*
  (`ws4_singly_bounded_collapses`), which the doubly-unbounded tower never meets — the
  local/global decoupling that is the whole escape.
(The descent-groundlessness — every object has a strictly finer relatum — is delivered on
the WS6 graded spine `descState`/`ws6_descent_nonterminating`; the tower-carrier descending
map is WS6's open obligation.) -/
theorem ws4_groundless_no_collapse (T : Tower Q) (a0 : T.Idx) {q1 q2 : Q} (hq : q1 ≠ q2) :
    (∃ x y : Winf T, x ≠ y)
  ∧ (∀ (κ : Cardinal.{u}), ℵ₀ ≤ κ →
       (∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X) := by
  refine ⟨⟨toColim T (loopState q1 (T.lvl a0).hinf), toColim T (loopState q2 (T.lvl a0).hinf), ?_⟩,
          fun κ hinf h => ws5_global_groundless_collapses hinf h⟩
  intro he
  exact absurd (toColim_level_inj T a0 he) (ws3_loopface_ne (T.lvl a0).hinf hq)

/-! ## Part B — the poles coincide (P1) or split (P2) -/

/-- **P1 — the poles coincide (self-dual `ℤ` index).** The ground never reached by
descending and the everything never reached by ascending are one absence: no-first ≡
no-last, because `ℤ ≃o ℤᵒᵈ` (`ws2_self_dual`). **Strip test: fails** — this is a bare order
self-duality; the philosophical reading (descent = ascent of *relating*) is flagged
interpretation, not earned by the carrier. -/
theorem ws4_poles_coincide :
    (∀ a : ℤ, ∃ b, a ≤ b ∧ a ≠ b) ↔ (∀ a : ℤ, ∃ b, b ≤ a ∧ a ≠ b) :=
  ⟨fun _ n => ⟨n - 1, by omega, by omega⟩, fun _ n => ⟨n + 1, by omega, by omega⟩⟩

/-- **P2 — the honest lopsided alternative.** A lopsided index (here `ℕ`: a least element,
no greatest) has genuinely two poles — descent bottoms out at a floor while ascent does
not — so self-duality is *false* and the poles split. Reported as the typed honest
negative the charter allows. -/
theorem ws4_poles_split :
    (∃ n : ℕ, ∀ m, n ≤ m) ∧ ¬ (∃ n : ℕ, ∀ m, m ≤ n) := by
  refine ⟨⟨0, fun m => Nat.zero_le m⟩, ?_⟩
  rintro ⟨n, hn⟩
  have := hn (n + 1)
  omega

/-! ## Part C — no view from nowhere: V1 (definitional), V2 (laundering), V3 (earned) -/

/-- **V1 — a view is positioned (definitional).** A view *is* an object at a level:
positioned by construction. `rfl`; carries no force alone (exactly what the coincidence
rule forbids reporting as the payoff). -/
theorem ws4_view_is_positioned (T : Tower Q) (v : ViewAt T) : ∃ a : T.Idx, v.level = a :=
  ⟨v.level, rfl⟩

/-- **V2 — no view from nowhere, naive (LAUNDERS — recorded, NOT reported as a payoff).**
"A view from nowhere is a view at an extremal level; there is none." Strip the `View`
wrapper and it is exactly `ws2_no_least ∧ ws2_no_great` — a bare order fact. Kept here to
record honestly that the naive V2 launders, as Series 4's V2 did. -/
theorem ws4_no_view_from_nowhere :
    ¬ (∃ n : ℤ, ∀ m, n ≤ m) ∧ ¬ (∃ n : ℤ, ∀ m, m ≤ n) :=
  ⟨ws2_no_least, ws2_no_great⟩

/-- **V3 — no completing view (the genuine payoff, survives the strip test).** A view's
*face* misses an object: it engages `< κ_α` targets and no level is last, so an object at a
higher level escapes its face. **Delete the face and there is nothing to miss** — the
face's reach is load-bearing, unlike V2. This is the genuine no-view Series 4 lacked. It is
literally WS6's `ws6_tower_unknowable`, read positionally (see `ws4_unknowable_eq_noview`). -/
theorem ws4_no_completing_view (T : Tower Q) (hQ : Nonempty Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (v : ViewAt T) :
    ∃ y : Winf T, ¬ FaceReaches T v y :=
  ws6_tower_unknowable T hQ hunb v

/-- **The coincidence: tower-unknowability = no-completing-view, one theorem.** The
epistemic form (WS6 `ws6_tower_unknowable`) and the positional form (V3) are the *same
proof term* — the no-first-no-last fact read once epistemically and once positionally.
Adjudicated as one theorem, per the charter's "one theorem or two" duty. -/
theorem ws4_unknowable_eq_noview (T : Tower Q) (hQ : Nonempty Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (v : ViewAt T) :
    ws6_tower_unknowable T hQ hunb v = ws4_no_completing_view T hQ hunb v := rfl

end Series5.WS4
