# WS4 — No first, no last: the doubly-open tower, its poles, and the view from nowhere

**Design doc. Series 5. Owns: unboundedness above and below; global groundlessness without collapse; the pole coincidence (self-duality) or its honest lopsided alternative; and no-view-from-nowhere forced by no-first-no-last — the coincidence Series 4 could not deliver.**

*Standalone. Depends on WS1 (`Tower`, `Winf`, `destInf`), WS2 (the `ℤ` index with `ws2_no_least`, `ws2_no_great`, `ws2_self_dual`, and the decoupling behind `ws5_global_groundless_collapses`), WS3 (`ws3_no_top`). Transcribes Series 4's `ws4_view_is_positioned` (V1) and its review-R2 finding that V2 was the cardinal wall in disguise — the failure this workstream is charged to repair.*

## The object at stake

This is the workstream where Series 5 either genuinely surpasses Series 4 or relocates its failure up a level. Series 4 (review R2) found: V1 ("a view is positioned") is `rfl` (a view was *defined* as a face); the forced partner V2 ("no view from nowhere") did not exist as a face-routed theorem — `ws4_no_global_observer` was the cardinal wall applied observer-side. Series 5's bet: on the tower, "a view from nowhere" = "a view at no level" = "a view at a first or last level," and *there is none*, so no-view is forced by no-first-no-last (a genuinely different mechanism from a cardinality cap). The design must deliver this **and pass the severe anti-laundering duty**: the forced no-view must not secretly reduce to "the index has no extremal element" as a bare order fact — the *facing/view* structure must be load-bearing, or WS4 is the Series 4 failure wearing a new hat and reported Partial again.

**Ambient theory.** WS1's `Winf T`; index `ℤ` (WS2) with proved no-least/no-greatest/self-dual. A **view** is (as in Series 4) a positioned observation — an object together with a chosen successor edge — but now *carrying its level*, so a view is intrinsically "at level α." No monad/distributive law. Self-duality is handled *order-theoretically* per WS1's C4 triage (the categorical bidirectional limit was rejected): descent and ascent are the same colimit construction applied to `ℤ` vs `ℤᵒᵈ`, related by the order-iso `n ↦ -n`.

## Part A — Unbounded above and below, and global groundlessness without collapse

### Candidates

- **A1 — Order-level unboundedness (necessary, decidable).**
```lean
theorem ws4_unbounded_above (T : Tower Q) : ∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b
theorem ws4_unbounded_below (T : Tower Q) : ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b
```
**Paper triage.** For the `ℤ` index these are `ws2_no_great` / `ws2_no_least` transported to the tower — decidable one-liners. Necessary but, alone, bare order facts (the anti-laundering worry). Keep as lemmas.

- **A2 — Global groundlessness without collapse (the real Part-A payoff).**
```lean
/-- Descent never bottoms out (no first level ⇒ every object has a finer relatum),
    yet `W_∞` is NOT a subsingleton — because the collapse hypothesis of
    `ws5_global_groundless_collapses` (atomlessness *within one fixed carrier*) is
    never met: each object is founded relative to the levels below it and unfounded
    only relative to the tower. -/
theorem ws4_groundless_no_collapse (T : Tower Q) (hunb_below : ∀ a, ∃ b, T.le b a ∧ a ≠ b) :
    -- groundless: every object has a strictly-lower relatum (no atom floor)
    (∀ x : Winf T, ∃ y, RelatesInf T y x ∧ StrictlyLower T y x)
    -- non-degenerate: W_∞ has ≥ 2 objects (plurality survives, from WS3/WS-plurality)
  ∧ (∃ a b : Winf T, a ≠ b)
```
**Paper triage — the crux of Part A.** This is the heart of the whole series: groundlessness becomes a *tower-level* property while local foundedness holds at each stratum, so the global-collapse hypothesis is never satisfied. Decidable-on-paper: the first conjunct is `ws2_no_atom_floor` (WS2) transported through the cross-level edge (WS6); the second is plurality (transcribed Series 4 `ws3_plurality_core`, surviving the colimit by WS1 injectivity). **The coincidence duty (severe):** the non-collapse must be *forced by the local/global decoupling*, not read off a definition. The charter demands exhibiting that a *singly*-bounded tower *does* collapse or wall:
```lean
/-- Coincidence: a tower WITH a least level collapses exactly as Series 4's global
    groundlessness does — the decoupling is what saves W_∞. -/
theorem ws4_singly_bounded_collapses (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X
```
This is the transcribed `ws5_global_groundless_collapses`: a "tower" that is really one carrier (a least = greatest level) meets the collapse hypothesis and dies. So the doubly-unbounded tower's survival is *earned against* the single-carrier collapse, not stipulated. **Winner for Part A: A2 with its coincidence.**

## Part B — The poles coincide at the layer level (self-duality) — or the lopsided alternative

### Candidates

- **P1 — Index self-duality (the `ℤ` case, the target).**
```lean
/-- The two absences — the ground never reached by descending, the everything never
    reached by ascending — are ONE absence: the index is order-isomorphic to its
    reverse, so descent and ascent are the same operation read in opposite directions,
    and "no first" ≡ "no last". -/
theorem ws4_poles_coincide (T : Tower Q) (hdual : Nonempty (T.Idx ≃o T.Idxᵒᵈ)) :
    (∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b) ↔ (∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b)
```
**Paper triage.** For `ℤ` the order-iso `n ↦ -n` witnesses `hdual` (`ws2_self_dual`), and the iff is then a transport of quantifiers along it — decidable. This realizes the charter's Series-3-zero-object dream (initial = terminal) *at the layer structure*, where WS1's C4 triage showed the *categorical* biproduct fails but the *order-theoretic* duality holds. **Winner when the index is self-dual.**

- **P2 — Lopsided index (the honest alternative).**
```lean
/-- If the index is NOT self-dual (e.g. ω + ωᵒᵈ glued asymmetrically, or a dense
    order without an order-reversal respecting the cardinal assignment), the poles
    are genuinely two and self-duality is reported FALSE — a real, reportable negative. -/
theorem ws4_poles_split (T : Tower Q) (hlop : IsEmpty (T.Idx ≃o T.Idxᵒᵈ)) :
    ¬ (descent and ascent are the same operation)
```
**Paper triage.** Decidable *given* a specific lopsided index. Its role is to keep P1 honest: pole-coincidence is a theorem *conditional on self-duality*, not a universal truth. For the chosen `ℤ` index P1 holds; P2 is stated to document that a different index (a live option if WS6 needs density and `ℚ`'s reversal fails to respect the cardinals) would split the poles. **Keep both; report P1 for `ℤ`, P2 as the typed alternative.**

**Trade-off (P1 vs P2, feeding the index choice).** `ℤ` (WS2 winner) gives P1 cleanly. If WS6 escalates to `ℚ` for interpolation, self-duality must be re-checked: `ℚ`'s `q ↦ -q` is an order-reversal, but the *cardinal assignment* `κ : ℚ → Cardinal` must satisfy `κ_q ↔ κ_{-q}` compatibly, which is an extra constraint. So the pole-coincidence payoff is a *reason to prefer `ℤ`* unless interpolation forces `ℚ`.

## Part C — No view from nowhere, forced (the Series 4 repair)

### Candidates

- **V1 — A view is positioned (definitional, transcribed — forbidden alone).**
```lean
theorem ws4_view_is_positioned (T : Tower Q) (o : ViewAt T) : ∃ a x y, viewOf o = faceAt T a x y
```
**Paper triage.** This is Series 4's `ws4_view_is_positioned` verbatim — `rfl`, "a view is a face at a level." True, definitional, carries no force alone. Exactly what the coincidence rule forbids reporting as Discharged. Transcribe and mark definitional.

- **V2 — No view from nowhere, forced by no-first-no-last (the forced partner Series 4 lacked).**
```lean
/-- A "view from nowhere" would be a view at NO level — i.e. at a level below all
    levels or above all levels. By no-first-no-last there is no such level, so there
    is no such view. This is FORCED by the index having no extremal element AS
    REALIZED IN THE VIEW STRUCTURE (a view carries its level), not by a cardinality
    cap. The V2 Series 4 could not deliver. -/
theorem ws4_no_view_from_nowhere (T : Tower Q)
    (hna : ∀ a, ∃ b, T.le a b ∧ a ≠ b) (hnb : ∀ a, ∃ b, T.le b a ∧ a ≠ b) :
    ¬ ∃ v : ViewFromNowhere T, True
```
where `ViewFromNowhere T := {v : View // v.level is extremal (first or last)}`.
- **Success condition:** proved from `hna`/`hnb` *through the view's level field* — the view structure carries a level, and "from nowhere" is defined as "at an extremal level," which no-first-no-last empties.
- **Failure mode (the severe anti-laundering risk):** if `ViewFromNowhere` is definable *without* the view/face structure — i.e. if the theorem is really "`ℤ` has no extremal element" with a `View` wrapper painted on — then V2 is a bare order fact and Series 4's failure is relocated up a level. **The strip test:** delete `View`/`face` and replace the view's level field with a bare index element; if the theorem still goes through, it is not earned.

**Paper triage — the decisive test for the whole workstream.** V2 is *provable* (it is `hna`/`hnb` applied to the level field). The question the charter forces is whether it is *earned*. Run the strip test on paper: `ws4_no_view_from_nowhere` says "no view sits at an extremal level." Strip `View`: "no index element is extremal" — which is `ws2_no_least ∧ ws2_no_great`, a bare order fact. **So V2 as stated above DOES launder** — the `View` wrapper is inert, exactly as Series 4's `View` wrapper on the cardinal wall was inert. This is the honest finding the triage produces, and it is not yet a repair.

  The repair candidate that survives the strip test:

- **V3 — No completing view, via the face's cross-level reach (the load-bearing form).**
```lean
/-- A view at level α sees, through its face, only what its face reaches — and by
    WS3's no-top and WS6's leak-free cross-level descent, a face at level α reaches
    strictly less than the whole tower: there are objects at levels above AND below α
    that α's face does not engage. So no view completes the world — and this uses the
    FACE'S reach (a face engages `< κ_α` targets and descends only finitely far at
    positive grade), not merely the index's lack of an endpoint. -/
theorem ws4_no_completing_view (T : Tower Q) (hunb : ∀ c, ∃ a, c < (T.lvl a).card)
    (v : ViewAt T) :
    ∃ y : Winf T, ¬ FaceReaches T v y     -- the view's face misses some object
```
**Paper triage.** Now run the strip test: delete `face`, and the statement "the view's face misses some object" has no content — there is nothing to miss *with*. The face's `< κ_α` reach (WS3) and its finite cross-level descent (WS6 leak-free but grade-bounded) are doing the work: a view at level α engages `< κ_α` targets and descends only to a bounded depth at a time, so objects far above (higher κ, WS3 `ws3_no_top`) and far below (finer grades not yet reached, WS6) escape *its face*. **This survives the strip test because removing the face removes the theorem.** The index's double-openness supplies the "far above and far below," but the *missing* is a fact about the face's reach. **This is the genuine V2 the charter wants — winner for Part C, replacing the laundering V2.**

  The coincidence: V1 (definitional, a view is a face) + V3 (forced, a face cannot complete the tower) are proved *distinct statements that coincide* — the same face structure that positions a view (V1) is what prevents it completing the world (V3).

## Winner: A2 (+coincidence), P1 for `ℤ` (with P2 typed), V1+V3 as the no-view coincidence (V2 recorded as the laundering form the triage rejects)

### The anti-laundering discipline, written into every proof (for WS7)

The charter mandates: *strip "face" and "view" from the statement; if it still goes through as a bare index fact, it is not earned.* WS4 pre-registers the strip test per theorem:
- `ws4_unbounded_above/below`: **bare index facts by design** — kept as lemmas, never reported as payoffs.
- `ws4_groundless_no_collapse`: survives — the non-collapse uses plurality of *objects* (`ws3_plurality_core`), which vanishes if you strip the carrier.
- `ws4_poles_coincide`: bare index fact (order self-duality) — reported honestly as an *index* property, its philosophical reading (descent = ascent of *relating*) flagged as interpretation, not earned by the carrier.
- `ws4_no_view_from_nowhere` (V2): **fails the strip test** — recorded as the laundering form, *not* reported as the payoff.
- `ws4_no_completing_view` (V3): **survives** — reported as the genuine no-view payoff.

This honesty is the whole point of the workstream: it states plainly which payoffs are earned (A2, V3) and which are index facts with philosophical glosses (poles, V2).

### Definitions and lemmas needed

```lean
namespace Series5.WS4

/-- A view carries its level. -/
structure ViewAt (T : Tower Q) where
  level : T.Idx
  obj   : (T.lvl level).carrier
  edge  : {y // y ∈ (lstr obj).1}       -- a chosen successor edge (positioned)

def viewOf (T) (v : ViewAt T) : Set _ := faceAt T v.level v.obj v.edge

/-- What a view's face reaches across the tower (its face composed down/up the levels). -/
def FaceReaches (T : Tower Q) (v : ViewAt T) (y : Winf T) : Prop := ...  -- uses WS6 cross-level face

def StrictlyLower (T : Tower Q) (y x : Winf T) : Prop := ...  -- y's representative level < x's
```

### Proof architecture for V3 (`ws4_no_completing_view`)

1. A view `v` sits at level `α`; its face `faceAt α v.obj v.edge` engages `< κ_α` targets at level α (WS3 local bound) and, extended cross-level (WS6), descends at bounded grade.
2. By `ws3_no_top` (WS3, powered by no-last-level), there is an object at a level `β > α` that `v`'s `< κ_α`-reach cannot cover.
3. That object is missed by `v`'s face: `FaceReaches T v y` is false. ∎ — and step 2 needs `hunb` (no last level), step 1 needs the face (its `< κ_α` reach), so *both* the index's openness and the face are load-bearing, passing the strip test.

**Dependencies on imported upstream theorems.** WS1: `Winf`, `destInf`, `ι_inj`. WS2: `ws2_no_least`, `ws2_no_great`, `ws2_self_dual`, and (transcribed) `ws5_global_groundless_collapses` for the Part-A coincidence. WS3: `ws3_no_top` (for V3 step 2), `ws3_local_bound`. WS6: the cross-level face and its leak-free-but-grade-bounded descent (for `FaceReaches`) — WS4's V3 has a **forward dependency on WS6**; pre-registered, so WS4's V3 is stated with the WS6 cross-level face as a hypothesis until WS6 discharges it. Transcribed Series 4: `ws4_view_is_positioned`, `ws3_plurality_core`.

## What counts as failure

- *Collapse:* if the local/global decoupling fails and `W_∞` meets the collapse hypothesis, `ws4_groundless_no_collapse` fails — the tower is a point, the whole program dies. (Foreclosed by WS1's level-local foundedness.)
- *Poles split unavoidably:* if the only workable index (after WS6) is lopsided, `ws4_poles_coincide` is false — report P2, point 8 as a genuine two-pole negative (charter allows this as honest).
- *No-view laundering:* if only V2 (not V3) is provable — i.e. the face is not load-bearing — report no-view as **Partial**, the Series 4 failure relocated up a level (charter §5.4 explicitly names this outcome).
- *V3's WS6 dependency unmet:* if WS6's cross-level face does not exist (the distributive-law risk), `FaceReaches` is undefined and V3 cannot be stated — report Partial pending WS6.

## Outcome classes (per charter §7)

- **Discharged:** A2 (+ coincidence), P1 (for `ℤ`), V1+V3 coincidence — *conditional on WS6 delivering the cross-level face*.
- **Impossibility proved (a success):** `ws4_singly_bounded_collapses` — a singly-bounded tower collapses — as the coincidence anchor.
- **Partial (the honest-negative outcome the charter foregrounds):** no-view reported Partial if only V2 (laundering) is available; poles reported split if the index is lopsided. Both are first-class per §5.4/§8.

## Deliverable

`series-5/formal/ws4.lean`: `ViewAt`, `viewOf`, `FaceReaches`, `StrictlyLower`; `ws4_unbounded_above/below` (A1 lemmas), `ws4_groundless_no_collapse` + `ws4_singly_bounded_collapses` (A2 + coincidence), `ws4_poles_coincide` (P1) + `ws4_poles_split` (P2), `ws4_view_is_positioned` (V1, transcribed), `ws4_no_view_from_nowhere` (V2, recorded as laundering — NOT a payoff), `ws4_no_completing_view` (V3, the genuine payoff). Per-theorem strip-test annotations for WS7. Axiom check owed on `ws4_groundless_no_collapse` and `ws4_no_completing_view`.
