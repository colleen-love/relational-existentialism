# 2.03-mechanization-a — Work Order: Certify the Mirror

**This document describes:** `scratch/formal/Spec203.lean` (new file; imports `Spec201`, `Spec201b`, `Spec201c`, `Spec201d`)
**Normative sources:** `scratch/spec/2-03.md` (the finding), `scratch/spec/2-00.md` (current, with the 2-03 corrections). Specs win; report discrepancies.
**Audience:** Claude Code. All conventions in force. This order is deliberately small: it certifies a finding, corrects the record, and banks the honesty lemmas — a half-day, not a construction. **Read 2-03 §0–§2 before writing a line; the doc-comments in this file are the finding's permanent record and must carry its meaning, not just its statements.**

---

## 1. Purpose and scope

Spec201c constructed Ω₀ correctly for a signature that turns out to be the boolean shadow in two-sorted clothing. T1 fires: the universe is one point. This order proves that fact with dignity, proves the coincidence of the framework's four forbidden extremes at that point, and mechanizes the honesty lemmas that prevent any future misreading of T5/T10's current status.

| ID | Name | Priority |
|----|------|----------|
| DIAG | `G_unit_subsingleton` — the F(1) diagnosis: G(1) ≅ 1 | MUST |
| UNIT | `unitRaw` + `isFinalBRaw_unitRaw` — the one-point bounded-final Raw | MUST |
| T17 | **`omega_collapse : ∀ x y : Ω₀, x = y`** — the Mirror, certified | MUST |
| T18 | `extremes_coincide` — Total, Windowless, saturation, self-anchoring at one point | MUST |
| HON | `genesis_vacuous : Genesis` and `eqDepth_trivial : ∀ n x y, EqDepth n x y` | MUST |
| DOC | Spec housekeeping (§6) | MUST |

**Out of scope:** the corrected functor (awaits O-2-03-1 — the owner's fork ruling); anything that would *repair* rather than *certify* (no new functors, no candidate F(1) computations — those are pre-registered deliverables of the correction spec, D20); the S1 pigeonhole; T4/T7.

**Tone requirement for doc-comments:** this file records the project's machinery catching the project's authors. Write it with the confidence that deserves — the Mirror is a *result*, not an embarrassment. The 2-03 §0 framing ("T1 firing on our own construction"; "the boolean shadow in two-sorted clothing") should appear nearly verbatim in `omega_collapse`'s comment.

---

## 2. DIAG and UNIT

```lean
/-- Spec 2-03 D20 — THE F(1) DIAGNOSIS. Over a one-point world there is exactly
one possible unfolding: `Sym2 PUnit` is a singleton, and the nonempty finite
subsets of a singleton are one element. G(1) ≅ 1 is the collapse criterion made
concrete — the Parmenides check, failed by the quality-free signature. Every
future functor computes this BEFORE construction (D20, pre-registered). -/
theorem G_unit_subsingleton : Subsingleton (G PUnit) := by
  sorry
```

Plan: `Subsingleton (Sym2 PUnit)` first (two `Sym2.ind`s + `Subsingleton PUnit`); then two elements of `G PUnit` have equal carriers by `Set.ext` — membership in each is settled by nonemptiness + the `Sym2 PUnit` subsingleton (any member of either set equals any member of the other); finish with `Subtype.ext`.

```lean
/-- The one-point bounded Raw: one object, one self-relation, whole-pattern.
The Raw form of Spec200's `Shadow.unit`. -/
def unitRaw : Raw where
  O := PUnit
  R := PUnit
  endpoints _ := s(PUnit.unit, PUnit.unit)
  pat _ := Set.univ
  pat_nonempty _ := ⟨PUnit.unit, trivial⟩

/-- The one-point Raw is final among bounded Raws — the two-sorted `unit_final`.
Existence: constant maps; `end_comm` because `Sym2 PUnit` is a subsingleton;
`pat_comm` because `Set PUnit`'s universe equals the image of any nonempty set
(the Spec200 crux, reused: nonemptiness is used exactly once, and must be).
Uniqueness: both carrier maps land in `PUnit`. -/
theorem isFinalBRaw_unitRaw : IsFinalBRaw unitRaw := by
  sorry
```

Plan: boundedness — `Set.univ : Set PUnit` is finite (`Set.finite_univ`, PUnit is a Fintype). Existence: `fO := fun _ => PUnit.unit`, `fR := fun _ => PUnit.unit`; `end_comm` by `Subsingleton.elim` on `Sym2 PUnit`; `pat_comm`: show `Set.univ = (fun _ => PUnit.unit) '' A.pat x` — `Set.eq_univ_iff_forall`, any `p : PUnit` is `PUnit.unit`, witness from `A.pat_nonempty x` (the crux). Uniqueness: `cases`/`congr`/`funext`/`Subsingleton.elim` per the Spec200/201c pattern.

## 3. T17 — the Mirror

```lean
/-- Spec 2-03 T17 — THE MIRROR. The constructed universe is a single point:
T1 firing on our own construction. The signature of 2-01 §2 — relations
individuated by bare endpoints, no grading anywhere in the functor — is the
boolean shadow in two-sorted clothing, and the framework's first theorem
enforced itself against the framework's authors. The construction (Spec201c)
is CORRECT; what it constructs is the One. ω̂ is not Ω's first citizen; it is
its only citizen. Derived structure (contexts, apertures, dyads) is
bisimilarity-invariant and cannot individuate — the D4 corollary, returning.
The many require loss in the functor (2-03 D21). This is the hostile-first
culture working exactly as designed: the formalization fought back and won. -/
theorem omega_collapse : ∀ x y : Ω₀, x = y := by
  sorry
```

**Route A (recommended — canonicity earning its keep):** `final_unique ZΩ unitRaw isFinalBRaw_ZΩ isFinalBRaw_unitRaw` yields `f : Hom ZΩ unitRaw`, `g : Hom unitRaw ZΩ` with `g.compRaw f = idRaw`. Then for `x y : Ω₀`: `x = g.fO (f.fO x) = g.fO PUnit.unit = g.fO (f.fO y) = y` — the middle equalities by `Subsingleton PUnit` and by reading the composite-equals-id equation at `x` and `y` (extract the carrier-map equation from the `Hom` equality via `congrArg` — the same move `final_subsingleton` used in Spec200; consult it).

**Route B (fallback, if Route A's Hom-equality extraction fights):** `identity_by_unfolding` with the total relation. The bisimulation obligation under the pinned mathlib's `Liftr` formulation requires, for arbitrary `a b : G Ω₀`, an element of `G {p // True}`-flavored type projecting to each: build it by pairing — for `p = s(p₁,p₂)` and a fixed `q₀ = s(q₁,q₂) ∈ b.1`, the element `s((p₁,q₁),(p₂,q₂))` projects correctly; take the union of `a`-indexed pairings against a fixed `q₀ ∈ b` with `b`-indexed pairings against a fixed `p₀ ∈ a` (both exist by nonemptiness); images recover `a.1` and `b.1` exactly. Fiddlier than Route A; use only if needed, and record which route shipped.

```lean
/-- ω̂'s corrected gloss, as a corollary with its own name: the only citizen. -/
theorem omegaHat_only : ∀ x : Ω₀, x = omegaHat := fun x => omega_collapse x omegaHat
```

## 4. T18 — the Coincidence of Extremes

```lean
/-- The collapsed universe as a Model: coherence holds because everything is
everything (Subsingleton membership); `dy` is the only choice available. -/
noncomputable def ZΩModel : Model where
  O := Ω₀
  R := Sym2 Ω₀
  endpoints := id
  pat := ZΩ.pat
  pat_nonempty := ZΩ.pat_nonempty
  coherent := by sorry  -- r ∈ pat x: `Sym2 Ω₀` is a subsingleton (from
                        -- omega_collapse), so r equals some member of the
                        -- nonempty pat x; conclude by rewriting.
  dy _ := omegaHat

/-- Spec 2-03 T18 — THE COINCIDENCE OF EXTREMES. In the collapsed universe the
four extremes the framework forbids are provably one point: ω̂ is Total (its
pattern is everything), Windowless (Internal = pat), and its self-relation is
SelfAnchored with saturating aperture (ctx = pat — the `reflexive_saturation`
configuration, whose witness model was this universe all along). T16, C1, S0,
and A1 are four faces of a single exclusion: the One cannot live among the many.
The exclusion zone of the entire framework is a point — and this project
constructed it. (C1's conditional stands consistent: its no-total hypothesis
fails exactly here, as it should.) -/
theorem extremes_coincide :
    Total ZΩModel omegaHat ∧
    Windowless ZΩModel omegaHat ∧
    ∃ r ∈ ZΩModel.pat omegaHat,
      SelfAnchored ZΩModel r ∧ ctx ZΩModel omegaHat r = ZΩModel.pat omegaHat := by
  sorry
```

Plan: everything reduces to two subsingleton facts — `Subsingleton Ω₀` (from `omega_collapse`) and hence `Subsingleton (Sym2 Ω₀)` — plus `pat_nonempty`. Total: `Set.eq_univ_iff_forall` + any member equals any member. Windowless: `Set.ext`; the `ContainedIn` condition is a subset relation between patterns over a subsingleton — everything is everything. The relation witness: `pat_nonempty` supplies `r`; `SelfAnchored` and the saturation both by subsingleton membership. Expect ~30 lines of `Subsingleton.elim` plumbing; write a local helper `sym2_subsingleton : Subsingleton (Sym2 Ω₀)` first and lean on it throughout.

## 5. HON — the honesty lemmas

```lean
/-- HONESTY LEMMA (Spec 2-03 §1). Genesis is VACUOUSLY TRUE over the collapsed
universe — everything is depth-matched by ω̂'s orbit because everything IS ω̂.
This is not a resolution of T10; it is the reason T10 must be re-anchored
against the corrected Ω (2-03 §5). Kept in the file so no later reader
mistakes the anchor for the answer. -/
theorem genesis_vacuous : Genesis := by
  sorry -- ω̂ ∈ omegaOrbit by refl; EqDepth by eqDepth_trivial below (order the
        -- two lemmas accordingly) or by omega_collapse + eqDepth_refl.

/-- HONESTY LEMMA. EqDepth is trivially total over the collapsed universe —
the density surrogate currently has no content. Template survives; content
awaits the corrected Ω. -/
theorem eqDepth_trivial : ∀ (n : ℕ) (x y : Ω₀), EqDepth n x y := by
  sorry -- rewrite y to x by omega_collapse; eqDepth_refl.
```

## 6. Spec housekeeping (MUST)

The 2-00 corrections (T2/T5/T10 labels, T17/T18 entries, D7 verdict, O1, series plan) ship in this PR from the spec author — **reconcile, do not duplicate**: if your in-flight branch carries the Spec201c/d label updates for T2/T5/T10, the 2-03-corrected labels supersede them (they *include* the c/d outcomes plus the collapse); resolve merge conflicts in favor of the 2-03 wording and note the reconciliation in the PR description. After this order lands, update: T17 → `[proved (Spec203): omega_collapse; route recorded]`; T18 → `[proved (Spec203)]`; the HON pair noted at T5/T10's entries. In `2-02.md` §7: remaining Series-2 work now reads — the O-2-03-1 ruling, then the corrected-functor spec + F(1) pre-registration, then re-anchoring (2-03 §5), then S1/T4/T7 against the corrected Ω.

Mapping table per convention; record which T17 route shipped; deviations recorded.

---

*End of work order. Small on purpose: certification, not construction. The file it produces is the repo's proudest scar — the place where the machinery turned on its makers and the makers wrote it down. `omega_collapse`'s doc-comment is the sentence future readers will quote; take the time to make it exact.*
