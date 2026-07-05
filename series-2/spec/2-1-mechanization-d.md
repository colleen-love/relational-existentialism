# 2.1-mechanization-d — Work Order: The Unblocked Four (T6, T9, T5, T10) and the Coinduction Principle

**This document describes:** `series-2/formal/Spec201d.lean` (new file; imports `Spec201`, `Spec201b`, `Spec201c`)
**Normative sources:** `series-2/2-0.md` (current), `series-2/2-1.md`, `series-2/2-2.md`. Specs win over this document; report discrepancies.
**Audience:** Claude Code. All prior conventions in force (no `sorry`, no new axioms, audit block, doc-comments with spec IDs, mapping table, deviations recorded, Lake root per precedent). Naming continues the `-b`/`-c` convention: fourth mechanization of 2.1's ground, now *against* the constructed universe.

---

## 1. Purpose and scope

Spec201c changed the tense: Ω exists (`T2_discharged`), inhabited (`omegaHat_coherent`). This order proves the theorem group that existence unblocked — the framework's claims *about* the universe, stated against `ZΩ`. Ordered so the day's first hours bank certain wins (T6, COIND, T9 are tractable) before the one genuinely hard construction (T5).

| ID | Name | Priority |
|----|------|----------|
| T6 | **No constitutive origin**: descent is serial; no well-founded elements; chains at every depth | MUST |
| COIND | **Identity by unfolding** (A4's formal face: bisimilar ⟹ equal, via `Cofix.bisim`) + **self-relation realized** (A5 at ZΩ) | MUST |
| T9 | **Canonicity**: any two bounded-final Raws are isomorphic (`Hom.id`/`Hom.comp` for Raw + `final_unique`) | MUST |
| T5 | **Closure of the closing**: depth-n equivalence `EqDepth`, the finitely-realized ρ, and density — every object is depth-n matched by a finitely-realized one, for every n | MUST, staged with a drop-clause on final assembly |
| T10s | **Genesis, anchored**: the conjecture as a named `Prop` with its orbit machinery — statement only (open in truth-value, D13(3)) | MUST (statement-level) |
| DOC | Spec housekeeping (§7) | MUST |

**Out of scope:** proving or refuting T10 (open in truth-value — anchor only); the S1 pigeonhole (next order); T3, T4, T7; whether `ContainedIn` both ways forces equality in ZΩ (T7 territory — if you notice it while doing T9, note it in the PR, do not prove it); general κ.

---

## 2. T6 — no constitutive origin

The signature made emptiness unformulable; against a constructed inhabited universe that becomes a theorem about descent: unfolding never bottoms out, becoming has no first brick.

```lean
/-- Spec 2.0 T6 / D13(1). One step of constitutive descent: `z` occurs one
level inside `x` — some relation of x's pattern has z among its endpoints. -/
def Desc (A : Raw) (z x : A.O) : Prop :=
  ∃ r ∈ A.pat x, z ∈ A.endpoints r

/-- Descent is serial in EVERY Raw: patterns are nonempty (D4's unformulability)
and every relation has an endpoint (every `Sym2` is inhabited). -/
theorem desc_serial (A : Raw) : ∀ x, ∃ z, Desc A z x := by
  sorry -- obtain r from pat_nonempty; expose an endpoint by `Sym2.ind` on
        -- `A.endpoints r` (or the `out`-projections verified in Spec201c);
        -- coherence is NOT needed here.

/-- Spec 2.0 T6 — NO CONSTITUTIVE ORIGIN. On any inhabited Raw, constitutive
descent is not well-founded: there is no ground floor, no first brick, no atom
at which the descent stops. Instantiated at ZΩ below. The proof is the
unformulability of emptiness cashed out: a well-founded descent would have a
minimal element, but seriality gives every element a predecessor-in-descent. -/
theorem no_constitutive_origin (A : Raw) [Nonempty A.O] :
    ¬ WellFounded (Desc A) := by
  sorry -- intro hwf; obtain minimal m from `hwf.has_min Set.univ ⟨Classical.arbitrary _, trivial⟩`
        -- (verify exact name: `WellFounded.has_min`); contradict with `desc_serial A m`.

theorem no_origin_ZΩ : ¬ WellFounded (Desc ZΩ) :=
  -- Nonempty via omegaHat
  sorry

/-- Corollary: chains of every finite depth descend from every object.
"Ad infinitum" in its concrete form. -/
theorem desc_chain (A : Raw) (x : A.O) :
    ∀ n : ℕ, ∃ c : Fin (n + 1) → A.O, c 0 = x ∧
      ∀ i : Fin n, Desc A (c i.succ) (c i.castSucc) := by
  sorry -- induction on n, extending by desc_serial; mind the Fin plumbing
        -- (`Fin.cases`/`Fin.snoc` or a `Nat`-indexed formulation first, then
        -- restrict — pick whichever fights less and note the choice).
```

Doc-comment duties: T6 does triple duty (2.0 §5) — A1's "ad infinitum" downward, D13(1)'s "no day zero in the order of constitution," and the consistency model for non-well-founded grounding (§6 positioning). Say all three.

## 3. COIND — identity by unfolding, and self-relation realized

```lean
/-- Spec 2.0 A4/A6, the formal face: AN OBJECT IS ITS UNFOLDING. Two objects of
Ω₀ related by any G-bisimulation are equal — the coinduction principle, which is
what "defined by its relations, ad infinitum" MEANS once the universe exists.
This is `QPF.Cofix.bisim` re-exported at the framework's door, with the
framework's name on it; it is also T7's seed (the representation-layer half of
identity-as-limit). Verify the exact `bisim` statement shape in the pinned
mathlib (relation-lifting formulation) and wrap it so downstream orders can
apply it without touching QPF internals. -/
theorem identity_by_unfolding : sorry := sorry
  -- Shape: ∀ (R : Ω₀ → Ω₀ → Prop), (bisimulation condition in G) → ∀ x y, R x y → x = y.
  -- Deliver whatever wrapper the mathlib API makes clean; the mapping table
  -- records the exact statement delivered.

/-- Spec 2.0 A5, realized: the universe contains an object that relates to
itself — ω̂, whose pattern is exactly its own self-relation. From Spec201c's
`pat_omegaHat` computation. The ledger's "theorem by Lambek" made concrete. -/
theorem self_relation_realized :
    ∃ (x : ZΩ.O) (r : ZΩ.R), r ∈ ZΩ.pat x ∧ ZΩ.endpoints r = s(x, x) := by
  sorry -- ⟨omegaHat, s(omegaHat, omegaHat), by rw [pat_omegaHat]; …, rfl⟩

```

## 4. T9 — canonicity

```lean
/-- Identity and composition of Raw homs (mirror Spec200's Shadow versions;
`Sym2.map_id`/`map_comp` and `Set.image_id`/`image_image` do the squares). -/
def Hom.idRaw (A : Raw) : Hom A A := sorry
def Hom.compRaw {A B C : Raw} (g : Hom B C) (f : Hom A B) : Hom A C := sorry

/-- Spec 2.0 T9 (Canonicity) / D12's mathematical content: any two bounded-final
Raws are isomorphic — the universe is characterized by its universal property,
independently of every encoding choice. THE ATOMS BELONG TO THE MAP: QPF, the
polynomial, `Quot.out`, `Type 0` — all scaffolding; what is canonical is Ω
up to isomorphism. Proof: the two unique morphisms compose to unique
endomorphisms, which equal the identities (uniqueness at each final object
applied to itself — the `final_subsingleton` pattern from Spec200, upgraded). -/
theorem final_unique (Z Z' : Raw) (h : IsFinalBRaw Z) (h' : IsFinalBRaw Z') :
    ∃ (f : Hom Z Z') (g : Hom Z' Z),
      Hom.compRaw g f = Hom.idRaw Z ∧ Hom.compRaw f g = Hom.idRaw Z' := by
  sorry -- h'.2 Z h.1 gives f; h.2 Z' h'.1 gives g; uniqueness of Z → Z homs
        -- (h.2 Z h.1) identifies both composites with idRaw; Hom equality by
        -- cases/congr/proof-irrelevance as usual.
```

## 5. T5 — the closure of the closing (the day's hard one)

**Statement being built:** every object of Ω is matched *to every finite depth* by a finitely-realized object. Depth-n matching is the metric-free surrogate for density (it IS density in the canonical ultrametric, without needing T3's topology); "finitely realized" is ρ — the patterns that close in finitely many steps.

### 5.1 Machinery

```lean
/-- Relation lifting through unordered pairs. (Check whether the pinned mathlib
has a `Sym2` relator; if not, this hand-rolled form is fine.) -/
def Sym2Lift (R : α → β → Prop) (p : Sym2 α) (q : Sym2 β) : Prop :=
  ∃ a b c d, p = s(a, b) ∧ q = s(c, d) ∧ ((R a c ∧ R b d) ∨ (R a d ∧ R b c))

/-- Egli–Milner-style lifting to sets: everything matches something, both ways. -/
def SetLift (R : α → β → Prop) (S : Set α) (T : Set β) : Prop :=
  (∀ p ∈ S, ∃ q ∈ T, R p q) ∧ (∀ q ∈ T, ∃ p ∈ S, R p q)

/-- Depth-n behavioural equivalence on Ω₀: agreement of unfoldings to depth n.
d(x, y) ≤ 2⁻ⁿ, without the metric. -/
def EqDepth : ℕ → Ω₀ → Ω₀ → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun x y => SetLift (Sym2Lift (EqDepth n)) (ZΩ.pat x) (ZΩ.pat y)

/-- Spec 2.0 §7 / T5: ρ — the finitely-realized objects: images of finite
bounded descriptions. "The patterns that close in finitely many steps." -/
def FinitelyRealized (x : Ω₀) : Prop :=
  ∃ (A : Raw), Bounded A ∧ Finite A.O ∧ Finite A.R ∧
    ∃ (h : Hom A ZΩ) (a : A.O), h.fO a = x
```

Basic lemmas to bank first: `EqDepth` is reflexive at every n (induction; `Sym2Lift` reflexivity by `Sym2.ind`); `omegaHat ∈ ρ` (witness: the one-point Raw from `Spec201c`'s `omegaHat` construction, packaged — this also gives ρ ≠ ∅ and a smoke test of `FinitelyRealized`'s shape).

### 5.2 Reachability is finite (the enabling lemma)

```lean
/-- Depth-bounded reachable set: D 0 = {x}; D (k+1) adds all endpoints of all
relations of members. Finite at every depth: patterns are finite (bounded_ZΩ)
and each Sym2 contributes at most two endpoints. -/
def reach (x : Ω₀) : ℕ → Set Ω₀ := sorry

theorem reach_finite (x : Ω₀) (k : ℕ) : (reach x k).Finite := by
  sorry -- induction; finite union over a finite pattern of the (≤2)-element
        -- endpoint sets (`Sym2` membership sets are finite — prove the tiny
        -- lemma `(setOf (· ∈ (p : Sym2 α))).Finite` by `Sym2.ind` if mathlib
        -- lacks it).

theorem reach_mono_step (x : Ω₀) (k : ℕ) :
    ∀ z ∈ reach x k, ∀ r ∈ ZΩ.pat z, ∀ w ∈ ZΩ.endpoints r, w ∈ reach x (k + 1) := sorry
```

### 5.3 The truncation and the assembly

Blueprint (design freedom granted within the stated invariant):

- **Carrier.** `T_O := {p : Ω₀ × Fin (n + 1) // p.1 ∈ reach x (n - p.2.val)}` — an object tagged with *remaining fidelity* k, constrained to be reachable within the budget already spent. Finite: subtype of (finite `reach x n` superset — note `reach` is monotone in depth, prove or inline) × `Fin`.
- **Relations & endpoints.** Mimic ZΩ: `T_R := Sym2 T_O`, `endpoints := id`.
- **Pattern.** At `(z, k)` with `k = 0`: the self-loop singleton `{s((z,0),(z,0))}` (nonemptiness preserved — the truncation *closes with loops*, which is the philosophically resonant move: finite realization ends not in atoms but in self-relation, exactly as the framework's regress always closes). At `k + 1`: the image of `ZΩ.pat z` tagging endpoints with `k` — membership proofs supplied by `reach_mono_step`.
- **The invariant to prove** (by induction on the remaining fidelity): the unique/corec-style hom `h : T → ZΩ` (or a directly-constructed one — you may define `h.fO (z, k) := z`-composed-with-inclusion **only if** you verify it is a Hom; more likely you construct h by hand and verify squares, or route through `isFinalBRaw_ZΩ` applied to T) satisfies **`EqDepth k z (h.fO (z, k))` for every state**. Instantiate at `(x, n)`.

```lean
/-- Spec 2.0 T5 — THE CLOSURE OF THE CLOSING. Every object of Ω is matched to
every finite depth by a finitely-realized object: the universe is the closure
of the patterns that close. The truncation closes its leaves with self-loops —
finite realization bottoms out not in atoms but in self-relation. -/
theorem closing_dense (x : Ω₀) (n : ℕ) :
    ∃ y : Ω₀, FinitelyRealized y ∧ EqDepth n x y := by
  sorry
```

**Drop-clause (honest, pre-authorized):** if the assembly (5.3) exceeds ~1.5 focused days after 5.1–5.2 are banked, deliver 5.1 + 5.2 + the truncation *definition* + `closing_dense` stated with its proof stubbed OUT of the file (moved verbatim into the PR description as the recorded plan — the file itself stays `sorry`-free), label T5 `[machinery proved; assembly deferred]`, and stop. The EqDepth/ρ machinery is independently load-bearing for T4 and T7 and is not wasted either way. What is NOT authorized: weakening `EqDepth`, restricting to `omegaHat`-like special cases, or proving a strictly easier statement under T5's name.

## 6. T10s — genesis, anchored

```lean
/-- One generative step: y arises within x's unfolding (occurs at some endpoint
of x's pattern) — the orbit-growing relation for D13(3). -/
def Arises (y x : Ω₀) : Prop := Desc ZΩ y x

/-- The orbit of the self-loop: everything reachable from ω̂ by finite unfolding. -/
def omegaOrbit : Set Ω₀ := { y | Relation.ReflTransGen (fun a b => Arises a b) y omegaHat }
  -- mind the argument order of ReflTransGen vs. the direction you intend;
  -- state it so `omegaHat ∈ omegaOrbit` is the `refl` case, and prove that
  -- one-liner as the sanity check.

/-- Spec 2.0 T10 / D13(3) — GENESIS, the named conjecture: does all multiplicity
unfold from self-meeting? Stated as depth-density of ω̂'s orbit (the metric-free
form matching T5's). OPEN IN TRUTH-VALUE: this declaration is an anchor, not a
claim — proof or refutation is future work, and per D13 the framework brings no
perspective where a proof can be had. -/
def Genesis : Prop :=
  ∀ x : Ω₀, ∀ n : ℕ, ∃ y ∈ omegaOrbit, EqDepth n x y
```

Note for the doc-comment: with T5 in hand, Genesis reduces to whether the *finitely-realized* objects are orbit-approximable — a genuinely open combinatorial question about which finite loop-closed shapes ω̂'s unfolding reaches. Do not attempt it; record the reduction observation in the comment (it sharpens the conjecture for whoever takes it up).

## 7. Spec housekeeping (MUST)

In `2-0.md` §5:
- T6 → `[proved (Spec201d): descent serial in every Raw; not well-founded on any inhabited Raw; instantiated at ZΩ; chains at every depth]`.
- T9 → `[proved (Spec201d): any two bounded-final Raws isomorphic — canonicity; the atoms belong to the map]`.
- T5 → per outcome: `[proved (Spec201d): every object depth-n matched by a finitely-realized one; truncation closes with self-loops]` or the drop-clause label.
- T10 → append `— formally anchored (Spec201d: Genesis, omegaOrbit); open in truth-value; reduction to orbit-approximability of ρ noted.`
- A4 ledger row → append `— coinduction principle realized (identity_by_unfolding, Spec201d)`; A5 row → append `— realized at ZΩ (self_relation_realized)`.

In `2-2.md` §7: this order delivered; remaining Series-2 theorem work: the S1 pigeonhole order, then T4 (profiles — now with EqDepth in hand), then T7.

---

*End of work order. T6 is the regress objection's tombstone: machine-checked, becoming has no first brick, and the descent that critics called vicious is serial, ordinary, and provably harmless. T5's truncation carries the order's grace note — finite realizations close their leaves with self-loops, so even the approximations end in turning rather than in atoms. Write the file so a philosopher can find `no_constitutive_origin` and `closing_dense` and understand: the universe has no floor, and it is everywhere within reach of things that close.*
