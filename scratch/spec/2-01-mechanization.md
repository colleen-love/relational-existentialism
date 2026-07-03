# 2.01-mechanization — Work Order: Signature, Enlargement, the C3 Split, and L1

**This document describes:** `scratch/formal/Spec201.lean`
**Normative sources:** `scratch/spec/2-00.md` (ontology) and `scratch/spec/2-01.md` (signature and definitions). Where this document and the specs disagree, the specs win; report the discrepancy rather than improvising.
**Audience:** Claude Code, executing without further human clarification. Follow closely; do not expand scope.
**Relation to prior work:** `Spec200.lean` stays untouched and remains valid — its Arena interface and proofs (T1, P0, P1s, P2, P3) are not superseded. `Spec201.lean` is a new file realizing the *two-sorted* signature of spec 2-01, which is the Arena's successor.

---

## 1. Purpose and scope

| ID | Name | Priority |
|----|------|----------|
| SIG | The two-sorted signature (`Model`, plus raw coalgebras and homs) | MUST |
| P4s | Enlargement, static form ("to be observed is to be enlarged") | MUST |
| PRJa | External join totality (representation-layer toy lemma) | MUST |
| C3-split | The self-anchored case split, **stated before any properness proof** | MUST |
| C3-gen | Generic-case properness theorem | MUST |
| C3-refl | Reflexive-case counterexample (properness not forced at self-anchored loops) | MUST |
| L1-quot | Coherence preserved along surjective homs | MUST |
| L1-sub | Coherence reflected along injective homs | MUST |
| L1-sum | Coherence preserved under binary coproducts | SHOULD |

**Out of scope — do not attempt** (§7 has the full list): T2/`MvQPF.Cofix`, the dyad construction (P5), T13, general P1, T4, the weak-pullback check, anything about κ or scarcity.

**Why these matter (for your doc-comments):** P4s formalizes "every eye that meets mine shapes me" — observation constitutes the observed, and the proof should be nearly nothing *because* the coherence field of the signature IS the co-requirement. The C3 pair is the delicate one: spec 2-01 §5 conjectures that A8(i) — the framework's ONLY axiom — is *derivable* except at self-referential attendings. Your job is to establish the split at interface level: prove properness in the generic case, and exhibit a concrete model where the self-anchored case saturates (properness not forced). This does NOT prove A8(i) false anywhere; it locates exactly where the axiom does irreducible work. Spec 2-00 D15 (pre-registration) applies with full force: this outcome is *wanted*, so the file must be structured so the case split is stated before any properness result, and the counterexample must be presented with a scrupulous doc-comment saying what it does and does not show. L1 discharges the lemma obligation from 2-01 §4's literature-verified construction: coherent coalgebras form a covariety, which is what makes Ω = greatest coherent subcoalgebra of νF legitimate.

---

## 2. Environment and conventions

Identical to `2-00-mechanization.md` §2, with these additions/changes:

- **New file** `scratch/formal/Spec201.lean`, registered alongside `Spec200` in the Lake config the same way `Spec200` was registered (second library root pattern; follow the precedent in the repo, and record any path deviation in the mapping table as before).
- **Imports:** `Mathlib.Data.Sym.Sym2` is needed (unordered pairs) in addition to the set-theory basics. `Sym2 α` is mathlib's quotient of `α × α` by swap; membership is `Sym2.Mem` (`x ∈ s` works), the functorial action is `Sym2.map`, and the key lemma is `Sym2.mem_map` (verify exact name with `exact?` if it has drifted). Diagonal pairs `s(x, x)` exist — self-relation is representable, which the framework requires (A5).
- **No `sorry`, no new axioms**; `#print axioms` audit on every theorem; doc-comments carry spec IDs from **2-00.md and 2-01.md** (note the new hyphenated filenames).
- Namespace: `RelEx.TwoSorted`.

---

## 3. Part A — the signature and interface-level results

### 3.1 The Model structure

```lean
namespace RelEx
namespace TwoSorted

/-- Spec 2-01 §2: the two-sorted signature, interface form. Two sorts (objects `O`,
relations `R`); unordered endpoints (no slots, 2-00 D6; `Sym2` permits diagonal
pairs, so self-relation A5 is representable); patterns as nonempty sets of
relations, with sharing as ordinary set membership (2-00 D3: one relation, two
containers, numerical identity for free); endpoint coherence as a field —
which IS proposition P3 and, as P4s will show, the co-requirement.
`dy` (dyad anchor) is taken as DATA at this interface: its construction from
`close` is P5 (spec 2-01 §3.1), deferred; no axioms govern it here, and results
below are interface-relative in the same sense as Spec200's Arena results. -/
structure Model where
  O : Type u
  R : Type u
  endpoints : R → Sym2 O
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty
  coherent : ∀ (r : R) (x : O), x ∈ endpoints r → r ∈ pat x
  dy : R → O

variable (M : Model)

/-- Spec 2-01 §3.2: the context of `r` in `x` — the relations in `x`'s pattern in
which `r`'s dyad participates. The aperture of `x` at `r` IS this set. -/
def ctx (x : M.O) (r : M.R) : Set M.R :=
  { s ∈ M.pat x | M.dy r ∈ M.endpoints s }
```

Note: `ctx x r ⊆ M.pat x` holds definitionally (it is a separation subset); you will want the one-line lemma `ctx_subset : M.ctx x r ⊆ M.pat x` for reuse.

### 3.2 P4 static

```lean
/-- Spec 2-00 §2.3 / 2-01 §5, P4 (static form): to be observed is to be enlarged.
Any relation through which `y` is observed — any relation with `y` among its
endpoints — is a part of `y`. The proof is the coherence field applied: this
brevity is the exhibit, not padding. Observation constitutes the observed
because relations are parts of their endpoints BY SIGNATURE; the critic's
reading is a part of the art. Static form only: the coming-into-being of new
relations is Series 3 (2-00 O9). -/
theorem P4_static (r : M.R) (y : M.O) (hy : y ∈ M.endpoints r) : r ∈ M.pat y :=
  M.coherent r y hy
```

### 3.3 PR-J(a)

```lean
/-- Spec 2-00 §3, PR-J(a): at the representation layer, proper subsets can union
to the whole. Exists to make PR-J(b)'s contrast exact: EXTERNALLY, totality of
attention is cheap; the framework's question (PR-J(b), via C3 below) is whether
any DEPLOYABLE attention is ever total. Pre-registered pair per 2-00 D15. -/
example : ∃ A B : Set (Fin 2), A ⊂ Set.univ ∧ B ⊂ Set.univ ∧ A ∪ B = Set.univ := by
  sorry -- use A = {0}, B = {1}; ssubset via the missing element; union by decide/ext
```

(Promote from `example` to a named `theorem PRJ_a` so the mapping table can point at it.)

### 3.4 The C3 split — ORDER OF DECLARATIONS IS NORMATIVE

Per 2-00 D15, the split is **defined first**, then the generic theorem, then the counterexample. Do not reorder.

```lean
/-- Spec 2-01 §5 (C3): the case split. An attending of `x` along `r` is
SELF-ANCHORED when `r`'s own dyad is among `r`'s endpoints — the relation
participates in its own context; the lens appears in its own field of view.
This is the split on which the derivability of A8(i) turns, and per 2-00 D15
it is stated before any properness result in this file. -/
def SelfAnchored (r : M.R) : Prop := M.dy r ∈ M.endpoints r

/-- Spec 2-01 §5 (C3, generic case): OFF the self-anchored locus, properness is a
THEOREM — the aperture always omits the very relation being attended, because
that relation's dyad is not among its own endpoints. You cannot fully witness
the lens you are looking through. Consequences: PR-J(b) holds for generic
attendings, and A8(i)'s content is derived rather than assumed there. -/
theorem generic_properness (r : M.R) (x : M.O)
    (hr : r ∈ M.pat x) (h : ¬ M.SelfAnchored r) :
    M.ctx x r ⊂ M.pat x := by
  sorry
```

Proof plan for `generic_properness`: `ctx_subset` gives `⊆`; for strictness exhibit `r` itself — `r ∈ M.pat x` by `hr`, but `r ∉ M.ctx x r` because membership would require `M.dy r ∈ M.endpoints r`, contradicting `h`. Package as `ssubset_iff_of_subset` or `Set.ssubset_iff_exists` (find the exact mathlib spelling with `exact?`; the mathematical content is the two lines above).

```lean
/-- Spec 2-01 §5 (C3, reflexive case): properness is NOT FORCED on the
self-anchored locus. Witness: the one-object, one-relation universe — the
self-loop, the framework's ω̂ — where the sole relation is its own dyad's
self-relation and the context of the attending saturates the entire pattern.

WHAT THIS SHOWS: the interface does not derive A8(i) at self-anchored
attendings; if lossiness holds there, it holds by AXIOM. A8(i)'s irreducible
content is located exactly at self-reference.
WHAT THIS DOES NOT SHOW: that A8(i) is false there. A richer signature (2-01's
full Ω, witnessing structure) may yet derive it, or refute it — either outcome
requires the machinery this file does not build. Per 2-00 D15, this comment is
the required hostile write-up: the project WANTS C3 true twice over (it would
shrink the last axiom and prove PR-J(b) at once), so the reflexive case is
reported at full strength, not softened. -/
theorem reflexive_saturation :
    ∃ (M : Model) (r : M.R) (x : M.O),
      M.SelfAnchored r ∧ r ∈ M.pat x ∧ M.ctx x r = M.pat x := by
  sorry
```

Construction plan for `reflexive_saturation`: take `O := PUnit`, `R := PUnit`, `endpoints _ := s(PUnit.unit, PUnit.unit)` (the diagonal), `pat _ := Set.univ` (nonempty via `⟨PUnit.unit, trivial⟩`), `dy _ := PUnit.unit`. Then `SelfAnchored` holds by `Sym2.mem_iff`-style computation on the diagonal pair; `ctx` unfolds to the whole of `pat` because the defining condition holds for the unique `s`. Expect the proof to be `Set.ext` plus `simp [ctx, SelfAnchored]` with small nudges. Note the resonance for the doc-comment: the saturating witness is exactly the self-loop universe of T1 — the One is the place where attention can span everything, and where lossiness must be legislated rather than derived.

---

## 4. Part B — L1: the covariety closures

These discharge the lemma obligation in spec 2-01 §4 (step 2 of the literature-verified construction). They are about **raw** two-sorted coalgebra models — coherence must be a `Prop` about them, not a bundled field — so a second, unbundled structure is needed. Do not refactor `Model`; the two structures serve different purposes (interface results vs. covariety lemmas) and a `Raw.toModel` bridge is not required in this work order.

```lean
/-- A raw two-sorted model: as `Model` but with coherence NOT bundled —
coherence is the property whose closure behavior L1 establishes. -/
structure Raw where
  O : Type u
  R : Type u
  endpoints : R → Sym2 O
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty

/-- Spec 2-01 §2/§4: endpoint coherence as a property of raw models. -/
def Coherent (A : Raw) : Prop :=
  ∀ (r : A.R) (x : A.O), x ∈ A.endpoints r → r ∈ A.pat x

/-- A homomorphism of raw models: sort maps commuting with endpoints (via
`Sym2.map`) and with patterns (via image — the powerset functor's action,
so equality, not mere inclusion). -/
structure Hom (A B : Raw) where
  fO : A.O → B.O
  fR : A.R → B.R
  end_comm : ∀ r, B.endpoints (fR r) = (A.endpoints r).map fO
  pat_comm : ∀ x, B.pat (fO x) = fR '' A.pat x
```

```lean
/-- Spec 2-01 §4, L1 (quotients): coherence is preserved along surjective homs.
One of the three closures making coherent coalgebras a covariety, hence making
Ω = greatest coherent subcoalgebra of νF legitimate. -/
theorem coherent_of_surjective_hom {A B : Raw} (h : Hom A B)
    (hO : Function.Surjective h.fO) (hR : Function.Surjective h.fR)
    (hA : Coherent A) : Coherent B := by
  sorry

/-- Spec 2-01 §4, L1 (subcoalgebras): coherence is reflected along injective homs. -/
theorem coherent_of_injective_hom {A B : Raw} (h : Hom A B)
    (hR : Function.Injective h.fR)
    (hB : Coherent B) : Coherent A := by
  sorry
```

Proof plans.
- *Quotients:* given `r' : B.R`, `x' ∈ B.endpoints r'`: obtain `r` with `h.fR r = r'` (surjectivity — note only `hR` is essential; if `hO` turns out unnecessary, drop it and record the strengthening in the mapping table). Rewrite `x' ∈ B.endpoints (h.fR r)` via `end_comm` and `Sym2.mem_map` to get `x` with `x ∈ A.endpoints r` and `h.fO x = x'`. Coherence of A: `r ∈ A.pat x`. Then `r' = h.fR r ∈ h.fR '' A.pat x = B.pat (h.fO x) = B.pat x'` via `pat_comm`.
- *Subcoalgebras:* given `r : A.R`, `x ∈ A.endpoints r`: then `h.fO x ∈ B.endpoints (h.fR r)` via `end_comm` + `Sym2.mem_map` (forward direction); coherence of B gives `h.fR r ∈ B.pat (h.fO x) = h.fR '' A.pat x`; injectivity of `fR` extracts `r ∈ A.pat x`.

**L1-sum (SHOULD, drop after ~1 hour):** define the binary coproduct of raw models (`O := A.O ⊕ B.O`, `R := A.R ⊕ B.R`, endpoints via `Sym2.map Sum.inl` / `Sym2.map Sum.inr`, patterns via images under the injections) and prove coherence is preserved. If `Sym2`/`Sum` plumbing gets heavy, drop and note — the sum closure is the least load-bearing of the three (the quotient and subcoalgebra closures carry the finality argument's weight).

---

## 5. What NOT to prove about C3

Three tempting overreaches, all forbidden:

1. **Do not add a properness axiom to `Model` to "complete" the picture.** The whole point is to see what the signature forces without A8(i). The axiom's formal placement is a 2-01/2-02 design decision, not yours.
2. **Do not prove `generic_properness` by adding hypotheses** (e.g., finiteness, extra structure on `dy`). If the theorem as stated fails to close, that is a *finding* — stop and report per §6.2 of the previous work order's rules, which remain in force.
3. **Do not conclude anything about A8(i)'s truth at loops.** `reflexive_saturation` shows non-derivability at this interface, nothing more. The doc-comment provided above is normative; keep its "WHAT THIS DOES NOT SHOW" block intact.

---

## 6. Build, verify, deliver

1. `lake build` clean; `grep -rn "sorry" scratch/formal/Spec201.lean` empty.
2. `#print axioms` on: `P4_static`, `PRJ_a`, `generic_properness`, `reflexive_saturation`, `coherent_of_surjective_hom`, `coherent_of_injective_hom` (+ `coherent_sum` if attempted). Baseline only (`propext`, `Classical.choice`, `Quot.sound`); several of these should be axiom-free — report what you see.
3. Declaration order in the file: `Model` → `ctx` → `P4_static` → `PRJ_a` → `SelfAnchored` → `generic_properness` → `reflexive_saturation` → Part B. The `SelfAnchored`-before-properness order is normative (D15).
4. Doc-comments per the templates above; every one carries its spec ID against 2-00.md / 2-01.md.
5. Mapping table at file foot:

```
-- Specs 2-00 / 2-01 ↔ scratch/formal/Spec201.lean
-- P4 (static)        = RelEx.TwoSorted.P4_static
-- PR-J(a)            = RelEx.TwoSorted.PRJ_a
-- C3 split           = RelEx.TwoSorted.SelfAnchored (definition; order normative)
-- C3 (generic)       = RelEx.TwoSorted.generic_properness
-- C3 (reflexive)     = RelEx.TwoSorted.reflexive_saturation (counterexample)
-- L1 (quotient)      = RelEx.TwoSorted.coherent_of_surjective_hom
-- L1 (subcoalgebra)  = RelEx.TwoSorted.coherent_of_injective_hom
-- L1 (sum)           = RelEx.TwoSorted.coherent_sum        (SHOULD; may be absent)
-- Deviations from 2-01-mechanization.md: <list here, or "none">
```

## 7. Out of scope — do not attempt

- **T2 / `MvQPF.Cofix` / any finality construction** — next work order, after L1 lands and the MvQPF encoding of `P⁺` and `Sym2` is planned on paper.
- **P5 (dyad construction)** — `dy` is data here; constructing it needs `close`, which needs T2.
- **T13, general P1, T4** — need witnessing structure not defined in this order.
- **The weak-pullback check** — categorical background hypothesis; separate small task.
- **κ-boundedness anywhere** — `Set R` unbounded is fine at this interface; κ is existence scaffolding (2-01 D4) and none of these results touch existence.
- **Modifying `Spec200.lean`** or the 2-00 mapping table.

If an unblocked-looking lemma outside this list presents itself, note it in the PR description; do not prove it.

---

*End of work order. The C3 pair is the heart: one theorem, one counterexample, and the framework's last axiom gets a precise address. Write the file so a philosopher with no Lean can find `SelfAnchored`, read three doc-comments in order, and understand that lossiness has been derived everywhere except where the lens turns on itself — and that exactly there, it must be chosen.*
