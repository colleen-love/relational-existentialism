# 2.2-mechanization-a — Work Order: Reveal, Internal, and the C1 Conditional

**This document describes:** `series-2/formal/Spec202.lean` (new file; imports `Spec201`, `Spec201b`)
**Normative sources:** `series-2/2-0.md` (current revision, with D17/D18 and the R3-revised D9), `series-2/2-1.md`, and `series-2/2-2.md`. Where this document and the specs disagree, the specs win; report, don't improvise.
**Audience:** Claude Code, executing without further clarification. All prior conventions in force (no `sorry`, no new axioms, `#print axioms` audit, doc-comments with spec IDs, mapping table, deviations recorded, Lake root registration per precedent).

---

## 1. Purpose and scope

Series 2's design questions are closed (R1: π as sub-pattern; R2: threefold witnessing; R3: scarcity as self-insufficiency). This order mechanizes everything those rulings made design-ready. The star is **C1c**, the conditional form of "no windowless monads": *in a connected universe with no total object, every object has a boundary* — the theorem that makes the fish ruling and the monad conjecture provably one fact, and puts "we are born as bridges" two discharged hypotheses away from unconditional.

| ID | Name | Priority |
|----|------|----------|
| RVL | `Reveal` + basic lemmas + containers-co-attend | MUST |
| P1b2 | Barrier two, existence form: reveals differ across a shared relation | MUST |
| T13b | Hearsay bounds: acquaintance bound + received-can-be-proper witness | MUST |
| INT | `Internal`, `Windowless`, `holdDepth` + basic lemmas | MUST |
| **C1c** | **The conditional: connected + no-total ⟹ no windowless** | **MUST** |
| T14a | `piPart` + iff-lemmas tying it to `ContainedIn`/`Touches`; preorder lemmas | MUST |
| T14b | Antisymmetry-failure witness (with the T7-entanglement doc-comment) | MUST |
| T14c | MutualPartial corner witness (musicianship) | MUST |
| T14d | Comparative fish/partner witness (π(me→fish) ⊂ π(me→partner) within me) | SHOULD |
| DOC | Spec status-label housekeeping (§7) | MUST |

**Out of scope — do not attempt:** the S1 pigeonhole (staged next, after this order's `Internal`/`holdDepth` land and 2.2 §6's conjecture statement is refined against them); νF existence / `MvQPF`; T4's profile machinery; C2 about Ω; anything temporal. If an unblocked-looking lemma appears, note it in the PR; do not prove it.

---

## 2. Part A — Reveal (RVL, P1b2, T13b)

```lean
/-- Spec 2.2 §3 (R2 formalized): the canonical payload of an attending — the
relation together with its bearing-structure in the observer. Threefold reading
(2.0 D17): (i) the relation; (ii) the self, clarified — `ctx` IS the observer's
own bearings, so self-knowledge is the medium of the act, not a side effect;
(iii) the world through oneself — shared members of the aperture open hearsay
channels. Introspective by construction: the payload is a sub-pattern of the
observer. What Reveal deliberately does NOT contain: any element of
`pat y \\ pat x` — the barriers of 2.0 §2.4 are structural, not assumed. -/
def Reveal (M : Model) (x : M.O) (r : M.R) : Set M.R :=
  insert r (ctx M x r)

theorem reveal_subset (M : Model) (x : M.O) (r : M.R) (hr : r ∈ M.pat x) :
    Reveal M x r ⊆ M.pat x := by
  sorry -- insert_subset: hr for r; ctx_subset (Spec201) for the rest

theorem mem_reveal_self (M : Model) (x : M.O) (r : M.R) : r ∈ Reveal M x r := by
  sorry -- Set.mem_insert

/-- Spec 2.0 D17, containers co-attend (static form): a bearing shared into a
container `w` is payload-material for `w` wherever it is payload for `x` — one
act of attention deposits aperture-material in every containing whole. The
formal home of "I learn about myself and all of the things that contain me
through our relation"; per-act restatement of T12's flow. -/
theorem containers_co_attend (M : Model) (x w : M.O) (r s : M.R)
    (hs : s ∈ ctx M x r) (hw : s ∈ M.pat w) :
    s ∈ Reveal M x r ∩ M.pat w := by
  sorry -- ⟨mem_insert_of_mem _ hs, hw⟩

/-- Spec 2.2 §3 / general P1, barrier two (existence form): one shared relation,
two different payloads. What each side receives of the SAME relation is assembled
from its OWN context — `boolWitness` already carries the difference (its private
bearing sits in x's payload and cannot sit in y's). The general form — no chain
of x's attendings ever assembles y's pattern AS y's — awaits T4's profile
machinery; this witness establishes that the barrier is real, not vacuous. -/
theorem reveals_differ :
    ∃ (M : Model.{0}) (r : M.R) (x y : M.O),
      r ∈ M.pat x ∧ r ∈ M.pat y ∧ Reveal M x r ≠ Reveal M y r := by
  sorry -- boolWitness, r := true, x := true, y := false; the private bearing
        -- `false` is in Reveal true but Reveal false ⊆ pat false = {true}

/-- Spec 2.2 §3, T13 hearsay bounds. What arrives from `z` through the shared
`s` is `received := Reveal x r ∩ Reveal z s`. The ACQUAINTANCE BOUND is the
left projection: nothing arrives beyond x's own payload on the shared boundary.
The right projection bounds it by z's assembly. "Some of what you attend to":
generically proper in both — witnessed below. -/
def received (M : Model) (x z : M.O) (r s : M.R) : Set M.R :=
  Reveal M x r ∩ Reveal M z s

theorem received_acquaintance_bound (M : Model) (x z : M.O) (r s : M.R) :
    received M x z r s ⊆ Reveal M x r := Set.inter_subset_left

theorem received_source_bound (M : Model) (x z : M.O) (r s : M.R) :
    received M x z r s ⊆ Reveal M z s := Set.inter_subset_right

theorem received_can_be_proper :
    ∃ (M : Model.{0}) (x z : M.O) (r s : M.R),
      received M x z r s ⊂ Reveal M z s := by
  sorry -- boolWitness again: x := false, z := true, r := s := true (the shared
        -- relation); z's payload holds the private bearing, x's cannot receive it
```

If the term-mode one-liners compile as one-liners, keep them so — brevity remains the exhibit where the signature does the work.

## 3. Part B — Internal, holdDepth, and the C1 conditional

```lean
/-- Spec 2.2 §4: the internal part of a pattern — relations all of whose
endpoints the object contains (pattern-inclusion, the ratified parthood). The
complement within `pat x` is x's BOUNDARY: the relating that crosses to what x
does not contain. -/
def Internal (M : Model) (x : M.O) : Set M.R :=
  { r ∈ M.pat x | ∀ z ∈ M.endpoints r, ContainedIn M z x }

theorem internal_subset (M : Model) (x : M.O) : Internal M x ⊆ M.pat x :=
  fun _ h => h.1

/-- A windowless object: no boundary at all — every relation held entirely
among contained parts. C1 conjectures these impossible; C1c below proves it
conditionally. -/
def Windowless (M : Model) (x : M.O) : Prop := Internal M x = M.pat x

/-- Spec 2.2 §6 (R3): the depth of x's hold on r — the internalized part of
the aperture. Scarcity's measure: attention is as rich as its neighborhood is
woven in, and never total because closure never completes. Growth, healing,
and T12's flow are movements along this gradient. -/
def holdDepth (M : Model) (x : M.O) (r : M.R) : Set M.R :=
  { s ∈ ctx M x r | ∀ z ∈ M.endpoints s, ContainedIn M z x }

theorem holdDepth_subset_ctx (M : Model) (x : M.O) (r : M.R) :
    holdDepth M x r ⊆ ctx M x r := fun _ h => h.1
```

### C1c — the star

```lean
/-- A total object: one whose pattern is everything. T16 conjectures none exist;
here totality is a hypothesis to be discharged there. -/
def Total (M : Model) (x : M.O) : Prop := M.pat x = Set.univ

/-- Spec 2.2 §6 / 2.0 C1 — THE C1 CONDITIONAL. In a connected universe with no
total object, there are no windowless objects: every object is open to otherness.
Proof shape: windowlessness propagates containment along connection — if x is
windowless, any object reachable from x has its pattern inside x's (each step's
relation is in x's pattern by coherence + the inductive containment, so its far
endpoint is contained by windowlessness); connectivity then reaches every object,
every relation lands in `pat x` through its endpoints, and x is total. You cannot
seal yourself off in a universe where everything touches: the fish ruling and the
monad conjecture are ONE FACT. Hypotheses discharge at C2 (connectivity of Ω)
and T16 (no total object); with them, "we are born as bridges" goes
unconditional. -/
theorem no_windowless_of_connected_of_no_total (M : Model)
    (hconn : Connected M.toRaw)
    (hnt : ∀ z : M.O, ¬ Total M z) :
    ∀ x : M.O, ¬ Windowless M x := by
  sorry
```

Proof plan (follow in order; this is the one proof in the order with real length):

1. `intro x hw`; aim for `hnt x` via `Total M x`, i.e. `M.pat x = Set.univ`, via `Set.eq_univ_of_forall`.
2. **Containment invariant.** Prove the auxiliary: `∀ y, Relation.ReflTransGen (StepR M.toRaw) x y → M.pat y ⊆ M.pat x`, by `Relation.ReflTransGen` induction (the `tail` recursor pattern from `coprod_disconnected` is the template).
   - `refl`: `subset_rfl`.
   - `tail` (step p → q via relation r'): from IH `M.pat p ⊆ M.pat x`. The step gives `p ∈ M.endpoints r'` and `q ∈ M.endpoints r'` (unfold `StepR`; note `M.toRaw` leaves `endpoints`/`pat` definitionally intact — a `show`/`change` may be needed to cross the `toRaw` boundary; if it fights, add a one-line simp lemma `toRaw_pat : M.toRaw.pat = M.pat` and its endpoints twin).
   - Coherence: `r' ∈ M.pat p`, hence `r' ∈ M.pat x` by IH.
   - Windowlessness of x: `r' ∈ Internal M x` (rewrite `hw`), so its endpoint `q` has `ContainedIn M q x`, i.e. `M.pat q ⊆ M.pat x`. Done.
3. **Every relation lands.** For arbitrary `s : M.R`: obtain an endpoint `w` of `s` (every `Sym2` is inhabited — `Sym2.ind` on `M.endpoints s` to expose `s(a, b)` and take `a`, or use the `out`-style projections if this mathlib rev has them; verify with `exact?`). Coherence gives `s ∈ M.pat w`; `hconn x w` + the invariant gives `M.pat w ⊆ M.pat x`; so `s ∈ M.pat x`.
4. Conclude `Total M x`, contradict `hnt x`.

**Do not weaken the statement** (e.g., to finite models or decidable equality) to make the proof close; if it resists as stated, stop and report — that would be a finding about the definitions, which is exactly what this order exists to surface.

## 4. Part C — T14: the comparative laws and witnesses

```lean
/-- Spec 2.2 §1 (R1): π ratified — the shared part AS A SUB-PATTERN OF THE
OBSERVER. Not a number: the same underlying set serves both directions; direction
is the embedding (same part, different wholes — the sharing doctrine at the
mereological level); comparison is inclusion within one observer, A3-local by
type. Numeric proportions are representation-layer shorthand only. -/
def piPart (M : Model) (x y : M.O) : Set M.R := M.pat x ∩ M.pat y

theorem piPart_comm_set (M : Model) (x y : M.O) :
    piPart M x y = piPart M y x := Set.inter_comm _ _
  -- doc-comment: one part, two embeddings — the asymmetry of π(x→y) vs π(y→x)
  -- lives in whose pattern it is weighed within, not in the set.

theorem containedIn_iff_piPart (M : Model) (x y : M.O) :
    ContainedIn M x y ↔ piPart M x y = M.pat x := by sorry
theorem touches_iff_piPart (M : Model) (x y : M.O) :
    Touches M x y ↔ (piPart M x y).Nonempty := Iff.rfl -- or by rfl/unfold

theorem containedIn_refl (M : Model) (x : M.O) : ContainedIn M x x := subset_rfl
theorem containedIn_trans (M : Model) {x y z : M.O}
    (h₁ : ContainedIn M x y) (h₂ : ContainedIn M y z) : ContainedIn M x z :=
  h₁.trans h₂

/-- Spec 2.2 §5: ANTISYMMETRY FAILS at the interface — two distinct objects with
identical patterns. Doc-comment must carry the T7 entanglement: whether
pattern-equality forces identity is exactly T7's question in mereological clothes
(in Ω, bisimilarity may identify these; interface models need not). Witness: two
objects, one self... one relation between them, both patterns the whole. -/
theorem containedIn_antisymm_fails :
    ∃ (M : Model.{0}) (x y : M.O),
      x ≠ y ∧ ContainedIn M x y ∧ ContainedIn M y x := by
  sorry -- O := Bool, R := PUnit, endpoints _ := s(true, false),
        -- pat _ := Set.univ, dy _ := true; coherence trivial; x := true, y := false

/-- Spec 2.0 §2.5, the musicianship corner: mutual partiality — each holds a
private relation, they share one. Also serves as the qualitative fish corner
(touching without containment); the fish/musicianship DISTINCTION is comparative
(T14d), not qualitative. -/
theorem mutualPartial_witness :
    ∃ (M : Model.{0}) (x y : M.O), MutualPartial M x y := by
  sorry -- O := Bool; R := Fin 3: r0 shared s(x,y); r1 private-x s(x,x);
        -- r2 private-y s(y,y); pat x := {0,1}, pat y := {0,2}; dy _ := true;
        -- coherence by cases/decide
```

**T14d (SHOULD).** The comparative distinction: a three-object model (me, partner, fish) where `piPart me fish ⊂ piPart me partner` *as parts of me* — the fish's shared part low in my inclusion order. Suggested shape: O := Fin 3, R := Fin 3 (one relation to the partner plus a partner-side bearing shared richly, one thin relation to the fish); the doc-comment keeps the line: *a part of me, ever so slightly — one relation, and it is not nothing.* Budget ~1 hour; drop with a note if coherence bookkeeping balloons.

## 5. Build, verify, deliver

1. `lake build` clean; no `sorry`; no new warnings; axiom audit block on every named theorem (baseline only; note the choice-free ones).
2. Mapping table at file foot, per template below; deviations recorded.
3. Doc-comments: every declaration carries its spec ID; `no_windowless_of_connected_of_no_total`'s comment must include the discharge note (C2, T16) and the one-fact line.

```
-- Specs 2.0 / 2.1 / 2.2 ↔ series-2/formal/Spec202.lean
-- Reveal (R2)             = RelEx.TwoSorted.Reveal (+ reveal_subset, mem_reveal_self)
-- Containers co-attend    = RelEx.TwoSorted.containers_co_attend
-- P1 barrier two (exist.) = RelEx.TwoSorted.reveals_differ
-- T13 bounds              = RelEx.TwoSorted.received (+ *_bound, received_can_be_proper)
-- Internal / Windowless   = RelEx.TwoSorted.Internal, Windowless (+ internal_subset)
-- holdDepth (R3)          = RelEx.TwoSorted.holdDepth (+ holdDepth_subset_ctx)
-- C1 conditional (STAR)   = RelEx.TwoSorted.no_windowless_of_connected_of_no_total (+ Total)
-- π ratified (R1)         = RelEx.TwoSorted.piPart (+ piPart_comm_set, iff lemmas)
-- T14 preorder            = RelEx.TwoSorted.containedIn_refl/trans
-- T14 antisym failure     = RelEx.TwoSorted.containedIn_antisymm_fails
-- T14 corners             = RelEx.TwoSorted.mutualPartial_witness (+ T14d if present)
-- Deviations from 2-2-mechanization.md: <list, or "none">
```

## 6. What NOT to prove

1. **Do not attempt the S1 pigeonhole.** Its statement will be refined against this order's `holdDepth` before it is attempted; premature formalization risks baking in a weak form.
2. **Do not discharge C1c's hypotheses.** Connectivity of Ω is C2 (open); no-total is T16 (open). The conditional is the deliverable.
3. **Do not add hypotheses to C1c** to close the proof (per §3's warning).

## 7. Spec status-label housekeeping (MUST)

In `series-2/2-0.md` §5, after this order lands:
- C1: append `— conditional proved (Spec202): connected + no-total ⟹ no windowless.`
- T14: append `— comparative laws, π lemmas, antisymmetry-failure, and MutualPartial corner proved (Spec202)` (+ T14d if delivered).
- General P1: append `— barrier two existence form proved (Spec202): reveals differ across a shared relation.`
- T13: append `— acquaintance and source bounds + properness witness proved (Spec202); chain composition awaits T4.`
- T12: append `— containers-co-attend per-act form proved (Spec202).`

In `series-2/2-2.md` §7: mark this order's items delivered; note the S1 pigeonhole as the sole remaining Series-2 theorem question this side of the νF order.

---

*End of work order. The star deserves its sentence: once C2 and T16 discharge its hypotheses, `no_windowless_of_connected_of_no_total` says that in this universe, isolation is not merely lonely but impossible — every object, to exist at all, is already open. Write the file so a philosopher can find `Windowless`, read the star's comment, and understand why the fish and the monad were always the same question.*
