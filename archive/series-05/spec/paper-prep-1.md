# Design + Executor Instructions: Closing Series 05 Open Obligations #2 and #12

**Owner workstream:** WS6 (with a WS3/WS1 carrier touch for #2).
**Status of this document:** a design contract, written to the Series 05 protocol.
Substitute openly, recover the intended content inside the surrogate where possible,
state any residual obstruction precisely, and **never relabel a shortfall as the
goal.** If either obligation cannot be discharged as specified, the honest outcome is
a Partial or an Impossibility, recorded in `charter-status.md`, not a redefinition.

No em dashes in any prose that lands in a paper drawn from this work.

---

## 0. The crux, resolved first (read before building)

The standing worry (raised in-conversation) was: does giving the tower a genuine
**carrier-level** infinite descent (obligation #2) reawaken the Parmenides collapse
(`ws2_collapse` / `ws5_global_groundless_collapses`)? If it did, #2 would be an
**Impossibility**, not an open task, and this design would be asking the executor to
prove something false.

It does **not** reawaken the collapse. The reason is in the hypotheses of the collapse
theorem, and the executor must preserve exactly the features that make this true:

1. **The collapse lives on the *plain, unlabelled* carrier `νPk κ`.** Its bisimulation
   (`hereditarilyNonempty_bisim`) works because on `νPk`, difference is only
   presence/absence of successors, so two objects that both never bottom out are
   bisimilar and hence equal. **The tower is built on the *labelled* carrier
   `νLk κ (GLabel Q)`, where the grade-and-`Q` label on each edge is a second currency
   of difference.** Two labelled descending spines with different labels are *not*
   bisimilar. This is precisely the Series 04 lesson (`ws3_loopface_ne`,
   `ws3_plurality_core`): faces defeat the collapse. The descending spine `descState`
   already exists and is plural-compatible for this reason.

2. **The collapse hypothesis is `HereditarilyNonempty` *everywhere on one carrier***
   (`∀ x, HereditarilyNonempty x` in `ws5_global_groundless_collapses`). A single
   descending chain on `Winf T` does **not** assert that hypothesis: it says *one*
   object has an infinite downward path, not that *every* object on a single carrier
   is hereditarily nonempty. The tower keeps **local foundedness at each level** (each
   `T.lvl a` is an honest bounded carrier); descent is a property of a *chain crossing
   levels*, not of a single carrier being atomless throughout. The Explosion Dilemma's
   second horn is about the latter and is untouched.

**Therefore #2 is closable in principle**: a labelled, cross-level descending chain on
`Winf T` is consistent with both impossibility theorems, because it is neither
unlabelled nor a single-carrier global-groundlessness claim. The executor's job is to
*build that chain on the real tower carrier* and prove it never terminates — porting
the existing standalone `descState` spine onto `Winf T`.

If, in the course of building, the executor finds that the port **forces** either (a)
dropping the labels or (b) asserting single-carrier hereditary-nonemptiness, then and
only then does #2 flip to an Impossibility. That would itself be a clean result; record
it as such. The design's expectation, grounded in the structure above, is that neither
is forced.

---

## Obligation #2 — no-first-level, earned at the carrier (not just the index)

### What is currently true (do not re-prove)

- `ws2_no_atom_floor`: no-first-level at the **index** level (no least index ⇒ a
  strictly lower level exists). Definitional; already built.
- `descState q0 hinf d` (WS6): a groundless descending spine on the **standalone**
  labelled carrier `νLk κ (GLabel Q)`, indexed by `ULift ℤ`, with
  `desc_succ` (the grade-`(d-1)` edge to its finer copy) and `ws6_descent_nonterminating`
  (below any grade there is a strictly finer grade at which it relates onward).
- What is **missing**: this spine is not on the tower carrier `Winf T`. The register
  says exactly this: "WS6's `descState` gives a descending spine on the standalone
  graded carrier, not yet on `Winf T`." So no-first-level is definitional at the
  carrier, not earned.

### Target (what "earned" means here)

Build a descending chain **on `Winf T`** for the constructed `cardinalTower Q`, and
prove it does not terminate: for every point on the chain there is a strictly
lower-level point it relates to, with the levels strictly decreasing in the tower index
and no least element reached. Concretely, the deliverable theorem:

```
theorem ws6_carrier_descent_nonterminating
    (Q : Type u) (hQ : Nonempty Q) (q0 : Q) :
    ∃ chain : ℤ → Winf (cardinalTower Q),
      ∀ n : ℤ,
        RelatesInf (cardinalTower Q) (chain n) (chain (n - 1))
        ∧ (chain (n - 1) ≠ chain n)
```

with a companion that ties the chain to genuinely descending **tower levels** (the
witness at `chain (n-1)` injects from a strictly lower index than the witness at
`chain n`), so the descent is cross-level and not collapsed inside one level:

```
theorem ws6_carrier_descent_crosslevel
    (Q : Type u) (hQ : Nonempty Q) (q0 : Q) :
    ∃ (chain : ℤ → Winf (cardinalTower Q)) (lvlOf : ℤ → (cardinalTower Q).Idx),
      ∀ n : ℤ,
        (∃ x : ((cardinalTower Q).lvl (lvlOf n)).carrier, chain n = toColim _ x)
        ∧ (cardinalTower Q).lt (lvlOf (n - 1)) (lvlOf n)   -- strictly lower level
        ∧ RelatesInf (cardinalTower Q) (chain n) (chain (n - 1))
```

(Adjust `.lt` to whatever strict-order the tower exposes; `cardinalTower`'s index is
`Cardinal × ℤ` under lex order, which has the strict descent in the `ℤ` component.)

### Construction plan

1. **Reuse `descState`, do not reinvent it.** The standalone spine already corecurses
   `d ↦ (grade-`(d-1)` edge to `descState (d-1)`)`. Its non-termination is
   `ws6_descent_nonterminating`. Keep it as the level-local content.

2. **Place each spine state at a level of `cardinalTower`.** The chain point `chain n`
   is `descState`'s state at grade `n`, injected into `Winf` via `toColim` at a tower
   index whose `ℤ`-component tracks `n`. Because `cardinalTower`'s index has a `ℤ`
   factor with no least element, the level assignment `lvlOf n` can strictly decrease
   without bound as `n` decreases: this is where "no first level" (index) does real
   work for "no atom floor" (carrier), which is the whole point of the obligation.

3. **Show the cross-level edge survives the colimit.** `RelatesInf T x y` is
   `∃ q, (q, y) ∈ succSet T x`. The spine's `desc_succ` edge must be shown to sit in
   `succSet (cardinalTower Q)` after `toColim`. This is the one genuinely new lemma:
   that `toColim` carries the level-local `lstr` edge to a `succSet` edge on `Winf`.
   Look for an existing `succSet`/`toColim` compatibility lemma in ws1/ws3 (the no-top
   proof `ws3_no_top` already reasons about `RelatesInf` across levels via `toColim`,
   so the plumbing exists — reuse its lemmas rather than proving compatibility from
   scratch).

4. **Distinctness (`chain (n-1) ≠ chain n`).** Use the label/grade to separate the
   states, exactly as `ws3_loopface_ne` separates faced loops. Two spine states at
   different grades carry different edge-labels, so they are not identified by
   `TowerColimRel`. This step is also what keeps the crux clean: distinctness comes
   from the *label*, never from an atom.

### Guardrails specific to #2

- **Do not** prove non-termination by asserting `HereditarilyNonempty` on any single
  carrier. The chain is a *selected path*, not a claim that the whole carrier is
  atomless. If a proof route seems to need global hereditary-nonemptiness, stop: that
  route runs into `ws5_global_groundless_collapses` and is the wrong route.
- **Do not** strip the labels to make the descent go through. A descent on the
  unlabelled `νPk` carrier *would* collapse; the labelled carrier is load-bearing.
  Run the strip test on the final theorem: delete the `GLabel`/grade and confirm the
  statement fails (it should). If it still goes through unlabelled, the theorem is
  proving the wrong thing.
- If the cross-level edge (step 3) cannot be built on `cardinalTower` specifically but
  can on `growingTower` or a bespoke tower, record #2 as **Partial — carrier descent
  on a bespoke tower, not `cardinalTower`**, and route the gap. Do not present a
  bespoke-tower descent as a `cardinalTower` result.

### Definition of done for #2

- `ws6_carrier_descent_nonterminating` and `ws6_carrier_descent_crosslevel` build,
  `sorry`-free, standard-three axioms.
- The strip test is recorded: unlabelled version stated and shown to fail (or a note
  that it reduces to the plain-carrier collapse).
- `charter-status.md` register #2 moved from **OPEN (Partial — definitional)** to
  **Discharged (carrier-level descent on `cardinalTower`)**, with the two theorem
  names and the crux note (why this does not reawaken Parmenides).
- The Series 05 payoff tracker row "Groundlessness without collapse" updated: the
  *descent* half is no longer "deferred to WS6's bespoke spine" but discharged on the
  tower carrier.
- `AxiomCheck.lean` extended with the two new theorems; axiom log regenerated.

---

## Obligation #12 — a genuine `relating = composed-of` coincidence

### What is currently true (do not re-prove)

- `RelatesAtGrade` and `IsComposedOfAtGrade` are **character-for-character the same
  definition** (both: `∃ q, ((grade,q), y) ∈ (lstr x).1`). So
  `ws6_relating_is_composition` is `Iff.rfl` and proves nothing. The register (#12) is
  explicit and honest about this; the code carries the confession in its docstrings.
- The identification duty (charter §5.5): a composition-side relation built from
  **`lcomp`** (the composition operator), proved `↔` the observation-side relation
  (`RelatesAtGrade`). The design's phrase: "one from `destInf`, one from `lcomp`."

### Target

Replace the alias with a **genuinely independent** composition-side definition, then
prove the coincidence:

```
/-- Composition side, built from `lcomp` — NOT an alias of the observation side.
    `x` is composed of `y` at grade `d` iff `y` appears as a component in the
    `lcomp`-composite structure of `x` at grade `d`. -/
def ComposedViaLcomp (x y : νLk κ (GLabel Q)) (d : ℤ) : Prop := …   -- from lcomp

theorem ws6_relating_is_composition_coincidence
    (x y : νLk κ (GLabel Q)) (d : ℤ) :
    RelatesAtGrade x y d ↔ ComposedViaLcomp x y d := …               -- a real proof
```

The theorem must **not** be `Iff.rfl`. Its proof must unfold `lcomp` on one side and
the observation destructor on the other and show they agree. If they only agree under
an extra hypothesis, that hypothesis is the honest scope: state it, do not hide it.

### Construction plan

1. **Find `lcomp` and its destructor law.** In Series 04 WS3, `lcomp` is the labelled
   composition operator and `lcomp_dest` is its computation rule (it appears in the S4
   axiom log as `Series04.WS3.lcomp_dest`). Series 05 transcribes the faced carrier;
   locate the S5 analogue (grep `lcomp`, `lcomp_dest`, `destInf` in ws3/ws6).

2. **Define `ComposedViaLcomp` from the composite's structure**, i.e. read the
   grade-`d` successors *out of* the `lcomp`-composite of `x`, rather than directly
   out of `x`'s own `lstr`. This is the "second, independently-motivated definition"
   the register demands. The content: `y` is a grade-`d` component of `x` iff, when
   you form the relevant `lcomp` composite, `y` shows up as a grade-`d` destination.

3. **Prove the `↔` via `lcomp_dest`.** The composition rule `lcomp_dest` says what the
   composite's destructor produces; the observation side `RelatesAtGrade` reads `x`'s
   destructor directly. The coincidence is that composing-then-observing equals
   observing, at matching grade. This is a genuine (if short) proof once `lcomp_dest`
   is in hand, not a definitional identity.

### Guardrails specific to #12

- The **acceptance criterion is that the proof is not `Iff.rfl` and the two
  definitions are not syntactically identical.** A reviewer (Phase D) will check this
  first. If the only way to make the `↔` go through is to make the two sides the same
  expression again, the coincidence is **not** earned; record #12 as remaining OPEN
  and say why, rather than dressing an alias in new syntax.
- If the coincidence holds only for a restricted class of `x` (e.g. non-atomic, or
  single-grade), that is a **Partial** with the class named, not a discharge.
- Keep `RelatesAtGrade` as the canonical observation-side relation so that
  `ws3_no_top`, `ws6_tower_unknowable`, and the descent theorems above are unaffected.
  Add the composition side alongside; do not rewire the existing payoffs through it.

### Definition of done for #12

- `ComposedViaLcomp` (independent of `RelatesAtGrade`) and
  `ws6_relating_is_composition_coincidence` build, `sorry`-free, standard-three axioms,
  and the proof is demonstrably not `Iff.rfl`.
- The old `ws6_relating_is_composition` (`Iff.rfl`) is either removed or explicitly
  retained only as a trivial remark clearly marked non-load-bearing.
- `charter-status.md` register #12 moved from **OPEN** to **Discharged (genuine
  coincidence)** or **Partial (coincidence on class C)**, with the theorem name and,
  if Partial, the class.
- The Series 05 payoff tracker "Cross-level relating, leak-free" coincidence column
  updated from **OPEN** to its earned status.
- `AxiomCheck.lean` + axiom log updated.

---

## Sequencing and process

Follow the Series 05 protocol phases for a scoped reopen, not a full series run:

1. **Design freeze.** This document is the contract. Commit it before building.
2. **Build (one session).** Do #2 and #12 together — they share the WS6 faced-carrier
   and `lcomp`/`descState` machinery, and touching both in one pass avoids a second
   carrier warm-up. Order: crux features first (labels + local foundedness preserved),
   then #12's `lcomp` coincidence (smaller, self-contained), then #2's carrier descent
   (needs the `toColim`/`succSet` plumbing).
3. **Blind review (Phase D).** Seed the reviewer with the built code + the two target
   signatures + the acceptance criteria above (the `Iff.rfl` check for #12, the strip
   test and the no-global-groundlessness check for #2) — **not** this document's
   motivating prose. The reviewer confirms: #12's proof is not an alias; #2's descent
   does not smuggle global hereditary-nonemptiness or drop labels.
4. **Address (Phase E), then one more review pass.** Exit when a pass returns no
   SERIOUS finding.
5. **Regenerate the axiom log against a clean build**, and update the README theorem
   counts (Series 05 goes from 43 to 43 + the new headline theorems).

## What must stay true no matter what (invariants)

- Sorry-free, no custom axioms, standard three only.
- Self-contained: nothing imported from `archive/` or `series-04/`; the faced carrier
  and `lcomp` are transcribed into Series 05 as they already are.
- Local foundedness at each tower level is preserved; global groundlessness is never
  asserted on a single carrier.
- Labels remain load-bearing; no payoff is allowed to go through on the stripped
  unlabelled carrier.
- If either obligation resists discharge, it is recorded as a Partial or Impossibility
  with a precise obstruction and routed. The bar is fixed; the ledger records the miss.

## Note on verification I could not perform

This design was written from a static read of the sources and the status registers; I
did not run Lean (no toolchain in this environment). The executor must treat the exact
names of `lcomp`/`lcomp_dest`/`succSet`/`toColim` compatibility lemmas as
*to-be-confirmed by grep in the live tree*, and must re-derive the crux argument inside
Lean rather than trusting the prose above. If the built reality contradicts any
structural claim here (for example, if `succSet`/`toColim` compatibility is not
already available), that is a design error to be recorded and fixed in this document,
not worked around silently.

---

## Executor note (built, `sorry`-free, axiom-clean — standard three)

Both obligations were built and verified against the pinned toolchain. Full `lake build` green;
`spec/axiom-check-log.md` regenerated; Series 05 headline count 43 → 47. Two design corrections,
recorded here as instructed:

**Obligation #2 — the descent.** Built as `ws6_carrier_descent_nonterminating` and
`ws6_carrier_descent_crosslevel` on `Winf (cardinalTower (GLabel Q))`.
- **Design fix (label set): `cardinalTower (GLabel Q)`, not `cardinalTower Q`.** The design's
  signature wrote `cardinalTower Q`, but step 1 reuses `descState`, which lives on the *graded*
  carrier `νLk κ (GLabel Q)`. A tower over the plain label set `Q` cannot host the graded spine,
  and the grade is exactly what the crux (and the strip test) require — on an ungraded uniform
  chain the descending states are bisimilar and collapse to one self-loop. So the tower is
  instantiated at the graded label set `GLabel Q` (WS6's own carrier). This is still *the*
  `cardinalTower`, not a bespoke tower.
- **Honest realization of "cross-level."** The chain's representatives sit at levels `(ℵ₀, n)`
  whose index strictly decreases in the `ℤ` coordinate (no least element), but whose cardinal is
  held fixed, so the connecting maps between them are identities (`boundRelax_refl`). Hence the
  descent's *unboundedness below* is powered by the `ℤ`-index having no least element, and its
  *distinctness* by the grade label (`descState_inj`) — not by cardinal stratification (cardinals
  are well-founded, so a strictly-descending cardinal chain is impossible; the design's "no first
  level (index) does real work for no atom floor (carrier)" is exactly this). The two theorems are
  honest about this: distinct colimit points, genuine `RelatesInf` edges, no `∀ x` /
  `HereditarilyNonempty` claim — a *selected path*, so the Parmenides collapse is not reawakened
  (the design's crux, confirmed in Lean).

**Obligation #12 — the coincidence.** Built as `ws6_relating_is_composition_coincidence`, proved
via the new lemma `lcomp_lstr : lstr (lcomp t) = t`.
- **Mechanism, stated transparently.** The genuine content is that `lcomp` is a *faithful section*
  of observation: `s ↦ Cofix.corec (lcompCoalg t) (some s)` is a coalgebra endomorphism of the
  terminal `νLk`, hence the identity (terminality), so `lcomp` reconstitutes a labelled structure
  exactly. The composition-side relation `ComposedViaLcomp x y d := RelatesAtGrade (lcomp (lstr x)) y d`
  (form the `lcomp` composite of `x`, then observe it) therefore coincides with `RelatesAtGrade x y d`,
  and the proof rewrites through `lcomp_lstr` — it is **not** `Iff.rfl`, and the two definitions are
  syntactically distinct (the acceptance criteria). The coincidence's meaning is "composing-then-observing
  = observing," i.e. composition's faithfulness; that is the honest level of the discharge, not a
  comparison of two a-priori-unrelated relations.

**Phase-D self-review (blind acceptance criteria).** #12: the proof is confirmed not `Iff.rfl` and
the definitions confirmed syntactically distinct. #2: the descent is confirmed to (a) depend on the
grade for distinctness (strip test bites — `descState_inj` uses the grade), (b) assert no global
hereditary-nonemptiness, (c) live on `cardinalTower`, not a bespoke tower. Verdict `payoffsEstablished`
is unchanged: the #2 carrier descent is not a double-unboundedness derivation, so WS7's derivation
count stays one.
