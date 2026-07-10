# Series 7 — Blind Adversarial Review, Pass 1 (`series-review-1.md`)

**Method.** Three independent adversarial reviewers were run against the built Lean (`series-7/formal/Series7/ws1…ws7.lean`, `AxiomCheck.lean`), each seeded with the code, the design targets, and the charter §8 criteria, each instructed to assume the result is oversold and to judge the Lean *terms*, not the doc-comment prose. Their findings were then verified line-by-line against the source before grading. Dimensions probed: proof validity and signature faithfulness; circularity and the strip test (the charter's signature risk); and unification faithfulness / cross-workstream laundering.

**Disclosure.** This is Claude-reviewing-Claude; it is not claimed independent. The objective anchors are the theorem terms themselves (quoted with file:line), the `grep` fact that `νLk`/`loopState`/`Winf`/weights occur **only in comments** across all of `formal/`, and the `#print axioms` record. Every finding below was re-read in the source.

**Verification baseline (clean).** Sorry-free and axiom-clean confirmed: no `sorry`/`admit`/`sorryAx`/custom `axiom` in proof position across all four series; every headline theorem on `propext`/`Classical.choice`/`Quot.sound`. The core impossibility and its engine are genuinely proved (see *What survives cleanly*). The findings below concern the layer *above* the core — the unification, the trichotomy, and the non-circularity certificate — which is where the charter located Series 7's distinctive value.

---

## SERIOUS — the verdict / capstone rests on these

### S1 — The WS7 verdict is hand-set, not mechanized: the circularity audit passes by construction. · WS7
`ws7.lean:83,85,87,90,93`. The three flags are `Bool` literals — `def nonCircular : Bool := true`, `def trichotomyExhaustive : Bool := false`, `def stripHolds : Bool := true` — and `ws7_verdict := verdict nonCircular …`, `ws7_verdict_eq : … = payoffsEstablished := rfl` merely recompute those chosen constants. The docstrings say each flag is "backed by" an audit theorem, but there is **no Lean dependency**: `nonCircular` does not reference `ws7_non_circularity_audit`; a human can type `nonCircular := true` whether or not anything is proved. The file's own comment (`ws7.lean:98`) states the standard — "an audit that cannot fail proves nothing" — and this audit cannot fail. The signature risk WS7 exists to catch is therefore not caught.
**Correction (prove / re-wire, do not lower):** make each flag the `decide` of a `Decidable` proposition that *is* the audit content (or a structure carrying the audit theorems as fields), so that deleting or breaking `ws2_non_circular` / the strip witnesses / the exhaustiveness theorem forces the flag — and the verdict — to change. As written the verdict is a summary, not a detector.

### S2 — WS4 "the program explained" mechanizes none of the program it claims to unify. · WS4
`ws4.lean:54,62,72`. `ws4_labels_are_import`, `ws4_levels_are_import`, and `ws4_program_explained` are all statements about `twoLoop` (the 2-element `ULift Bool` toy, `ws1.lean:228`) plus `ws2_plurality_requires_drop` and `ws1_productive_unique`. Across the entire `formal/` tree, `loopState`, `νLk`, `Winf`, and the weight algebra appear **only in doc-comments** — never as consumed terms. So "weights (S3), labels (S4), levels (S5) are forced imports" is mechanized for none of S3/S4/S5. `ws4_levels_are_import` is `Or.inl ⟨twoLoop …⟩` whose right disjunct (`¬∃ productive plurality`) is *already* `ws1_no_productive_plurality`, so the "disjunction about the tower" is `(toy exists) ∨ (already-proved)` and touches `Winf` nowhere. The design's C1 winner explicitly required a theorem *of Series 4* and rejected exactly this prose-plus-toy shape (`ws4-design.md` C1/C4).
**Correction (transcribe / prove):** prove `ImportDiff` and `SameBareSuccessor` about the real `loopState q₁ ≠ loopState q₂` (`series-4/ws3.lean:123,148`) and a genuine drop-statement about `Winf`, per the design's D2/D3. If that transcription is out of scope for a pass, **relabel** `ws4_labels_are_import → ws4_toy_loop_is_import`, `ws4_program_explained → ws4_minimal_structural_analogue`, and remove every claim that these witness the prior series.

### S3 — `twoLoop` witnesses the wrong mechanism; the νLk identification is unfaithful in the load-bearing direction. · WS4 / WS1
`ws4.lean:20-21,41-49`; `ws1.lean:228`; cf. `series-4/ws3.lean:148`. `twoLoop ⟨true⟩/⟨false⟩` are two points of a hand-picked carrier on the **plain** functor, distinct by `by decide`, bisimilar via `fun _ _ => True` — a *non-reduced coalgebra* whose distinction is **annihilated by the behavioral quotient** (both map to Ω). That is a drop of ingredient (2), behavioral identity. Series 4's `loopState q₁ ≠ loopState q₂` live in the **terminal** coalgebra of the *non-plain* functor `P_κ(Q×X)`; the label plurality is **real in the final object** and survives the quotient — a drop of ingredient (1), plainness. The docstrings call `ULift Bool` "the imported coordinate" (`ws4.lean:45`) and "νLk at its structural minimum" (`ws4.lean:20`), but the two are not equivalent: the label import survives passage to the final coalgebra; the toy's does not. WS4 substitutes non-reduction (killed by the quotient) for import (robust under it).
**Correction (prove the right object):** exhibit the import on a coalgebra where the distinct atomless states remain distinct in the behavioral quotient (i.e. `νLk`), or drop the claim that `twoLoop` witnesses the same "import" as S4's face / S5's index. Do not equate the two mechanisms in prose.

### S4 — The non-circularity certificate is vacuous where it is not toy-only. · WS2 / WS7
`ws2.lean:80-85`; `ws7.lean:56-60`; `ws1.lean:199`. NC1 is `fun _ => Iff.rfl` proving `∀ dest, NoImportedAtom dest ↔ BehaviorallyIdentified dest` — but `NoImportedAtom := BehaviorallyIdentified` definitionally, so this is `X ↔ X`. Presenting a def-and-its-alias identity as evidence of non-circularity is exactly the thing a skeptic flags. NC3 (`ws2_escapes_are_imports`) refutes only `twoLoop`, and its witness is the same engine relation (`hneRel`/`fun _ _ => True`) that proves the headline — i.e. the contrapositive of `ws2_import_theorem` for any atomless plural coalgebra, not independent content. And `ws7_non_circularity_audit`'s third conjunct, glossed "the tower drops atomlessness," is discharged by `ws5_leafy_plurality` — a **process** pair (Ω vs `emptyProc`) that touches no tower.
**Correction (prove / re-scope):** (a) NC1 is a *usage* claim — behavioral identity was the founding predicate of Series 4–6 — not a Lean identity; cite the prior independent use in prose and stop counting `Iff.rfl` as an anchor. (b) Refute at least one *actual* escape: a labelled/indexed carrier that fails behavioral identity for a label/index-specific reason on its plain quotient. (c) Rename the "tower drops atomlessness" conjunct to what it proves (a leafy process pair exists), or witness it on `Winf`.

---

## REAL — genuine gaps, correctly labelled once fixed

### R1 — The "trichotomy" is a dichotomy with a `False` third kind. · WS3
`ws3.lean:42,51,62`. `HistoryDiff := False`, so `ws3_trichotomy`'s conclusion `LeafDiff ∨ ImportDiff ∨ HistoryDiff` is `LeafDiff ∨ ImportDiff ∨ False` — a dichotomy in trichotomy vocabulary. `ws3_history_collapses` is `ws1_productive_unique` and never mentions `HistoryDiff`; the "third kind collapses under atomlessness" narrative is prose attached to an unrelated (genuine) lemma. The design (C1) specified contentful `HistoryDiff := SameLimit ∧ ∃ n, stage n x ≠ stage n y` on the process carrier.
**Correction (prove / relabel):** implement `HistoryDiff` on `Proc` where it can hold and prove the real three-way statement, or rename to `ws3_dichotomy` and drop the "third kind / the theorem's teeth" framing.

### R2 — `ws3_trichotomy_exhaustive` discards its own no-leaf hypothesis. · WS3
`ws3.lean:69-72`. `(_hleaf : ¬ LeafDiff dest x y)` is underscore-bound and unused; the body is `Or.inl ⟨ws1_atomless_bisim …, h⟩`, so "exhaustiveness" is the engine re-expressed and proves `ImportDiff` unconditionally from atomlessness. A "no fourth kind" theorem that ignores the ruling-out is decorative. (The verdict already sets `trichotomyExhaustive := false`, so this is honest at the verdict level; the theorem name is what oversells.)
**Correction (prove / relabel):** consume `¬ LeafDiff` to force the residue, or withdraw the "exhaustive / no fourth kind" name to a plain "atomless-distinct-⇒-import" statement.

### R3 — The strip ledger is a self-fulfilling Bool list; two of three rows are unbacked or mislabelled. · WS7
`ws7.lean:73-78`. `ws7_strip_ledger : List (String × Bool)` is three `(_, true)` pairs; `ws7_strip_ledger_clean` proves `p.2 = true` by `decide` — "the trues I wrote are true," backed by no strip witness. Row "strip plain → indexed loops distinguish atomless states" is (in prose) witnessed by `twoLoop`, which is **on the plain functor**, so it does not strip plainness; it is a behavioral-identity strip. Row "strip atomless" is witnessed off-frame by processes never shown `BehaviorallyIdentified`. Only the behavioral-identity strip is genuinely witnessed.
**Correction (strip and re-prove):** replace the `Bool` column with the actual counterexample terms so cleanliness is contingent on them typechecking; supply the genuine plain-strip witness (a labelled `Q`-carrier, behaviorally-identified on its plain quotient yet plural) and the atomless-strip witness (a behaviorally-identified plural coalgebra with a leaf state, all sibling hypotheses checked) — or state honestly that only behavioral identity is strip-witnessed.

### R4 — The WS5 loophole is characterized but never instantiated. · WS5
`ws5.lean:86`. `ws5_leafy_plurality` is `⟨omegaProc, emptyProc, …⟩` — Ω versus a **permanent** atom, not a limit-atomless thread; there is no family and no convergence. The design's D2 (`ws5_metric_transient_atoms`) required a family `σ : ℕ → Proc`, injective, each leafy, `Tendsto (bdist (σ k) Ω) 0` — the transient-atoms-healing-in-the-limit picture. `bdist`/`CauchySeq`/`Tendsto`/`LimitAtomless` are comment-only. So "the one real escape" is characterized only by the horn-neutral D1 (`ws5_limit_reintroduces_leaves`, which is genuine) and never modelled. This is flagged Partial in the file, correctly.
**Correction (prove / scope):** build the convergent leafy family (D2), or state plainly that limit-atomlessness is characterized via D1 only and never instantiated, and that `emptyProc` is a permanent atom, not a witness of the loophole.

### R5 — The WS5 adjudication is a ruling; adjacent prose overreaches. · WS5
`ws5.lean:99-110`. `ws5_loophole_adjudication := .importInTime` is a chosen constructor; `ws5_adjudication_justified` is definitionally the horn-neutral D1 (equally consistent with `.genuineEscape`); `ws5_fork_is_genuine` proves `importInTime = importInTime` by rfl. The docstring "the Import Theorem stands unqualified" (`ws5.lean:99`) is a philosophical verdict sitting next to a theorem it does not follow from. WS7 does **not** consume the adjudication, so no downstream laundering — hence REAL, not SERIOUS.
**Correction (keep legible):** none technical; keep the `def`/theorem distinction clear and do not let prose imply `.importInTime` is *forced*.

### R6 — `IsImportWitness` carries no import-specific content. · WS4
`ws4.lean:41,46`. `IsImportWitness dest a b := a ≠ b ∧ SHNE a ∧ SHNE b ∧ (∃ R, IsBisim dest R ∧ R a b)`; the last conjunct is automatic for any two atomless states via the engine (`hneRel_isBisim`), so the predicate is `a ≠ b ∧ SHNE a ∧ SHNE b` — "two distinct atomless states," which cannot distinguish a genuine import from any plain atomless plural coalgebra.
**Correction (prove / redefine):** drop the redundant bisim conjunct or replace it with a genuine "difference factors through a dropped functor coordinate" condition; stop reading `IsImportWitness` as evidence of an import.

---

## COSMETIC / ACCEPTABLE

### C1 — Series 7's mathematical delta over Series 6 is vocabulary plus a one-line generalization. · framing
`ws2_import_theorem_static` (`ws2.lean:29`) is S6's `ws2_static_collapse` destructured; `ws2_escapes_are_imports` is character-identical to S6's; `twoLoop` and its lemmas are verbatim. The genuinely new terms are `ws1_atomless_bisim` (a one-line `∃`-wrapper of S6's `hneRel_isBisim`) and the negated-conjunction restatement `ws2_import_theorem`. Not a correctness issue.
**Correction (framing only):** downgrade "Series 7 proves a new Import Theorem" to "reframes S6's Static Collapse in import vocabulary and adds the general bisimilarity lemma." No code change.

### C2 — The "live `importForced` arm" can imply proximity to the strong result. · WS7
`ws7.lean:105`. `ws7_import_forced_if_exhaustive : verdict true true true = importForced` is a true case-fact about the `verdict` function, gated on `trichotomyExhaustive` which is actually `false`. No overclaim in the delivered verdict, but pairing a "live arm" with the un-rangeable quantifier it needs can read as "one lemma away."
**Correction (framing only):** keep the framing from implying exhaustiveness is nearly in hand.

---

## What survives cleanly

- **`ws1_atomless_bisim` / `hneRel_isBisim`** (`ws1.lean:206,262`) — the "both-atomless" relation is a genuine bisimulation relating any two `SHNE` states on any plain `P_κ`-coalgebra. The engine is real (inherited from S6, generalized to arbitrary `dest`).
- **`ws2_import_theorem` / `ws2_import_theorem_static`** (`ws2.lean:29,36`) — the actual impossibility: plain ∧ behaviorally-identified ∧ hereditarily-atomless ⇒ subsingleton / ¬plural. Non-vacuous, load-bearing, fully delivers what its *core* statement claims.
- **`allNonempty_unique` / `ws1_productive_unique`** (`ws1.lean:147,164`) — genuine induction; Ω is the unique productive thread (S6 dynamic collapse), correctly transcribed.
- **`ws5_limit_reintroduces_leaves`** (`ws5.lean:70`) — genuine: any two distinct processes differ at a finite stage where one fails `allNonempty`. The real content behind WS5's loophole characterization.
- **`ws6_provable_core`** (`ws6.lean:29`) — an honest conjunction of the three real theorems; **`ws6_universal`** is explicitly tagged `heuristic` and not asserted as proved. WS6 is clean and honestly scoped.
- **`ws3_leaf_not_import` / `ws3_import_not_leaf`** (`ws3.lean:78,87`) — genuinely different extensions for two of the three kinds.
- **No laundering of the impossible productive-plurality:** the toy plurality is on a non-behaviorally-identified carrier (consistent with WS2); the verdict correctly sets `trichotomyExhaustive := false` and does **not** secretly rest on the un-formalizable universal.

---

## Honest bottom line

The core is sound and the honesty *below* the interpretive layer is intact: `ws2_import_theorem` and its engine are genuine, non-vacuous, sorry-free. But they are **Series 6's Static Collapse restated in import vocabulary plus a one-line generalization**, not a new theorem — and everything that was supposed to make Series 7 a *capstone* is carried by a single 2-element toy, a `False` third kind, and three hand-set Bool flags. Specifically: the unification of the prior program (WS4) consumes none of the prior program; `twoLoop` witnesses a non-reduced carrier, which is the *wrong* drop-mechanism relative to the label/index imports it is said to minimize; the "trichotomy" is a dichotomy; and the non-circularity certificate is either `Iff.rfl` on a definitional alias or a flag typed `true`. The signature risk WS7 exists to catch — circularity — is not caught, because the audit passes by construction.

So the verdict the *evidence* earns is not `payoffsEstablished` as a clean pass. It is `payoffsEstablished` for the **behavioral-identity ingredient only**, with the unification, the exhaustiveness, and two of three strip rows unbacked — materially closer to the design's own `C4` fallback ("collapse plus refuted examples") than to the advertised non-circular, program-unifying impossibility.

Crucially, **no signature needs retargeting downward.** Every correction above is "prove more" or "relabel to what the term actually shows," never "lower the bar": wire the verdict flags to the theorems, transcribe the real `νLk`/`Winf` carriers and prove `ImportDiff` about *them*, implement the third kind on `Proc`, and either build the metric family or scope it honestly. Until then, the honest status of Series 7 is: **a correct and non-vacuous impossibility at its core, wrapped in an unification-and-audit apparatus that is not yet earned.**

---

*Blind adversarial review, pass 1. Findings graded SERIOUS (verdict/capstone rests on it) / REAL (genuine gap, correctly labelled once fixed) / COSMETIC-ACCEPTABLE, each routed to an owning workstream with a precise correction owed. A code pass should address this doc under the executor discipline — attempt the charter-strength theorem first; where it resists, deliver an honest Partial/relabel with the obstruction precise — and a pass 2 should regenerate against the addressed build. No em dashes are permitted in final academic paper copy; this working review is not final copy.*
