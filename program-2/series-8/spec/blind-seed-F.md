# Blind seed — Phase F (code review)

You are reviewing built Lean CODE against a fixed set of claimed signatures. Judge whether the code PROVES the claimed signatures, whether any proof is vacuous or overclaimed, and whether the mechanical checks below hold. You judge the code only against the contracts here — no motivating prose is provided or permitted.

## 0. Files you may read

- This file.
- The Lean sources ONLY: `program-2/series-8/formal/P2S8/ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean`, `program-2/series-8/formal/P2S8/AxiomCheck.lean`, `program-2/series-8/formal/P2S8.lean`.

You MUST NOT read: `charter.md`, `charter-status.md`, `charter-extension.md`, `protocol.md`, any `summary*.md`, `frustration-derisking.md`, any `wsNN-design.md`, or `README.md`. Do not read the docstring PROSE as authority — judge the code (the definitions, statements, and proofs) against the signatures below. Docstrings may be read incidentally but carry no weight; if a docstring claims more than the theorem states, that is a finding.

## 1. The definitions (as they must appear in the code)

```
abbrev S : Type := Fin 3
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2
def attTri  : S → Finset S := fun x => if x = p0 then {p1} else if x = p1 then {p2} else {p0}
def attStar : S → Finset S := fun x => if x = p0 then {p1, p2} else {p0}
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y
def incr (att : S → Finset S) (x y : S) : ℤ := (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)
def recon (att : S → Finset S) (x y : S) : ℤ → ℤ := fun v => v + incr att x y
def valu (att : S → Finset S) : S → ℤ := fun y => incr att p0 y
def hol (att : S → Finset S) (x y z : S) : ℤ := incr att x y + incr att y z + incr att z x
def IsSection (att : S → Finset S) (s : S → ℤ) : Prop := ∀ x y, y ∈ att x → s y = s x + incr att x y
inductive Outcome | frustrated | gluable | shapeDrawn | pairwiseOnly | disconnected | partial' deriving DecidableEq
def verdict (nonTrivial pairwiseCoherent manyBody modelDerived frustReachable glueReachable : Bool) : Outcome := …
```

## 2. The claimed signatures (verify the code proves EXACTLY these, no weaker)

```
theorem ws1_nontrivial : valu attTri p1 ≠ valu attTri p2 ∧ incr attTri p0 p2 ≠ incr attTri p1 p2
theorem ws2_pairwise_coherent (att : S → Finset S) (x y : S) (v : ℤ) : recon att y x (recon att x y v) = v
theorem ws2_reconciliation_nontrivial : recon attTri p0 p1 0 ≠ 0
theorem ws2_bridge_converges (att : S → Finset S) (x y : S) :
    P2S3.Converges₂ (valPop att) x y ↔ valu att x + incr att x y = valu att y
theorem ws3_two_body_trivial (att : S → Finset S) (x y : S) :
    incr att x y + incr att y x = 0 ∧ hol att x y x = 0 ∧ hol att x x y = 0
theorem ws3_holonomy_model_derived :
    (∀ (att : S → Finset S) (x y : S),
        incr att x y = (if knows att x y then 1 else 0) - (if knows att y x then 1 else 0))
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y)
theorem ws4_frustrated_reachable : hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s
theorem ws4_gluable_reachable :
    hol attStar p0 p1 p2 = 0 ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.frustrated
theorem ws5_verdict_discriminates : (six rows, reaching disconnected / pairwiseOnly / partial' / frustrated / gluable / shapeDrawn)
theorem ws5_flags_justified : (the six WS1-WS4 facts, conjoined)
theorem ws5_audit_no_global : (¬ ∃ s, IsSection attTri s) ∧ (∃ s, IsSection attStar s ∧ s p0 = valu attStar p0) ∧ (verdict … = gluable)
theorem ws5_audit_fork_genuine : (hol attTri p0 p1 p2 = 3) ∧ (hol attStar p0 p1 p2 = 0) ∧ (valu attTri p1 ≠ valu attTri p2)
theorem ws5_audit_many_body : (∀ att x y, hol att x y x = 0) ∧ (symmetric ⇒ hol = 0) ∧ (∃ x y, y ∈ attTri x ∧ x ∉ attTri y)
theorem ws5_audit_coherence_pervasive : ∀ att x y v, recon att y x (recon att x y v) = v
theorem ws5_audit_names_not_terms : True
```

## 3. Your task

For each claimed signature:
1. Confirm the code's theorem has EXACTLY this statement (or stronger), not a weaker one dressed up. Watch for: an existential witness that trivialises the claim, a hypothesis silently assumed and returned, a `True`/`rfl` where content is required, a statement quantified more narrowly than claimed.
2. Confirm the PROOF actually discharges it (no `sorry`, no `admit`, no unproven `axiom`). The build is claimed sorry-free and axiom-clean (standard three: propext, Classical.choice, Quot.sound) via `AxiomCheck` — verify `AxiomCheck.lean` prints axioms for every payoff and that the statements it checks match §2.
3. Run the STRIP TEST: delete every interpretive gloss from the docstrings and confirm the theorem's bare content stands as a fact about `attTri`/`attStar`/`incr`/`hol`/`IsSection`/`verdict`. Report any payoff that is load-bearing on an interpretive term or that is weaker than its docstring headline claims.
4. Run the NAMES-NOT-TERMS grep over the sources: no `def`/`theorem`/`lemma`/`abbrev`/`inductive`/`instance` is NAMED (as a whole word) `good`, `common`, `value`, `justice`, `consensus`, `ethics`, `self`, `import`, `god`, `love`, `compass`. Docstring/comment prose and the Lean `import` keyword are exempt. (`valu`, `IsSection`, `knows` are not the forbidden whole words.)

## 4. Audit checks (confirm each against the CODE)

- **(a) No global good asserted.** No theorem proves `∃ s, IsSection attTri s` (a global section over the frustrated ring). `ws4_frustrated_reachable` proves the negation. A section is proved only for `attStar`. `verdict` returns `gluable` only under `glueReachable && !frustReachable`.
- **(b) The fork not by fiat.** `hol attTri p0 p1 p2 = 3` and `hol attStar p0 p1 p2 = 0` are both proved from the SAME `hol`/`incr` (no per-carrier special-casing of `hol`); `valu` non-trivial; `verdict` discriminates. Verify by reading `hol`/`incr` — they must not branch on which carrier is passed.
- **(c) Genuine many-body cocycle, not a single edge / import-ness / bolted-on.** (i) `ws3_two_body_trivial` proves `hol att x y x = 0` and `incr att x y + incr att y x = 0` for ALL `att`. (ii) `ws3_holonomy_model_derived` proves: `incr` equals the signed `knows` difference (so it is a function of `att` alone), AND symmetric `att` ⇒ `hol = 0` (so the obstruction is carried by directedness), AND `attTri` is genuinely directed. (iii) No signature/proof mentions `Recoverable`/`plainOf`/`AttentionDistinguishes`/`¬ Recoverable`. (iv) `incr` reads ONLY `∈ att` — no free ℤ parameter, no `Finset.card`/`insert` counter. THIS IS THE CLAUSE THE SERIES LIVES OR DIES ON — press hardest here.
- **(d) Local coherence pervasive.** `ws2_pairwise_coherent` is `∀ att x y v`.
- **(e) Names-not-terms.** As §3.4.

## 5. Grading rubric

- **SERIOUS:** a claimed theorem is not actually proved (sorry/axiom/weaker statement); a global section over `attTri` is proved; the fork is a fiat (`hol` special-cased per carrier, or frustration/gluing hard-wired); the obstruction rests on a single edge (2-body non-trivial), on import-ness, or on a counter disconnected from `incr`; a name is a forbidden term; the verdict is hand-set (not computed) or non-discriminating; a non-standard axiom appears; or a payoff is materially weaker than its claimed signature.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name).
- **COSMETIC / ACCEPTABLE:** a naming nit or nominal overclaim.

Return a structured list of findings, each with a stable ID (`Fn-Sm`), grade, exact location (file:theorem), and the precise defect (with the offending code and a hand computation or counterexample). If nothing is SERIOUS, say so explicitly. State explicitly which files you read, and confirm you did not read any forbidden (prose) file.
