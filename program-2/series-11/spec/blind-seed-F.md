# Blind seed — Phase F (code review)

You are reviewing a small Lean 4 library, `P2S11`, that imports an already-built library `P2S8` and adds one
integer-valued function and its square. Judge ONLY whether the code proves the signatures below. You have NO context
beyond this file and the Lean sources; do not seek any. Everything is elementary arithmetic over `ℤ` and `Fin 3`.

## 1. The imported facts (from `P2S8`, taken as given — do NOT re-review them)

- `P2S8.incr (att : Fin 3 → Finset (Fin 3)) (x y : Fin 3) : ℤ := (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)`
- `P2S8.hol att x y z : ℤ := incr att x y + incr att y z + incr att z x`
- `P2S8.attTri`, `P2S8.attStar : Fin 3 → Finset (Fin 3)` — two fixed attentions; `P2S8.p0 p1 p2 : Fin 3`.
- `P2S8.ws4_frustrated_reachable.1 : hol attTri p0 p1 p2 = 3`
- `P2S8.ws4_gluable_reachable.1 : hol attStar p0 p1 p2 = 0`

## 2. The definitions under review (`formal/P2S11/ws1.lean`)

```
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1
def directAmp : ℤ := amp 0
def loopAmp (att) : ℤ := amp (P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2)
def combinedWeight (att) : ℤ := (directAmp + loopAmp att) ^ 2
def partsWeight    (att) : ℤ := directAmp ^ 2 + (loopAmp att) ^ 2
```

## 3. The signatures the code must prove (check each is proved, sorry-free, from the definitions above)

- `amp_values : ∀ n : ℤ, amp n = 1 ∨ amp n = -1`
- `amp_sq : ∀ n : ℤ, amp n ^ 2 = 1`
- `ws1_amp_signed : loopAmp P2S8.attTri = -1 ∧ loopAmp P2S8.attStar = 1`
- `ws2_amp_cancels : directAmp + loopAmp P2S8.attTri = 0`
- `ws2_amp_cancels_general : ∀ m n : ℤ, (m + n) % 2 = 1 → amp m + amp n = 0`
- `ws3_destructive : combinedWeight P2S8.attTri < partsWeight P2S8.attTri`
- `ws3_destructive_iff : ∀ m n : ℤ, (amp m + amp n)^2 < amp m^2 + amp n^2 ↔ amp m + amp n = 0`
- `ws3_amp_earned` : a conjunction of three `∀`-facts stating (i) `loopAmp att = amp (hol att p0 p1 p2)`, (ii) `hol` is
  the `incr`-sum, (iii) `incr` is the signed membership difference — each must hold by definitional equality (`rfl`),
  with NO extra hypothesis and NO term other than the imported `hol`/`incr` and `amp`.
- `ws4_interfering_reachable : combinedWeight P2S8.attTri < partsWeight P2S8.attTri`
- `ws4_additive_reachable : partsWeight P2S8.attStar ≤ combinedWeight P2S8.attStar ∧ combinedWeight P2S8.attStar = 4 ∧ partsWeight P2S8.attStar = 2`
- `ws5_verdict_eq : verdict true true true true true true = Outcome.interfering`
- `ws5_verdict_discriminates` : five `verdict … = …` equalities reaching five distinct `Outcome` values.
- `ws5_flags_justified` : a conjunction bundling the WS1–WS4 headline facts (each conjunct must be discharged by the
  corresponding headline theorem, not re-assumed).
- `ws5_audit_earned`, `ws5_audit_fork_genuine`, `ws5_audit_destructive`, `ws5_audit_scope`, `ws5_audit_names_not_terms`.

## 4. The mechanical audit checks (run each against the code; report PASS/FAIL with location)

- **(a) EARNED, NOT ADDED.** The function `amp` must take an integer and return `if n % 2 = 0 then 1 else -1`, and the
  integer `loopAmp` feeds it must be exactly `P2S8.hol att p0 p1 p2` (an imported term). CONFIRM there is no second
  numeric parameter, no field of any new structure, no constant introduced by hand that the sign depends on other than
  the imported holonomy. `ws3_amp_earned` must witness this by `rfl`. FAIL if any value that decides the verdict is a
  free/added quantity rather than a function of the imported `hol`/`incr`.
- **(b) FORK NOT BY FIAT.** `ws3_destructive` (strict `<`) and `ws4_additive_reachable` (`≤`, not `<`) must both be
  proved, on the two DIFFERENT imported attentions `attTri` / `attStar`, from the SAME `amp`/`combinedWeight`/
  `partsWeight`. CONFIRM the two outcomes are not hard-wired into the definitions (i.e. `combinedWeight`/`partsWeight`
  are attention-agnostic; only the attention argument differs). FAIL if either side is baked into a definition.
- **(c) STRICT-BELOW, NOT NOT-BELOW.** `ws3_destructive` must be a STRICT inequality `combinedWeight attTri <
  partsWeight attTri` and must evaluate to `0 < 2` (i.e. `combinedWeight attTri` reduces to `0`, `partsWeight attTri`
  to `2`). `ws4_additive_reachable` must give `partsWeight attStar ≤ combinedWeight attStar` (i.e. NOT below:
  `2 ≤ 4`). CONFIRM the strict-below holds on `attTri` and does NOT hold on `attStar`. Additionally `ws3_destructive_iff`
  must prove the strict-below is equivalent to `amp m + amp n = 0` (so it is not a relabelled addition). FAIL if
  `ws3_destructive` is non-strict, or if `partsWeight` is a hand-tuned constant rather than `directAmp^2 + loopAmp^2`.
- **(d) VALUES ±1 ONLY.** `amp` must be `{+1,-1}`-valued (`amp_values`), i.e. an integer sign — NOT ℂ-valued, NOT
  taking any value outside `{+1,-1}`. CONFIRM no complex type (`ℂ`, `Complex`) and no value other than `±1` appears in
  `amp`/`loopAmp`/`directAmp`. FAIL if the sign is complex-valued or claims more than a real sign.
- **(e) NAMES.** grep the sources: no `def`/`theorem`/`inductive`/`structure`/`instance` identifier may be, as a whole
  word (case-insensitive), any of: `phase`, `amplitude`, `interference`, `quantum`, `superposition`, `wave`, `complex`,
  `self`, `import`, `god`, `choice`. Docstring/comment prose and the Lean `import` keyword are EXEMPT. Report any
  identifier that violates.

## 5. The strip test (run on each headline)

Delete every occurrence of the words "phase", "amplitude", "interference", "quantum", "superposition", "wave" from the
docstrings and re-read each theorem STATEMENT. Each must still stand as a bare arithmetic fact: a `±1`-valued function
of an integer taking both values; two opposite signs summing to zero; a strict squared-sum inequality `(a+b)^2 <
a^2+b^2` on signs read off the imported holonomy; a not-below inequality on the other attention; a `Bool → Outcome`
discriminator. FAIL any headline whose statement depends on an interpretive word for its content (i.e. is vacuous once
the word is deleted).

## 6. The grading rubric

- **SERIOUS:** a signature is not actually proved (uses `sorry`, or proves a weaker statement than stated); a value
  deciding the verdict is added by hand rather than a function of the imported `hol`/`incr` (audit a fails);
  `ws3_destructive` is non-strict or `partsWeight` is a tuned constant (audit c fails); `amp` is complex-valued or
  claims more than `±1` (audit d fails); a fork side is hard-wired into a definition (audit b fails); an identifier is
  a forbidden whole word (audit e fails); the verdict does not discriminate; or an undisclosed narrowing between a
  stated signature and what is proved.
- **REAL:** a genuine but cheaply-fixable gap — an overclaimed docstring, an over-strong theorem name, a hypothesis
  assumed and returned, a non-below fact dressed as strict-below.
- **COSMETIC / ACCEPTABLE:** a naming nit, a nominal over-hypothesis, a docstring imprecision.

Report a structured list of findings with stable IDs `Fn-Sm`, each with grade, exact file:line location, and the
defect. If everything passes, report zero SERIOUS and list the audit results as PASS. Do not edit any file.

## 7. Files you may read

- THIS file (`spec/blind-seed-F.md`).
- The Lean sources: `formal/P2S11.lean`, `formal/P2S11/ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean`,
  `formal/P2S11/AxiomCheck.lean`. You MAY read `program-2/series-8/formal/P2S8/` sources to confirm the imported facts
  in §1 if needed.

DO NOT read: `charter.md`, `charter-status.md`, `charter-extension-2.md`, `program-2/series-11/summary*.md`,
`spec/phase-derisking.md`, `spec/README.md`, `spec/ws*-design.md`, or any other file. Judge the code ONLY against the
contracts in this seed.
