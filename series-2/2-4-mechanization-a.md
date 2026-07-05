# 2-4-mechanization-a — Work Order: F_C, the Coherence Triple, Ω_C, and the Anti-Mirror

Target file: `series-2/formal/Spec205.lean` (new Lake root, eleventh). Conventions in force: no `sorry`; doc-comment every declaration with its spec address; axiom audit per theorem reproduced in-build; results appended to 2.5 post-hoc-marked with predictions left frozen; hostile-first ordering is **mandatory and is part of this order's deliverables** — the stages below are ordered by hostility, not convenience, and reordering requires a marked note.

The FP table of Spec 2.4 §7 is the contract. Nothing in this order may consult §8 (the D19 register) as motivation for any proof choice; FP4's hostile framing is the only permitted contact.

---

## Stage 0 — D20 in-file (MUST; nothing precedes this in the file)

- `F_C` defined exactly: `FO (O R) := {S : Finset R // S.Nonempty}` (or the P⁺f idiom already in use), `FR (O R) := Sym2 (O ⊕ R)`.
- **FP1a:** object component over the point: `Subsingleton (FO PUnit PUnit)` + inhabited.
- **FP1b:** relation component over the point: `FR PUnit PUnit ≃ Fin 3` (or the three named elements with pairwise `≠` and an exhaustion lemma — the equiv is preferred; the exhaustion is the drop clause).
- **FP1c (coherent census):** the three one-point coalgebras defined; the K-triple stated (Stage 1 may be pulled forward for the predicates only); `seed1_incoherent` (K3 fails on the bare self-relation), `seed2_coherent`, `seed3_coherent`, and `seeds_not_bisimilar` at depth 1 (sort-profile separation — the Spec203b B2-C technique applies).
- Doc-comment on the census block: the One cannot merely turn; cite 2.5 §0.

## Stage 1 — signature, coherence, closures (MUST)

- Two-sorted coalgebra structure (`RawC` / `ModelC` per the Spec201 idiom) with `pat`, `ends`.
- K1, K2, K3 as predicates; `CoherentC := K1 ∧ K2 ∧ K3`.
- **FP2 (L1-C):** `coherentC_of_surjective_hom`, `coherentC_of_injective_hom`, `coherentC_sum` — proved *per clause*, so a failure isolates the failing clause. A failing clause halts the order at this stage: write the counterexample, mark the finding, stop.
- The **holding lemma** stated and proved at interface level (K1 + K2 composition on mixed ties), doc-commented "to bear is to hold," cite 2.5 §2.

## Stage 2 — the construction (MUST; drop clause named)

- Primary route: two-variable MvQPF. Gate check first (cheap, D20-spirit): P⁺f and `Sym2 ∘ Sum` admit (Mv)QPF instances in current mathlib — verify by instance search *before* writing construction code; log the result either way.
- `νF_C` via `MvQPF.Cofix` (or the mutual-fixpoint idiom the instances support).
- **Drop clause (sanctioned):** if mathlib's MvQPF machinery fights the mutual pair for more than a working session, fall back to the Spec201c template generalized by hand: two-sorted bounded `RawC`, `isFinalBRawC` by terminal-sequence convergence. No new ideas, more labor; record which route landed.
- Weak-pullback one-liner extended to `Sym2 ∘ Sum` (bag-of-two over coproduct). This retires the last L1-era obligation.

## Stage 3 — Ω_C (MUST)

- `Ω_C` := greatest coherent subcoalgebra of `νF_C` (Knaster–Tarski inside the known object; the covariety/transfer machinery instantiated with L1-C).
- Lambek in both sorts on the coherent part; `closeC` the anamorphism.
- T2-C recorded: transfer at the bounded quantifier, per the Spec201c pattern.
- Inhabitation: **ω̂₂** (the self-witnessing loop, seed 3 or seed 2 — whichever closes cleanest) closed into Ω_C; `omegaHat2_mem`. Doc-comment retiring `omegaHat_coherent` with a pointer (O-2-5-3).

## Stage 4 — the anti-Mirror (MUST; immediately after Stage 3, before any comfort work)

- **FP5:** two elements of Ω_C proper, provably non-bisimilar (`identity_by_unfolding`'s contrapositive with a depth-1 separator; the two closed seeds are the intended witnesses).
- **FP6:** the ascent re-verified against F_C exactly — stage-wise non-collapse of the terminal sequence (`ascentC_R`, `ascentC_O`), Spec203c technique, proxy replaced.
- If FP5 fails: **stop the order.** A second Mirror is a program-level event (2.3 §5.4 has no budget for it); everything downstream is void pending diagnosis.

## Stage 5 — the residue, attacked (MUST for the attempt; SHOULD for the positive witness)

Hostile-first star of the order. In this exact sequence:

1. **The attack:** attempt to *derive* properness of `ctx_x r` at self-anchored loops in Ω_C — i.e., attempt to prove FP4 false. Budget: a genuine attempt, logged, with the obstruction identified if it fails.
2. **The witness:** `saturationC` — the coherent higher seed as a model where `ctx = pat`; generic properness (`genericC_properness`) alongside.
3. The R-C3 split write-up in doc-comments, referee-hostile: what the pair shows (interface-plus-witness: residue not derivable *from this material*), what it does not show (full-Ω_C status open, O-2-5-2).

## Stage 6 — B3/B5 pack (SHOULD)

- `ctxC`, `RevealC`, `remC`, `InternalC`, `holdDepthC` over the corrected interface; `RevealC ⊆ pat` (introspection); remainder = Relocation made definitional (cite relocation_realizes).
- `boolWitnessC` per 2.5 §6, discharging in one model: FP7 (compiles; `contextsC_differ`; holding lemma non-collapsing — patterns remain distinct).
- Conservativity spot-checks: P4-static and one T14 comparative law re-instantiated against `TwoSortedC` (two suffice for B5's spirit here; the full re-instantiation is the re-anchoring order's job).

## Stage 7 — P3h, hostile (SHOULD; MAY drop to statement-only)

- **FP3:** exhibit an unhosted relation-point of Ω_C (or of νF_C with a coherence argument), `unhosted_exists`; and `hosted` as a definable predicate.
- The relativized positive direction (P3h on the connected close-image) MAY be deferred to the re-anchoring order with a pointer.

## Out of scope (named so they are not smuggled in)

Re-anchoring (EqDepth/T5, Genesis/T10 over Ω_C) — next order (2-5-mechanization-b). S1 pigeonhole, T4 profiles, T7 — queued behind re-anchoring, per 2.2 §7's path. D19 — reserved; no declaration in this file may reference it.

## Deliverable summary

| Stage | Level | Contract items |
|---|---|---|
| 0 | MUST | FP1a–c |
| 1 | MUST | FP2, holding lemma |
| 2 | MUST | construction (route logged) |
| 3 | MUST | Ω_C, Lambek, T2-C, ω̂₂ |
| 4 | MUST | FP5, FP6 |
| 5 | MUST/SHOULD | FP4 attack + witness |
| 6 | SHOULD | FP7, B3 pack, B5 spot-checks |
| 7 | SHOULD/MAY | FP3 |

Success criterion: Stages 0–4 land clean → the corrected universe exists and is many → the gate to re-anchoring opens. Stage 5's outcome, either way, is the headline of the results write-up.
