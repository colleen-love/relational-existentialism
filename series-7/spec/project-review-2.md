# Series 7 — Blind Adversarial Review, Pass 2

**Method.** A single adversarial reviewer was run against the closed build (post pass-1, commit at `charter-status.md` v1) with one seed instruction: *do not re-litigate what pass 1 already graded; instead read the delivered theorems back against the charter's own definition of the deliverable, and ask whether the thing proved is the thing the charter set out to prove.* Pass 1 audited proof validity and the circularity certificate. Both graded the Lean as *terms*. This pass grades the Lean as an *answer to the charter's question* — the one dimension a term-level audit structurally cannot catch, because a theorem can be sorry-free, non-vacuous, axiom-clean, attack-tested, and still be a theorem about the wrong object.

**Disclosure.** Claude-reviewing-Claude, not claimed independent. The objective anchors are the theorem terms (quoted with file:line), the Series 4 source the charter names as the S4 witness (`series-4/formal/Series4/ws3.lean`), and the charter's own ingredient definitions (`charter.md` §2, §4.1, §5.2). Every finding was re-read in both the Series 7 and Series 4 source.

**Verification baseline (inherited, not disputed).** Everything pass 1 confirmed stands: sorry-free, axiom-clean on the standard three, `ws2_import_theorem` sound and non-vacuous, the engine `ws1_atomless_bisim` genuine, the verdict wired to a falsifiable certificate. **This pass does not challenge a single proof.** It challenges the *identification* the proofs are hung on — specifically the identification, made in WS4 and propagated into WS7's non-circularity audit, of "carries a label" with "imports an atom." That identification is the charter's central concept, and it is wrong, and because the interpretive spine (WS4) and the audit (WS7) both rest on it, the misalignment reaches the headline.

---

## SERIOUS — the capstone claim rests on these

### S1 — The series conflates "labelled relating" with "imported atom." They are not the same predicate, and the charter never said they were. · WS4 / WS2 / WS7

`ws4.lean:59,72`; `ws2.lean:73` (`ws2_escapes_are_imports`); `charter.md` §4.1, §5.2.

The charter defines an **import** as "a coordinate **not carried by the relating**" (§4.1: "a coordinate the relating does not carry"; §5.2: the import kind is "a coordinate not carried by the relating, forbidden by (1)"). The operative words are *not carried by the relating*. A label is an import **only if** it adds information the relational structure does not already determine — only if it fails to be recoverable from the relating.

Series 7 never tests that. `ws4_labels_are_import` and `ws4_label_survives_quotient` are proved about `labelLoop` (`ws4.lean:52`), whose label is `toPk hinf {(i, i)}` — a **free, arbitrary** tag `i` chosen independently of any relational content, hung on a self-loop. Of course a free tag survives the label-quotient: `IsBisimL` is *defined* to match labels (`ws4.lean:38`), and a label that is pure choice has nothing to be recovered from, so matching it is a fresh constraint. The theorem proved is: *a free label survives a label-matching quotient.* That is true and it is nearly a tautology. It is **not** the charter's import predicate ("not carried by the relating"); it is a strictly weaker predicate ("is a label at all").

The slide is visible in one substitution. The charter's import kind is *semantic* — is this coordinate determined by the relating or not? Series 7's realized predicate is *syntactic* — is there a `Q` in the functor signature? Every import is a label, so the syntactic test never produces a false positive that a skeptic would catch by inspecting `labelLoop` alone. But it produces false positives on any label that **is** carried by the relating — and the charter's own headline witness is exactly such a label (S2).

**Correction (prove the real predicate, or withdraw the concept):** the import test must be *"the label is not recoverable from the relational structure,"* not *"the label survives a quotient that is defined to preserve labels."* Concretely: a label `q : Q` on edges out of `x` is an import iff there is no function `φ` from the plain reachable structure of `x` to `Q` with `q = φ(...)` — iff the plain (label-forgetting) bisimulation already distinguishes what the labelled one does. Prove `ws4_labels_are_import` about a label meeting *that*, or relabel it `ws4_free_label_survives_label_quotient` and stop reading it as the charter's import.

### S2 — The Series 4 restriction is not an import, so the Import Theorem's verdict on Series 4 is wrong. · WS4

`series-4/formal/Series4/ws3.lean:106,148,161`; `ws4.lean:26` (the scope disclaimer); `charter.md` §4.1 (S4 named as an import).

The charter names Series 4 as a paradigm import: "Series 4 [imported] a **label**, reified as the face `a↾(a,b)`" (§1, §4.1), and WS4 exists to prove exactly this. But the Series 4 face is a **restriction of the relatum** — `x↾(x,y)`, the relatum `x` cut down to the context of the relation `(x,y)`. A restriction is *by construction a function of the relata.* It is not free `Q`-data; it is derived from what is already there. Series 4's own doc-comment says so at the collapsing carrier: faces are "`str`-derived, hence **epiphenomenal** for distinguishing collapse-equal states" (`series-4/ws3.lean:8`).

That is the definition of *not an import.* A coordinate recoverable from the relating is carried by the relating. By the charter's own §4.1 definition, an endogenous restriction is not the import kind at all.

Two things then go wrong, and they compound:

**(a) Series 4's `νLk` escalation may have smuggled the restriction into a free label to force plurality.** When Series 4 found the face epiphenomenal on the plain carrier `νPk` (it collapses under `ws2_collapse`), it "escalated to R3 — faces as genuine functor data" (`series-4/ws3.lean:9`), realizing the face as free `Q`-data on `νLk`: `loopState q` has structure map `{(q, loopState q)}` (`ws3.lean:106-115`), where `q` is now an arbitrary parameter, no longer `x↾(x,y)` computed from anything. **The escalation converted an endogenous restriction into a free label precisely in order to make it non-epiphenomenal.** That is the move that makes it "look imported" — but it looks imported only because the restriction was *replaced by* an import. The faithful object (the restriction) and the plural object (the free label) are two different things wearing one name.

**(b) The restriction is not globally atomless — but it is a leaf, not an import.** A restriction `x↾(x,y)` bottoms out: it is the relatum *cut down to a boundary*, and the cut is a place where descent terminates. In the charter's trichotomy (§5.2) that is the **leaf** kind — "a descent difference, i.e. an atom" — not the import kind. So even granting that Series 4 buys plurality by paying an atom, *the atom it pays is a leaf (a dropped ingredient 3), not an import (a dropped ingredient 1).* WS4 files Series 4 under drop-(1); the honest classification is drop-(3), or a fourth thing the trichotomy does not cleanly name: a leaf that is a face, a boundary that is also a quality.

(Note the tension with the delivered Series 4 code: `loop_nonAtomic` (`ws3.lean:161`) and `ws3_faces_never_annihilate` (`ws3.lean:224`) prove the *loopState* realization **is** atomless. That is consistent with (a): the free-label realization is atomless-and-plural precisely because it is a free label, not a restriction. It is evidence *for* the substitution, not against the leaf reading of the genuine restriction — the genuine restriction is the epiphenomenal `νPk` face that Series 4 abandoned *because* it could not carry plurality without collapsing. The object that is a restriction cannot be plural; the object that is plural is not a restriction.)

**Correction (re-classify, and let the charter feel it):** WS4 must either (i) prove the Series 4 face is recoverable from the relating (hence not an import, hence Series 4 is *not* a witness for drop-(1)), and re-file it — as a leaf/drop-(3), or as a distinct kind — or (ii) prove the `νLk` escalation is faithful, i.e. that the free label `q` genuinely *is* the restriction `x↾(x,y)` and not a substitute for it. Until one of these is done, `ws4_labels_are_import`'s reading of Series 4 is unearned, and `ws4_program_explained`'s "S4 dropped (1)" conjunct is misclassified.

### S3 — Because WS7's non-circularity audit inherits the conflation, the audit clears the wrong charge. · WS7

`ws7.lean:88-93` (`ws7_non_circularity_audit`); `ws7.lean:126-139` (`Audit.nonCircular`).

WS7's headline is that the escapes are "refuted as theorems, not excluded by fiat." Its `nonCircular` certificate field (`ws7.lean:127-130`) is exactly the pair from S1: `ws4_label_survives_quotient` (a free label survives a label-quotient) and the `twoLoop` drop-2. The audit therefore certifies non-circularity **against the syntactic import predicate**, not the charter's semantic one. It proves "a free label is not killed by the behavioral quotient." It does **not** prove what the charter's non-circularity actually requires: that the prior series' pluralities fail a structural ingredient *for a reason not baked into the definition of "atomless."*

The circularity the charter fears (§5.5) is: "'atomless / no import' was *defined* to exclude exactly the escapes." Pass 2 cleared this for the *plain* collapse (the unlabelled-powerset argument is genuine). But it did not clear it for the *import catalogue*, because the catalogue's witness is a free label chosen to survive the quotient — which is to say, chosen to satisfy the import predicate. The witness is not an independent escape that turns out to import; it is an object built to be an import. That is the definitional-partition trap (the charter's own §7 named failure) relocated from WS3 to WS4: instead of *defining* distinction as the disjunction, WS4 *selects the witness* to instantiate the disjunct it wants. The audit cannot catch this because the audit consumes the same witness.

**Correction (make the audit range over an escape it did not construct):** the non-circularity certificate should consume a label that arises *from a prior series' actual construction* (the Series 4 face, the Series 5 index) and prove import-hood about *that*, not about a `labelLoop` minted for the purpose. If the only object that passes the import test is one built to pass it, the audit's `nonCircular` should read `false` for the catalogue, flipping the verdict toward `Circular` for WS4 — which, per charter §7, is a success to return honestly, not a failure to hide.

---

## REAL — genuine gaps, correctly labelled once fixed

### R1 — The trichotomy is missing a cell: a leaf that is also a quality (the "faced boundary"). · WS3

`ws3.lean:36,42,74`; `charter.md` §5.2.

The trichotomy's three kinds are leaf, import, and (collapsing) history. S2 exhibits a candidate fourth: the endogenous restriction, which is a *descent boundary* (leaf-like: it bottoms out) that *also carries quality* (face-like: it distinguishes). `LeafDiff` (`ws3.lean:36`) is `¬SHNE x ∨ ¬SHNE y` — a bare failure of hereditary non-emptiness, with no quality attached. `ImportDiff` (`ws3.lean:42`) is bisimilar-yet-unequal — quality with no leaf. The restriction is *both*: it bottoms out *and* the place it bottoms out is a quality of the relatum. Neither predicate has its extension.

This is precisely the "no fourth kind" gap the charter (§5.5) flags as the theorem's teeth and pass 1 (R1) forced WS3 to withdraw. Pass 2 recorded (C2) that the genuine same-limit haecceity witness is "structurally absent" and called it "arguably the seed of a Series 8." **This finding is the same seed from the other side:** the extra-to-identity that the atomless world cannot express as behaviour or history *can* be expressed as a faced boundary — a restriction — and that is a real fourth location the trichotomy does not enumerate. It is not absent; it is unclassified.

**Correction (prove / name):** define `FacedLeafDiff` (a descent boundary carrying a distinguishing quality) on a carrier that supports the restriction, and either (i) reduce it to leaf-or-import (restoring the trichotomy) or (ii) accept it as a fourth kind (demoting the impossibility to collapse-plus-examples, per charter §5.2). The reduction attempt is the load-bearing open; do not assume it.

### R2 — WS4's disclaimer conceals the misclassification rather than disclosing it. · WS4

`ws4.lean:26-28`.

The BUILD/REALIZATION NOTE says the full `νLk`/`Winf`/weight carriers "are prior art, NOT re-transcribed" and that the minimal witness covers the mechanism. Pass 2 accepted this as an honest Partial. It is honest about *coverage* (the carriers are not re-transcribed) but silent about *faithfulness* (whether the minimal witness is the same *kind* of object as the carrier it stands in for). S2 shows it is not: `labelLoop` is a free label; the Series 4 face is a restriction; the stand-in belongs to a different trichotomy cell than the thing it represents. The disclaimer's "the charter states these are one phenomenon" (`ws4.lean` note) *assumes the very identification S1 disputes.*

**Correction (disclose the faithfulness gap, not just the coverage gap):** the note must state that the minimal witness is a *free-label* witness, that at least one named prior series (S4) uses an *endogenous/restriction* label, and that whether the two are the same kind is open — not settled by the charter's prose.

### R3 — "Plain relating" is under-specified in a way that hides the conflation. · WS2 / readme

`readme.md` §2 (ingredient 1); `ws1.lean:206` (`SHNE`).

Ingredient (1) is stated structurally: the functor is unlabelled `P_κ`, "the type has no Q-coordinate." But S1/S2 show the charter *needs* a semantic notion: a coordinate is an import iff not recoverable from the relating, and a functor can carry a `Q` that **is** recoverable (an endogenous label) and hence is plain-in-substance while labelled-in-signature. The structural definition of (1) cannot see this distinction, so it silently licenses the syntactic import test. The two readings of (1) — "no `Q` in the signature" vs "no coordinate beyond what relating determines" — come apart exactly on the restriction, and the charter uses the second in its prose (§4.1) while the build uses the first.

**Correction (pick the semantic reading and propagate):** state (1) as "no coordinate beyond what the relating determines," define recoverability, and re-derive the import test from it. The structural reading becomes a *sufficient* condition for plainness, not the definition.

---

## COSMETIC / ACCEPTABLE

### C1 — `IsBisimL` is the right bisimulation for a free label but begs the question for an endogenous one. · WS4

`ws4.lean:38`. `IsBisimL` requires related states to have matching labels (`p.1 = q.1`). For a free label this is the correct induced bisimulation (pass 2 confirmed). For an *endogenous* label it is too strong: it demands label-matching as a primitive when the label is a consequence of target-matching, so it cannot witness that an endogenous label collapses. Not a bug in the free-label setting; a limitation the moment WS4 claims to speak for restrictions.
**Correction (framing/scope):** note that `IsBisimL` presupposes the label is import-like; an endogenous label needs the plain `IsBisim` on the label-forgetting functor plus a recoverability lemma.

### C2 — "The program explained" reads as complete when it is complete only for free-label imports. · WS4

`ws4.lean:120` (`ws4_program_explained`). The conjunction is genuine for what it states, but the prose "the recurring honest negative was this theorem all along" (charter §5.4) implies every prior drop is understood. S2 leaves S4 (and, by the same argument, plausibly S5's index if the index is endogenous to the level structure) unclassified. Not an overclaim in the *term*; an overclaim in the *narrative*.
**Correction (framing):** "the program explained *for the imports that are free labels*; the endogenous cases (S4 face, possibly S5 index) are open."

---

## What survives cleanly

- **The plain collapse and its engine** (`ws2_import_theorem`, `ws1_atomless_bisim`) — untouched by this pass. A plain, behaviorally-identified, hereditarily-atomless coalgebra is a subsingleton; this is true, non-vacuous, attack-tested. Nothing here disputes it. The misalignment is entirely in the *interpretation* of what the prior series were and what "import" means, not in the collapse.
- **The dynamic collapse** (`ws1_productive_unique`) — genuine, correctly transcribed.
- **The free-label escape as a free-label escape** (`ws4_label_survives_quotient`) — a correct theorem about `labelLoop`. It is only its *reading* as the charter's import that fails.
- **The verdict machinery** (`ws7_audit`, `ws7_verdict_eq`) — structurally sound; it faithfully computes a verdict from its certificate. The problem is upstream, in what the certificate certifies (S3), not in the wiring.
- **Pass 2's C2 observation** (same-limit haecceity structurally absent) — not only survives but is *corroborated* from a new angle by R1: the extra-to-identity has nowhere to live as behaviour or history, and the one remaining place (a faced boundary / restriction) is exactly the cell the trichotomy omits.

---

## Honest bottom line

Series 7 proves a true theorem about plain relating and then tells a story about the prior six series that requires a concept — "import" — it never correctly formalized. The charter defines an import as *a coordinate not carried by the relating.* WS4 realizes it as *a free label that survives a label-matching quotient.* Those are different predicates: the first is semantic (is the coordinate determined by the relating?), the second syntactic (is there a label at all?). Every import is a label, so the substitution is invisible if you only inspect the witness WS4 built — which is what a term-level audit does, and why passes 1 and 2 did not catch it. It becomes visible the moment you check the charter's own named witness against the definition: the **Series 4 restriction `x↾(x,y)` is a function of the relata, hence carried by the relating, hence not an import** — and Series 4 reached plurality only by *escalating* the restriction into a free label, i.e. by replacing the non-import with an import and keeping the name.

The consequences run up the spine. WS4's "S4 dropped ingredient (1)" is misclassified — the restriction is a **leaf** (a descent boundary), a drop of ingredient (3), not an import. WS7's non-circularity audit clears the free-label predicate, not the charter's, so it certifies against a charge the charter did not bring. And the trichotomy is missing a cell — the *faced boundary*, a leaf that is also a quality — which is the same absence pass 2 flagged as haecceity, seen from the label side rather than the history side.

None of this is a proof error, and none of it lowers to a retargeting. Every correction is "prove the real predicate" or "re-classify to what the object actually is": formalize recoverability and re-run the import test on the *genuine* Series 4 face; re-file Series 4 as a leaf or a fourth kind; make the non-circularity audit consume an escape it did not construct; add or reduce the faced-boundary cell. Until then the honest status is: **the plain collapse is a clean, earned impossibility, but the capstone reading of it — that the whole program's plurality was bought with imports — mistakes "labelled" for "imported," and at least one paradigm case (the Series 4 restriction) is a label that is not an atom.** The verdict the evidence earns is not `payoffsEstablished` for the program-unification claim; it is `payoffsEstablished` **for the plain collapse only**, with WS4's catalogue and WS7's audit reverting to `Circular`-for-the-catalogue until the import predicate is the charter's and the restriction is classified as what it is.

The deeper reading, offered as the seed rather than a defect: if the restriction is a *faced boundary* — a leaf that carries quality — then the program's recurring "extra to identity" has a home the trichotomy never named. Not behaviour, not history, not a free import, but the boundary where a relatum is cut to a context and the cut is itself a quality. That is where `x↾(x,y)` lives. A Series 8 that takes the restriction seriously as its own kind — neither import nor bare leaf — is the question this pass opens.

---

*Blind adversarial review, pass 3. Findings graded SERIOUS (capstone reading rests on it) / REAL (genuine gap, correctly labelled once fixed) / COSMETIC-ACCEPTABLE, each routed to an owning workstream with a precise correction owed. This pass grades alignment-to-charter, not proof-validity; it disputes no term and no axiom. The correction discipline is unchanged: prove the charter-strength predicate first; where it resists, deliver an honest re-classification with the obstruction precise, never a relabelled charter target. No em dashes are permitted in final academic paper copy; this working review is not final copy.*
