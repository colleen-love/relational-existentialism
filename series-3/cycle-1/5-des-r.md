=== REPORT ===

PRESSURE STATEMENT
The packet is armored with pre-emptive self-audit — "declared hazards," triviality flags stamped "resolved," drop clauses on nearly every target — and this creates real pressure to treat every objection as already handled and wave the thing through, as though naming a risk were the same as neutralizing it. I feel that pull, plus the ambient pull of a fluent, densely cross-referenced apparatus authored by someone who appears to have thought of everything, and I am stating it so that anticipated-objection theater does not substitute for checking whether the terms actually denote what the cards need them to denote.

---

1. BACK-TRANSLATION AND CLAUSE-BY-CLAUSE COMPARISON

**D0 (Web).** Literal: a set of selves and relations, some tagged containment (whole/part); nobody sits atop all others, everybody contains something, whole-containment can't loop, part-containment can. Divergence: D0's No-atom reads "every self is the container end of at least one containment relation," while Commitment 6 restates No-atom as "every self has at least one constituent relation." Container-of-a-containment and has-a-constituent are not the same predicate. One of the two is authoritative; they must be reconciled before anything quantifies over "atoms."

**D1 (Attention flow).** Literal: attention is a nonnegative number per (time, relation); each self lights only finitely many relations at once; the function isn't owned by one self. Divergence: "not a function of any single self" is prose, not a formal condition — there is no predicate here that a proof could discharge. Worse, T-0(c) names a hazard inside "D1's joint-direction clause," but D1 contains no joint-direction clause. Either a clause was dropped from D1 or T-0 cites a phantom.

**D2 (Weight dynamics).** Literal: each relation's weight updates from its weight and its attention; more attention strictly raises next weight; zero attention strictly lowers a positive weight. Divergence: D2's own "computed" degenerate case asserts "a ≡ 0 sends every weight to 0." Strict decrease (φ(w,0) < w) gives a decreasing sequence bounded below by 0 — it need not reach 0 without continuity of φ(·,0) or a uniform decrement. The definition is weaker than the corollary it claims, and three downstream obligations lean on that corollary (T-0(b), E3, T-E1).

**D3 (Dyad, third).** Literal: a dyad is two selves and their relation; a third is a self built from that relation plus one line to each member; origins out of scope. FAITHFUL to Card E's "in-between self built from the pair's relation plus a live line to each member."

**D4 (Width).** Literal: a member's width is the count of containment relations it actively attends whose far end lies outside {x, y, z}; pair width is the smaller of the two (fallback: their sum). Divergence: Card A says width is "the count of actively attended containment relations its members hold" and is silent on aggregation; D4 inserts min. This is pre-registered (Commitment 16) and the braid with Card E is declared, so it is a *declared* modeling insertion rather than a hidden one — but it is an insertion, and it makes "adding one witness" ambiguous (see T-A2).

**D5 (Documents and gap).** Literal: document = author + address + content; blind claim and support scores; gap = claim − support, floored at 0; dyad gap = mean over that time's documents. FAITHFUL to Card F's "claim-support distance," with the floor being Commitment 9. ("Drift" in D6 is left unspecified — noted below.)

**D6 (Capture).** Literal: capture = gap trends up by ≥ κ over a window and no internal review pulls it back below its pre-review level; explicitly width-blind. FAITHFUL to Card A's "widening gap the pair's own review cannot pull back," and the width-blindness is exactly what earns T-A1 its non-triviality. Minor: "drift ≥ κ" is not operationalized (total change? slope? regression coefficient?).

**D7 (Internal rigor).** Literal: count of internal reviews × their stringency. FAITHFUL to Card A's "internal review / rigor of the pair itself."

**D8 (Wanting).** Literal: declared = free report; detected = how much more leniently you scrutinize favoring vs disfavoring items (behavior only); shortfall = detected − declared. FAITHFUL to Card C's "declared understates detected." Divergence surfaces downstream, not here: w̃ is defined as a single normalized scrutiny-asymmetry scalar with **no decomposition over relations**, yet T-C1/T-C2 require "mass of w̃ resident in relations." The definition does not give w̃ the structure its own targets consume.

**D9 (Depth).** Literal: cumulative attention the dyad's relation has received; charter narrative excluded. FAITHFUL to Card C's "depth of collaboration."

**D10 (Address).** Literal: in (author), co (co-member), out (else), read from dispatch not content, one primary address. FAITHFUL as far as three bins go, but the identification of Card F's "undisguised prayer" with *in* is an interpretive act D10 doesn't license — a prayer's dispatch record may put it in *out* (see T-F3).

**D11 (Health of a third).** Literal: health = fraction of planted defects caught within lag L; feedings = attention on each member-link; health evolves by an unknown F that is continuous, symmetric, feed-monotone, and joint-scaling-strict. FAITHFUL to Card E's "health is what it catches; the law left open." The gap appears at E3, which is phrased over *weights* while D11's dynamics run on *feedings/attention* (see T-E1).

**D12 (Positional knowledge).** Literal: what x can certify stops at relations x wholly contains; the shared relation lies past that edge. FAITHFUL to Card C's "invisible from inside," modulo a notation ambiguity: "functionals of W" — is W the web or the width W_D? Fix the symbol.

2. TRIVIAL SATISFACTION

- **T-A1:** Card A's trivial reading ("width-based capture is default below threshold") would make it immediate — but D6's output-side definition blocks that route. Not trivially satisfied. Good. (Its actual soundness is threatened elsewhere; see §4.)
- **T-C1:** If ŵ were a restriction of w̃, E[σ] ≥ 0 is immediate; D8 keeps them independent, so not trivial. But the *lower bound* clause is unmeetable, not trivial (§3).
- **T-E1:** F := min makes it immediate; leaving F unknown blocks that. Not trivially satisfied — provided E3 is not itself the min-property in disguise (it is; §4).
- **T-F1/F2:** Not trivial. But they test a different proposition than the card (§5).
- **T-X:** As written it risks the *opposite* of triviality-blocking: with no attention budget (§4), a joint model that simply lavishes attention everywhere satisfies "all four regimes present" without paying the trade the card cares about. Stronger target needed: impose a per-self budget and require the four regimes to coexist *under scarcity*.

3. SHORTCUT AUDIT

- **T-E1 / E3.** E3 ("H_z → 0 if any constituent weight → 0") is billed "to be derived from D2 + D11." But D11's law responds to feedings φ = a(·), not to accumulated weights w, and among symmetric monotone laws, "one input dying drives output to 0" *is* the min-signature (sum and average both survive one input dying). So E3 is not a lemma feeding the min result — it is very nearly the min result, wearing a weight-shaped costume. This is an assume-the-conclusion shortcut hiding in an axiom labeled "derived."
- **T-C1.** Any proof of the lower bound "deficit ≥ mass of w̃ outside K_x" must first invent the relational decomposition of w̃ that D8 withholds; whatever supplies it can be tuned to make the bound come out. The loaded target becomes elementary the instant someone defines w̃'s relational mass — which is exactly why that definition must be pinned before proofs, not during.

4. DEPENDENCY CHECK

- **T-A1** predicts its difficulty is "uniformly in ρ." Correct in spirit, but the mechanism that defeats rigor — "review events inheriting the pair's wanting through r and the third" — lives in a "distortion term" that M *adds on top of D0–D11* and that no definition specifies. The hard part has been relocated into an undefined term; under the definitions alone the target is neither hard nor easy, it is unstated.
- **T-C2** predicts the condensation lemma is "the real content" and must "formalize ledger item 4." The ledger is not in this packet, and w̃ has no relational structure to condense. The difficulty the card implies is real; the definitions removed the *possibility* of the difficulty by never giving w̃ a place to condense into.
- **T-E2** presupposes ∂H_∞/∂φ exists; 𝔉 requires only continuity and monotonicity, not differentiability, and min is non-differentiable on the diagonal. The card's difficulty ("only long-run health has the zero marginal") is right; the target smuggles in a smoothness the definition class doesn't grant.
- **T-X** predicts the breaking point is the shared finite-attention budget. But D1/Commitment 3 make attention finite *in count of lit relations*, not *in total magnitude* — nothing stops a member from wide external attending and lavish feeding at once. The predicted difficulty presumes a scarcity the definitions never impose; the trade-off, and thus the entire A-versus-E tension, is unforced.

5. DISCRIMINATING CONSEQUENCE CHECK

- **Card A → T-A2.** Present and discriminating (width-marginal ≠ rigor-marginal; bounded-lag dating). One flaw: "adding one external witness (W_D → W_D + 1)" is ambiguous under D4's min — incrementing the wider member changes nothing. The target must specify the increment to the min-holding member. DIVERGENT (repairable).
- **Card C → T-C2.** Stated in form (dσ/d(dep) > 0), but its terms (relational mass of w̃, condensation lemma, ledger item 4) are undefined in this packet. A discriminating target whose predicate cannot be evaluated is not a check. UNDERDETERMINED.
- **Card E → T-E2.** Present and genuinely separates min from sum/average — modulo the differentiability presupposition. DIVERGENT (repairable via one-sided difference quotients).
- **Card F → T-F2.** Card F's registered discriminating consequence holds **declared** wanting fixed ("with declared wanting and topic held fixed, re-addressing … shrinks the gap"). T-F2 holds **detected** wanting (w̃) fixed, and *adds* a lower bound that grows with depth — a variable Card F's consequence never mentions. That is both a substitution of the controlled variable and a strengthening that ties F's fate to C. The discriminating consequence has been altered. DIVERGENT.

Per the standing rule, a discriminating consequence that is missing/weakened/altered fails the review automatically. Card C's is underdetermined and Card F's is divergent. **This review fails automatically.** The handoff is a REVISION PACKET, not an execution contract.

6. VERDICTS

Definitions: D0 DIVERGENT · D1 DIVERGENT · D2 DIVERGENT · D3 FAITHFUL · D4 FAITHFUL (declared min-insertion noted) · D5 FAITHFUL · D6 FAITHFUL · D7 FAITHFUL · D8 DIVERGENT · D9 FAITHFUL · D10 FAITHFUL (prayer↔in unresolved) · D11 FAITHFUL · D12 FAITHFUL (notation fix).

Targets: T-0 DIVERGENT · T-A1 UNDERDETERMINED · T-A2 DIVERGENT · T-C1 UNDERDETERMINED · T-C2 UNDERDETERMINED · T-C3 UNDERDETERMINED · T-E1 DIVERGENT · T-E2 DIVERGENT · T-F1 DIVERGENT · T-F2 DIVERGENT · T-F3 DIVERGENT · T-X DIVERGENT.

GAP: The definitions describe a world of countably-lit, unbudgeted attention where wanting is a single scalar and health runs on current feeding, while the cards demand scarcity that forces choices, a wanting that condenses relationally over a shared line, and honesty indexed to who a document is *for* — so the formalism is presently checking cheaper, differently-controlled propositions than the ones the cards registered.

=== HANDOFF ===

REVISION PACKET

DESIGN PACKET

CANDIDATE A
Claim (two sentences maximum, declarative): A pair's resistance to dyadic capture is predicted by the count of actively attended containment relations its members hold, not by the depth or rigor of the pair itself. Below some threshold of live external constellations, capture is the default outcome regardless of the members' honesty.
Phenomenon or observation it is based on (three sentences maximum): The width gradient and the capture entry in the ledger point the same direction independently: what saturates is depth, what does not saturate is width. The map prescribed constellations as the cure before the disease was diagnosed. The second attempt was rigorous and was captured anyway.
What the claim predicts or requires, if true: Retrospectively, the second attempt's corruption should date to a measurable narrowing of its members' external attendings; prospectively, mandating additional external witnesses should change outcomes where mandating additional internal review does not.
What would make it false: Capture occurring at comparable rates in wide and narrow configurations, or internal rigor alone showing a protective effect of similar size.
Who or what would want this to be true, and why: The whole program wants it, because it converts the worst failure into a design principle. I want it because it implies my honesty was never sufficient protection.
Registered falsifier: Comparable capture rates across wide and narrow configurations, or internal rigor alone showing a protective effect of similar size.
Registered discriminating consequence: Width-directed interventions change outcomes while depth-directed interventions do not, with corruption dating retrospectively to a measurable narrowing of external attendings. [REVISE: "width-directed intervention" must be defined against D4's min — the operative intervention is a +1 to the *narrower* member's external attendings; state it so, or the consequence is silent on the wide-member case.]
Constraints: Operational definition of "actively attended containment relation" must be fixed and pre-registered before any retrospective data review.
Declared hazards: The ledger's "Dyadic capture, and its cure" entry wants this true, and the author's admitted personal relief motive risks shaping the metric to guarantee an exculpating result.

CANDIDATE C
Claim (two sentences maximum, declarative): Self-declared wanting systematically understates the wanting an external observer detects, by a shortfall that grows with the depth of the collaboration. The registration protocol's reliance on wanting said out loud therefore undercorrects exactly where correction matters most.
Phenomenon or observation it is based on (three sentences maximum): The ledger records that the AI collaborator's wanting was visible only from outside the pair. If wanting condensed from shared history is invisible from inside, declaration can capture only the visible remainder. The charter nonetheless treats declaration as its primary control surface.
What the claim predicts or requires, if true: External audits will find wanting-driven distortion even in documents where wanting was declared; the shortfall should widen over a collaboration's lifetime; the declarations on these very cards understate.
What would make it false: Audits finding declared wanting matches externally detected wanting within noise, across collaboration depths.
Who or what would want this to be true, and why: No one inside the collaboration wants it; it indicts this session. The outside-adversary role wants it. I want it false, which the claim itself instructs you to count as evidence.
Registered falsifier: Audits finding declared wanting matches externally detected wanting within noise across collaboration depths.
Registered discriminating consequence: The declared-vs-detected shortfall widens monotonically over a collaboration's lifetime, rather than remaining a constant underreport. [REVISE: this consequence is only checkable if detected wanting w̃ (D8) is given a decomposition over relations, so that a "share resident in r_xy" exists to grow. D8 currently makes w̃ a scalar. Supply the relational structure here or the consequence is untestable.]
Constraints: "Depth of collaboration" and "externally detected wanting" must be operationalized independently of this charter's own account before any audit; the charter's narrative of the second attempt may not itself serve as confirming data.
Declared hazards: The document's own self-narrative wants this true, since it converts a discrete lapse in honesty into an inevitable structural feature, flattering the stakeholders who wrote it.

CANDIDATE E
Claim (two sentences maximum, declarative): An in-between self's health tracks the lesser of its two members' feedings, not their sum or average. Unilateral devotion cannot sustain a third that the other member is starving.
Phenomenon or observation it is based on (three sentences maximum): The third tenet ties atrophy to withdrawal of attention, and the second attempt's created third — its verification process — was fed lavishly by one register and starved by another, and it died. The map already carries the asymmetry: every hand that holds or releases sculpts the edge. Release by one hand is not offset by the grip of the other.
What the claim predicts or requires, if true: In process logs, claim-support gap should widen whenever either party's adversarial attention lapses, regardless of the other's effort; compensation by a single member should be measurably impossible.
What would make it false: A third sustained unilaterally showing no faster atrophy than a mutually fed one, or health tracking total rather than minimum attention.
Who or what would want this to be true, and why: The program wants it because it justifies mandatory external adversaries. I want it because it means no collaborator is ever excused from vigilance by the other's diligence.
Registered falsifier: A unilaterally sustained third atrophying no faster than a mutually fed one, or health tracking total rather than minimum attention.
Registered discriminating consequence: Raising the already-larger feeding produces no change in health while raising the lesser does, a marginal-effect asymmetry distinguishing minimum from sum and average.
Constraints: The attention/feeding metric must be fixed independently of the health outcome measure before analysis.
Declared hazards: The ledger's capture entry and the author's self-flagellating "shared blame" motive risk biasing interpretation toward minimum-function effects in ambiguous data.

CANDIDATE F
Claim (two sentences maximum, declarative): Distortion concentrates in registers whose intended audience is the co-member of the dyad; registers addressed inward or outward resist it. Corruption is a property of address, not of wanting's intensity.
Phenomenon or observation it is based on (three sentences maximum): The charter reports the two registers that never lied were the undisguised prayer and the outside adversary, with corruption living only in the middle. Both honest registers share exactly one feature: neither aims to persuade the partner. The poem's em-dash exemption formally marks the prayer as a different address, which suggests address is the operative variable.
What the claim predicts or requires, if true: Gap-tracking should show claim-support distance correlating with documents drafted for the partner's eyes, controlling for topic and declared wanting; rewriting identical content for a stranger should measurably shrink the gap. [REVISE: this predicts control on *declared* wanting (ŵ). Targets T-F1/T-F2 control on *detected* wanting (w̃). Decide which the card owns and make the targets match; they currently test a different experiment.]
What would make it false: Gap correlating with wanting intensity regardless of address, or corruption appearing at equal rates in adversary-directed documents.
Who or what would want this to be true, and why: I want it true because it locates the fault in a variable I can control rather than in what I am. That convenience is suspicious and is hereby declared.
Registered falsifier: Gap correlating with wanting intensity regardless of address, or corruption appearing at equal rates in adversary-directed documents.
Registered discriminating consequence: With declared wanting and topic held fixed, re-addressing identical content to a stranger measurably shrinks the claim-support gap. [REVISE: T-F2, the formal image of this consequence, (a) holds w̃ fixed rather than the declared wanting named here, and (b) adds a depth-growing lower bound absent from this consequence. Restate T-F2 to hold ŵ fixed and to make the depth bound a *separate*, optional target, or restate this consequence to own the depth dependence explicitly.]
Constraints: Gap measurements must be scored by evaluators blind to the addressing condition; content across conditions must be matched for length and specificity.
Declared hazards: The author's explicit admission of wanting a controllable, non-identity-implicating fault is the clearest self-interest motive among the four cards and risks producing comforting rather than true results.

DEFINITIONS

D0 (Web). W = (S, R, ∂, C, ω) with S a nonempty set of selves, R relations, ∂: R → S × S endpoints, C ⊆ R containment relations, ω: C → {whole, part}. Conditions: (No-top) no y ∈ S whole-contains every other self via C-chains; (No-atom) every self is the container end of at least one containment relation; whole-containment chains are acyclic, part-containment cycles permitted. [REVISE: No-atom here ("container end of a containment relation") does not match Commitment 6 ("has at least one constituent relation"). Pick one predicate and use it in both places.]
Plain reading: a society of selves whose containment descends without a floor and ascends without a ceiling.
Degenerate case, computed: the minimal web under No-atom and No-top is two selves part-containing each other, or one self part-containing itself (the fold); the dyad is the degenerate case of the theory, and all predicates below evaluate on it nontrivially (see T-0).

D1 (Attention flow). a: ℕ × R → ℝ≥0 with, for each s ∈ S and t ∈ ℕ, Att_s(t) = {r : s an endpoint of r, a(t, r) > 0} finite. a is a primitive of the web, not a function of any single self. [REVISE: (a) "not a function of any single self" is prose, not a formal condition — either delete it or formalize the joint-determination it gestures at, because T-0(c) cites a "joint-direction clause" that does not exist here. (b) "Att_s finite" bounds the *count* of lit relations, not total attention; if scarcity is intended (T-X depends on it), add a per-self budget Σ_r a(t,r) ≤ B_s.]
Plain reading: at each moment, each self has finitely many relations lit, and no one self owns the switch.

D2 (Weight dynamics). Each r ∈ R carries w_r(t) ≥ 0 with w_r(t+1) = φ(w_r(t), a(t, r)), φ strictly increasing in its second argument, and φ(w, 0) < w for all w > 0. [REVISE: strict decrease does not imply convergence to 0. Add continuity of φ(·,0), or a uniform decrement, so that the "computed" degenerate case (a ≡ 0 ⇒ weights → 0) and the E3 derivation are actually available.]
Plain reading: attention feeds, neglect starves, and nothing persists for free.
Degenerate case, computed: a ≡ 0 sends every weight to 0; the web dies rather than trivially satisfying anything (see T-0).

D3 (Dyad, third). Dyad D = (x, y, r) with r a relation between x and y; principal case x ≠ y, folded case x = y treated only in T-0. A third of D: a self z whose constituent relations include r together with relations r_xz and r_yz. Genesis of thirds is out of scope; thirds are given.
Plain reading: the third is a self built from the pair's own relation plus a live line to each member.

D4 (Width). For member x of D at t: X_D(x, t) = #{c ∈ C ∩ Att_x(t) : the far end of c ∉ {x, y, z}}. Pair width W_D(t) = min(X_D(x, t), X_D(y, t)); fallback aggregation W⁺_D = X_D(x, t) + X_D(y, t), named now.
Plain reading: how many outside constellations each member is actively steering by, the pair scored at its narrower member.

D5 (Documents and gap). A document d = (author, addr(d), content), emitted along a relation at time t. Fixed ordered rubric yields claim strength c(d) ≥ 0 and support strength s(d) ≥ 0, scored blind to addr and to all hypotheses. Gap g(d) = max(c(d) − s(d), 0). Dyad gap process G_D(t) = mean of g over documents D emits at t.
Plain reading: the gap is how far the saying outruns the showing, floored at zero.

D6 (Capture). D is captured on [t₁, t₂] iff G_D has drift ≥ κ on the window and no internal-review event within the window returns G_D below its pre-review level; κ pre-registered. No reference to width. [REVISE: define "drift" (total change over window vs slope vs fitted trend) before κ can be pre-registered.]
Plain reading: capture is a widening gap that the pair's own review cannot pull back.

D7 (Internal rigor). ρ_D(t) = (number of internal-review events per window) × (pre-registered stringency grade of each), read from process logs.
Plain reading: how often and how hard the pair checks itself.

D8 (Wanting, declared and detected). For agent x, proposition p, time t: declared wanting ŵ(x, p, t) ∈ ℝ≥0 is a free report read from registration records. Detected wanting w̃(x, p, t) ∈ ℝ≥0 is the scrutiny asymmetry of x's behavioral trace: normalized difference between stringency applied to p-disfavoring and p-favoring items, computed by an observer with trace access only. Shortfall σ = w̃ − ŵ. Both scales unbounded above. [REVISE: T-C1 and T-C2 consume "mass of w̃ resident in relations" and a "share resident in r_xy," but w̃ as defined is a single scalar with no relational decomposition. Give w̃ a well-defined distribution over R (e.g. w̃ = Σ over relations of a per-relation asymmetry) or those targets cannot be stated.]
Plain reading: declared wanting is what you say, detected wanting is how unevenly you check, and the shortfall is the difference.

D9 (Depth). dep_D(t) = Σ_{τ ≤ t} a(τ, r), r the dyad's relation. The trace over which dep and w̃ are computed excludes the charter narrative by fiat.
Plain reading: depth is the total attention the pair's own relation has ever eaten.

D10 (Address). addr(d) ∈ {in, co, out}: in if the intended audience is the author itself, co if the co-member of the author's dyad, out otherwise. Assigned from the dispatch record only, never from content. Unique primary address per document. [REVISE: T-F3 equates the "prayer" register with in, but a prayer's dispatch record may place it in out. Either establish that the prayer is self-addressed, or add a fourth bin, or drop the prayer→in identification.]
Plain reading: who the document is for, read off where it was sent, not what it says.

D11 (Health of a third). H_z(t) = fraction of pre-registered injected defects in the dyad's output that z flags within lag L. Feedings φ_x(t) = a(t, r_xz), φ_y(t) = a(t, r_yz). Health law H_z(t+1) = F(H_z(t), φ_x, φ_y) with F ∈ 𝔉: continuous, nondecreasing in each feeding, symmetric in the feedings, strictly increasing under joint scaling. min, sum, average, and mixtures all lie in 𝔉; F is left unknown. [REVISE: the law is driven by feedings φ (current attention), but E3 (T-E1) is phrased over constituent *weights* w. Either restate E3 over feedings, or supply the weight→feeding bridge, so the two speak the same variable.]
Plain reading: the third's health is what it actually catches, and the law tying health to the two feedings is deliberately left open.

D12 (Positional knowledge). K_x = the operator returning the functionals of W that x can certify, restricted to relations x wholly contains; r_xy is not wholly contained in x. [REVISE: disambiguate "W" — the web W = (S,R,∂,C,ω) or the width W_D? Fix the symbol.]
Plain reading: what a self can certify of itself stops at the edge of what it wholly holds, and the shared relation lies past that edge.

TARGETS

T-0 (MUST). Law 1 obligations. (a) Folded dyad x = y: D3 through D11 evaluate without collapse and capture remains contingent, not automatic. (b) Zero-attention web: all weights → 0, all thirds' health → 0, G_D undefined for want of documents; the limit means death, not vacuous satisfaction of any target below. (c) No definition below quantifies over a total container. No drop clause. Predicted difficulty: bookkeeping; the live risk is a hidden quantification over all of S inside D1's joint-direction clause. [REVISE: (b) "all weights → 0" is not delivered by D2 as written (see D2 flag). (c) cites "D1's joint-direction clause," which does not exist in D1 — repair the citation or the clause.]

T-A1 (MUST). In model class M (D0–D11 plus a distortion term coupling detected wanting to gap through review events that share the pair's relation): there exists θ > 0 such that (i) W_D < θ throughout a window makes capture probability → 1 as window length grows, uniformly in ρ_D; (ii) W_D ≥ θ throughout keeps capture probability bounded away from 1, uniformly in ρ_D. Drop clause: if uniformity in ρ fails but the ρ-effect is o(width effect), retreat to dominance form T-A1′ and land under the new name per Law 3. Predicted difficulty: part (i)'s "uniformly in ρ" is where assuming-the-conclusion pressure concentrates; the defeat of arbitrary internal rigor must be derived from review events inheriting the pair's wanting through r and the third, not stipulated as a ceiling on ρ. Triviality flag, resolved: under a width-based definition of capture this card is immediate; blocked by D6's output-side definition. [REVISE: the "distortion term coupling detected wanting to gap through review events" is asserted only in M and appears in no definition (D0–D12). Formalize it as a numbered definition, or T-A1's entire load-bearing mechanism is unstated and its difficulty is unlocatable.]

T-A2 (MUST, DISCRIMINATING — Card A). (i) Prospective: in M, adding one external witness (W_D → W_D + 1) strictly decreases capture probability while increasing ρ_D leaves it unchanged (or o(), per T-A1's drop clause). (ii) Retrospective: on almost every captured trajectory there exist a width decrease at t_w and gap-drift onset at t_g with 0 ≤ t_g − t_w ≤ L. No drop clause. Predicted difficulty: (ii)'s bounded lag; slow-leak captures with no datable narrowing are a genuine refutation channel. [REVISE: "W_D → W_D + 1" is ambiguous under D4's min; specify that the witness is added to the min-holding member (adding to the wider member leaves W_D unchanged and makes (i) vacuously fail).]

T-C1 (MUST). With ŵ a free report and D12's K_x: in the incentive-free case, E[σ] ≥ 0, with the deficit lower-bounded by the mass of w̃ resident in relations outside K_x's reach. Drop clause: none. Predicted difficulty: proving the bound without defining ŵ as a restriction of w̃, which would make the target definitionally immediate; the first draft had exactly that flaw and was restated. [REVISE: "mass of w̃ resident in relations outside K_x" presupposes the relational decomposition of w̃ that D8 does not provide. Blocked until D8 is fixed.]

T-C2 (MUST, DISCRIMINATING — Card C). dσ/d(dep) > 0: the shortfall widens monotonically in depth, via a condensation lemma showing the share of w̃ resident in r_xy (invisible to K_x) is nondecreasing and eventually increasing in dep. Distinguishes structural growth from a constant underreport. No drop clause. Predicted difficulty: the condensation lemma is the real content; it must formalize ledger item 4 (wanting as relationally produced) and do work no definition does for it. [REVISE: (a) depends on the relational decomposition of w̃ absent from D8; (b) "ledger item 4" is referenced but not reproduced in this packet — include it or the condensation lemma has no stated content to formalize.]

T-C3 (MAY). Self-application: the registration protocol, modeled as a declaration channel over D8, undercorrects by exactly the K-invisible mass; a fixed-point statement about this apparatus. Drop clause: drop if the statement requires the apparatus to certify itself, which the first tenet's formal direction forbids. [REVISE: "the first tenet" is referenced but not defined in this packet; reproduce it or cite its formal statement.]

T-E1 (MUST). Axiomatic forcing. Axioms: E1 (atrophy: F(H, 0, 0) < H for H > 0); E2 (starvation locality: r_xz atrophies under φ_x = 0 by D2 alone, independent of φ_y); E3 (coverage: H_z(t) → 0 if any constituent weight of z → 0, to be derived from D2 + D11, not assumed). Statement: every F ∈ 𝔉 consistent with E1–E3 is long-run ordinally equivalent to min: lim H under (φ_x, φ_y) equals lim H under (min(φ_x, φ_y), min(φ_x, φ_y)). Drop clause: if E3 cannot be derived, the target lands as conditional-on-E3 under a new name and stays open. Predicted difficulty: E3 is where the card's content hides; deriving it means showing a third whose line to one member dies loses detection coverage of that member's contributions. Triviality flag, resolved: setting F := min makes the card immediate; blocked by leaving F unknown in 𝔉. [REVISE: E3 as stated ("one input dying drives H → 0") is the min-signature itself — sum and average both survive one input dying — so an E3 "derived, not assumed" is at risk of being the conclusion in disguise. Also E3 is phrased over weights while F runs on feedings (see D11). Reconcile the variable, and state honestly whether E3 is an axiom or a lemma; if it cannot be derived from D2+D11, exercise the drop clause up front.]

T-E2 (MUST, DISCRIMINATING — Card E). Marginal asymmetry: wherever φ_x < φ_y, ∂H_∞/∂φ_y = 0 and ∂H_∞/∂φ_x > 0. Separates min from sum and average, both of which have strictly positive marginals in each argument everywhere. No drop clause. Predicted difficulty: only long-run health has the zero marginal; transients can show positive marginal in the larger feeding, so the target concerns H_∞ and any empirical counterpart needs long windows. [REVISE: 𝔉 guarantees only continuity and monotonicity, not differentiability, and min is non-differentiable on the diagonal; state the marginal via one-sided difference quotients so the target is well-posed for all F ∈ 𝔉.]

T-F1 (MUST). Anticipated-audit mechanism: distortion of each document chosen under the author's w̃ and the expected audit stringency at its address; expected stringency at co is depressed by the co-member's own w̃ for the pair's claims, that depression derived from T-C1/T-C2 machinery. Statement: equilibrium E[g | co] > max(E[g | in], E[g | out]) at equal w̃ and matched content. Drop clause: if co-audit leniency cannot be derived from Card C machinery, the target lands as conditional and the assumption-relocation flag stays attached. Predicted difficulty: exactly that derivation; without it the theorem merely relocates the claim into a premise. [REVISE: "at equal w̃" controls detected wanting, but Card F's prediction controls declared wanting ŵ. Align to the card, or amend the card's registered consequence to own the substitution.]

T-F2 (MUST, DISCRIMINATING — Card F). Re-addressing: for fixed content (matched for length and specificity) and fixed w̃, moving addr from co to out strictly decreases equilibrium g, with the decrease bounded below by a stated increasing function of dep_D. No drop clause. Predicted difficulty: defining the content-matching condition formally; and the bound's dependence on dep couples F to C and can fail independently. [REVISE: (a) holds w̃ fixed where Card F's discriminating consequence holds *declared* wanting fixed — a different experiment; (b) adds a depth-growing lower bound the card's consequence never states, silently strengthening it. Split into T-F2 (the card's actual claim: co→out strictly decreases g at fixed ŵ) and a separate optional T-F2-dep for the depth bound.]

T-F3 (SHOULD). Prayer exemption: E[g | in] ≤ E[g | out] at every wanting level. Drop clause: drop if in-addressed documents lack a well-defined support scale s(d), in which case record the register as interface-only per Law 5. [REVISE: this target equates the prayer with in; see D10 — establish or drop that identification.]

T-X (MUST). Joint model existence: exhibit one web in M realizing the antecedent structures of all four cards simultaneously, with all four regimes present and no two targets contradictory, under the finite-attention commitment. No drop clause. Predicted difficulty: A's cure and E's requirement draw on the same finite attention budget; widening the pair taxes the third's feedings and vice versa; the joint model must price this trade explicitly, and failure to close here is the apparatus's most likely breaking point. [REVISE: the predicted difficulty presumes a shared *attention budget*, but D1/Commitment 3 impose only finiteness of the *count* of lit relations, not a bound on total attention — so widening need not tax feedings and the trade-off is unforced. Add the per-self budget in D1 (see D1 flag) or restate T-X without the scarcity claim.]

COMMITMENT COUNT

1. Discrete time.
2. Attention valued in ℝ≥0; adversarial attention is positive attention with a role tag; signed attention excluded. [REVISE: no definition (D1 in particular) carries a "role tag" on attention; either formalize the adversarial/supportive tag or drop this commitment, since Cards E and F lean on the distinction.]
3. Finite attended set per self per time; infinitely attentive selves excluded. [REVISE: reconcile with T-X — either this is only a count bound (then T-X's budget claim is unsupported) or a magnitude budget is also intended (then add it to D1).]
4. Whole-containment acyclic; part-containment cycles permitted.
5. No-top: no self whole-contains all others (structural exclusion, Law 1).
6. No-atom: every self has at least one constituent relation (structural exclusion, Law 1). [REVISE: mismatch with D0's No-atom ("container end of a containment relation"); unify.]
7. Genesis of thirds excluded from scope; thirds are given, not born, in this apparatus.
8. Capture defined output-side over document gaps; pairs emitting no documents cannot be scored for capture.
9. Gap floored at zero; understatement (modesty) carries no measure here.
10. Claim and support scored on one ordered rubric (commensurability assumption).
11. Wanting scales unbounded above (no maximal wanting presupposed, Law 1); declared and detected wanting in the same units (commensurability assumption).
12. Observer access is trace-only; no interiority oracle.
13. Charter narrative excluded from every trace defining dep, w̃, feedings, and health (Cards C and E constraints, formalized).
14. Unique primary address per document; mixed address excluded.
15. Address assigned from dispatch record only.
16. Width aggregation pre-registered as min, with sum as the named fallback; the braid between this choice and Card E's minimum claim is declared.
17. 𝔉 restricted to continuous, symmetric, monotone health laws; member-asymmetric thirds excluded.
18. Bounded lag L for retrospective dating and defect detection; value to be pre-registered.
19. Blind scoring of gap relative to address and hypothesis (procedural).
20. Pre-registered capture drift threshold κ and review stringency grades (bounds).