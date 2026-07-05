/-
Spec 2.5 — the D19 formal pack, S1_ω, and the closing theorems of Series 2.

Normative source: `series-2/2-5.md` (§1 D19, §2 D25, §5 the formal content, §6 frozen
predictions) and the work order `2-5-mechanization-a.md`. Continues `Spec24g.lean` (the whole
corrected-universe chain). Specs win.

STANDING DISCIPLINE (2-5-mechanization-a): the D19 register is now written and citable, but
**no proof term below depends on D19 for its mathematics** — the naming is interpretation over
proved structure. If any theorem needed D19 as a hypothesis, that would be a category error; none
does. Doc-comments carry the interpretive readings; the proof terms do not.

D25 GLOSSARY (the verb emendation, doc-side; no proof term or declaration renames — 2.5 §2).
Under D25 the primitive's verb is **know**, not observe. Legacy identifiers keep their names; read
them under acquaintance, not spectation:
  * `Reveal`/`RevealC`  — what a knowing returns of itself (the threefold payload), not "what is
    observed".
  * `ctx`/`ctxC`        — the context/aperture of a knowing.
  * `contextsC_differ`  — two hosts *know* a shared relation differently (barrier two).
  * `HasObjEndpointΩ`, `ApproxW`, etc. — knowing-local structure. The mathematics is unmoved; the
    interpretation moves truer. The 2.0 prose sweep (A8's wording, §2.4 headers, D10) is spec-side.
-/
import Spec24g

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 1 — the D19 formal pack (2.5 §5; the naming's machine-checked content) -/

/-- **V1 (the vanishing)** — 2.5 §5, FP-D1. At saturation the set-remainder is EMPTY: when the
context of `r` at `x` spans the whole pattern, `remC x r = ∅`. This is the honesty lemma that
forces the *stratified reading* of D19(b): at the one locus where the residue lives — self-
reference, where `ctxC = pat` (`saturationC`) — loss cannot be edge-shaped. Nothing is *missing*;
the loss is pure fog (the inexhaustibility of `selfKnowing_inexhaustible`), not a determinate
set-remainder. -/
theorem rem_empty_at_saturation (A : RawC) (x : A.O) (r : A.R)
    (hsat : ctxC A x r = A.pat x) : remC A x r = ∅ := by
  show A.pat x \ RevealC A x r = ∅
  rw [Set.diff_eq_empty, RevealC, hsat]
  exact Set.subset_insert r (A.pat x)

/-- One step of constitutive descent among relations: `r` occurs one level inside `s`'s unfolding
(as a relation endpoint). The corrected `Desc` (cf. Spec21d), on the relation sort. -/
def DescC (r s : ΩR) : Prop := Sum.inr r ∈ ZΩC.endpoints s

/-- **P-D19-1 (inexhaustibility / the fog, as theorem)** — 2.5 §5, FP-D1. The tower of self-
knowing never terminates: over a self-anchored knowing `r` (one that knows itself, `SelfAnchoredC`),
constitutive descent admits a chain of *every* finite depth — the ascent restricted to the self-
anchored locus, with T6's seriality (Spec21d's `desc_chain` idiom, ascended to the corrected
functor). At every order of self-knowing there is a further turning; nothing is missing at any
order, something is unclosable at every order. This is D19(b)'s fog made precise. -/
theorem selfKnowing_inexhaustible (r : ΩR) (hsa : SelfAnchoredC ZΩC r) :
    ∀ n : ℕ, ∃ c : Fin (n + 1) → ΩR, c 0 = r ∧
      ∀ i : Fin n, DescC (c i.succ) (c i.castSucc) :=
  fun _ => ⟨fun _ => r, rfl, fun _ => hsa⟩

/-- **P-D19-2 (privacy / inaccessibility)** — 2.5 §5, FP-D2. The residue appears in no knowing's
payload — including the being's own. Concretely: a relation `r` unshared with `w` (`r ∉ pat w`)
lies in NO `Reveal` of `w` (of any relation `s` that `w` knows). Asking `w`'s self-knowing to
deliver `r` is asking the payload to contain what the payload is defined against (feature 2, 3). -/
theorem residue_private (A : RawC) (w : A.O) (r s : A.R)
    (hrw : r ∉ A.pat w) (hsw : s ∈ A.pat w) : r ∉ RevealC A w s := by
  intro hmem
  rw [RevealC, Set.mem_insert_iff] at hmem
  rcases hmem with rfl | hmem
  · exact hrw hsw
  · exact hrw (ctxC_subset A w s hmem)

/-- What `x` receives, by hearsay through `z`, about a relation `s` that `z` knows: the part of
`z`'s context of `s` that `x` already shares. The corrected `received` (cf. Spec22a), bounded by
acquaintance. -/
def receivedC (A : RawC) (x z : A.O) (s : A.R) : Set A.R := ctxC A z s ∩ A.pat x

/-- The acquaintance bound: hearsay through `z` carries only what `x` already holds. -/
theorem receivedC_bound (A : RawC) (x z : A.O) (s : A.R) : receivedC A x z s ⊆ A.pat x :=
  fun _ h => h.2

/-- **P-D19-3 (non-transmissibility)** — 2.5 §5, FP-D2. No hearsay chain assembles another's
self-anchored tower: the residue is on the wrong side of every boundary. A relation `r` unshared
with `x` (`r ∉ pat x`) is in nothing `x` receives about `z`'s knowing — hearsay is bounded by
shared boundaries at every step (T13's acquaintance bound, applied). Feature 4. -/
theorem residue_nontransmissible (A : RawC) (x z : A.O) (r s : A.R)
    (hrx : r ∉ A.pat x) : r ∉ receivedC A x z s :=
  fun h => hrx (receivedC_bound A x z s h)

/-- **T19 (the transcendental theorem)** — 2.5 §5, FP-D3. The Mirror and the Forcing Lemma,
packaged as one citable statement: **(i)** any derived-division signature over the point collapses
(`forcing_lemma` — no self-referential loss-generator ⟹ the fiber is a subsingleton), and **(ii)**
the boolean-shadow universe IS a single point (`omega_collapse`, T17). Together: *no residue, no
many.* Modus tollens (doc-side, not a hypothesis of any proof): the world is manifestly many;
therefore the residue exists. The sheer plurality of the world is evidence for D19 (feature 6). -/
theorem T19_no_residue_no_many :
    (∀ (α : Type) [Subsingleton α] (P : Set α → Prop) (ι : Set α → Type),
      Subsingleton (RelEx.Trials.DivisionData α P ι))
    ∧ (∀ x y : RelEx.TwoSorted.Ω₀, x = y) :=
  ⟨fun α _ P ι => RelEx.Trials.forcing_lemma α P ι, RelEx.TwoSorted.omega_collapse⟩

/-! ## Stage 2 — S1 at the ω-tier (2.5 §5, FP-D4) -/

/-- **S1_ω** — FP-D4. At the ω-tier the finitude of deep holds is TRIVIAL: `pat x` is finite by
boundedness, so any hold within it is finite.

SAID LOUDLY, as the order demands: this is **scaffold-borrowed** content — the finiteness is the
D4 κ-loan's ω-instance, not an intrinsic bound. The real, contentful S1 is the κ-form, conditional
on T11 material (the loan's discharge attempt, `depth_bound_of_no_total`, still open). **R3's
warning stands: S1 was the most-wantable resolution, and triviality at ω is not vindication.** -/
theorem S1_omega (x : ΩO) : (ZΩC.pat x).Finite := bounded_ZΩC x

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms rem_empty_at_saturation
#print axioms selfKnowing_inexhaustible
#print axioms residue_private
#print axioms residue_nontransmissible
#print axioms T19_no_residue_no_many
#print axioms S1_omega
end AxiomAudit
