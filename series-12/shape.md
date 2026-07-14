The diagonal and the import share one shape — that's the central result of Series 12 (WS1, the "coincidence" workstream). The repo defines it once, in `series-12/formal/Series12/ws1.lean`:

```lean
def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c
```

So the shape of both is **the opening: `¬ realizable c`** — a parametric negation wrapper over a recoverability notion. What differs is which recoverability predicate each side plugs in, and from which quantifier direction it inhabits the shape:

**The diagonal (the residue side).** Here `realizable := ResidueRecoverable`, defined as `∃ h, insp h = residue insp` — the residue of an inspection is recoverable iff some hold's content realizes it. The residue itself is the diagonal content (`diag insp`), the Cantor/Russell/Gödel move: no inspection surjects onto the space of contents (`ws1_insp_not_surjective`), so the residue is distinct from every hold's content and `ws2_residue_free` proves `¬ ResidueRecoverable insp` — for *every* inspection. So the diagonal inhabits the opening **forced-for-all**: generated from within, universally non-recoverable.

**The import (the labelled side).** Here `realizable := Recoverable`, defined as `∀ R, IsBisim (plainOf dest) R → IsBisimL dest R` — a label is recoverable iff every plain (label-forgetting) bisimulation already respects the labels. The witness is `labelLoop`, the free directed hold where each state self-loops carrying its own index as its label; `ws4_labelLoop_not_recoverable` proves it fails the test. So the import inhabits the opening **exists-satisfying**: there exists a labelled distinction the plain relating cannot recover — required from without.

The coincidence theorem (`D2`, `ws1_shape_coincidence` region) proves both instantiations at once. And the repo is careful about what this does *not* say: the two `realizable` predicates are type-heterogeneous (one ranges over inspections, the other over labelled coalgebras), so "the import IS the residue" isn't even expressible — it's a coincidence of shape, not identity, and `D3` (`ws1_coincidence_not_identity_witness`) exhibits two pointwise-opposite inspections both inhabiting the opening, showing shared non-recoverability can't entail sameness.

In the program's own gloss: Series 07's fact (a differentiator must be imported) and the diagonal's fact (self-inspection leaves an uncapturable residue) turn out to be one outline — the structure produces, at its own edge, the exact shape of what it can neither derive nor contain.
