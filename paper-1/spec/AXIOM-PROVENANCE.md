# paper-1 — axiom & lemma provenance

**Status (handoff XXI): thin layer over `theory/`.** The proof-DAG reorg made paper one a thin layer: the
band layer (`RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`) was genuinely double-imported (paper one
**and** paper two), so it **promoted** into clean `Theory.*` and paper one now **imports** it (the import that
spec XX found namespace-blocked — that block is now gone). The matrix substrate (`MatrixModel`,
`PartialTrace`) moved to `foundation/`. Paper one keeps its own `P1.x` (the seam, lived identity, the arrow);
its energy headline (`band_coincidence_from_axioms`, `undifferentiated_two_term_from_axioms`) now lives at
its canonical `Theory.BandFromAxioms.*` address. **Footprint-checked identical** to pre-reorg at the Phase-2
checkpoint. Node inventory: [`theory/spec/NODES.md`](../../theory/spec/NODES.md). The historical "canonical
home" framing below is retained for provenance.

> *Note (`CanonicalEigenform`).* It was the spec-XX collision workaround; Phase 2 dissolved the collision, so
> it is now **redundant** with `Theory.Axioms.eigenform_of_fixed` and is a candidate for deletion (paper one
> importing `Theory.Axioms` directly). Kept this phase to preserve the green+footprint baseline.

---

**Historical (handoff XIII): canonical home of its own closure.** Under the lazy-fork discipline, paper one's
modules were *not* forked from `theory/` — they lived here canonically, frozen, and `theory/` forked *forward*
from here. (Superseded by XXI's unification, above.)

- **Canonical here (frozen):** paper one's axiom spine (`RelExist.Mirror/Relating/Seam/SeamBridge`,
  aggregator `RelExist`) and its kept mathlib closure (`Scratch.*`, aggregator `Scratch`). Module names are
  byte-for-byte the pre-reorg names; only file *locations* and six import lines changed in the reorg.
- **Imported (not forked):** `foundation/` — the traced-SMC typeclass (`Foundation.Traced`), at `fe935a6`.
  Safe to import: `foundation` only generalizes (backward-compatible), toward an eventual mathlib PR.
- **Forked *out* of here (by `theory/`, on demand):** `Theory.We`, `Theory.RotatingSpectrum`,
  `Theory.BandCoincidence`, `Theory.BandFromAxioms` are frozen copies `theory/` took from this root at
  `fe935a6` because its frontier modules (`Priority`, `MutualCoupling`) consume them. They may now diverge;
  see `theory/spec/PROVENANCE.md` for the drift note. This root does not depend on those copies.

**Deliberately divergent (future):** when `theory/`'s axiom readings move ahead of paper one's
(A3 = `νΦ_c`-at-trace-limit here vs. the modular/phase-bearing reading in `theory/`), this file records the
split per affected module. **Intended identical (today):** everything, because no divergence has landed yet.

**Drift check:** diff this root's `Scratch.*`/`RelExist.*` against the corresponding `theory/` forks; any
*accidental* difference in an "intended identical" module is a bug to reconcile, any *deliberate* one is the
sequel's content and belongs in the list above.

## Canonical axiom layer — pin and the eigenform's upgraded status (handoff XX)

Handoff XX **reframed A3 as a process** — *relations co-direct attention asymmetrically in the relata*, with
per-relatum capacity `α` — and **derived** the per-paper readings of the self as theorems of that one
process, canonically in the **canonical axiom layer** [`Theory.Axioms`](../../theory/formal/Theory/Axioms.lean)
(prose: [`theory/spec/AXIOMS.md`](../../theory/spec/AXIOMS.md)). The collapse is total: existence, the
eigenform (this paper), the generative engine, and the modular self all derive (`Theory.Axioms`, outcome 1).

- **Pin.** Paper one is proved against the **canonical axiom layer** `Theory.Axioms` as of **handoff XX**
  (branch `claude/normalize-canonical-axioms-wyg8xq`). The layer changes **only backward-compatibly**
  (generalization, never redefinition), so this pin keeps meaning what it meant — the same discipline that
  makes `foundation/` safe.

- **The eigenform is now *derived*, not posited.** Paper one's self `νΦ_c` / `Peri(Φ_c)` was previously **A3
  read at the strength of its text** (the `C1` reading — *"the self **is** `Peri`"*, [`02-axioms.md`](02-axioms.md)
  §A3). Under the reframe it is the **fixed point of a faithful A3 process** — a theorem
  (`Theory.Axioms.eigenform_of_fixed`), mirrored in this root's own namespace as
  [`Scratch.CanonicalEigenform.eigenform_of_sustained`](../formal/Scratch/CanonicalEigenform.lean). **C1's
  status moves from `[reading]` to `[derived]`; the last faithfulness caveat closes.**

- **Consumed by citation + pin, not import — the namespace exception.** A literal `import Theory.Axioms` into
  this root is **structurally blocked**: the `theory/` forks share this root's `RelExist.*` namespace (the
  fork-and-freeze gave them paper-one's names so they would stay byte-identical), so importing both `Scratch.*`
  and the transitively-required `Theory.*` forks collides (`environment already contains
  'RelExist.RotatingSpectrum.Ucoh'`). Because the forks are **byte-identical** to this root's modules (drift
  check above), the canonical theorem certifies *this* root's exact eigenform object; paper one therefore
  consumes it by citation + pin and re-proves the state-half locally in `Scratch.CanonicalEigenform` — the
  same way paper two cites paper one's arrow. The change is **purely additive**: no existing theorem is
  touched, so the headline arrow/energy footprints are **unchanged** (still `[propext, Classical.choice,
  Quot.sound]` — verified on `TimeFlow.Flow.coh_orbit_antitone`,
  `BandFromAxioms.band_coincidence_from_axioms`, `BandFromAxioms.undifferentiated_two_term_from_axioms`).

- **Reversal of the freeze (handoff XX, Part C).** Spec XIII protected a per-paper A3 *divergence* by frozen
  duplication. That divergence is now **gone** (the readings are one process's consequences), so the freeze
  shifts from *duplication* to **version-pinning**: this root keeps its byte-identical forks as the pinned
  copy (the namespace exception above blocks unifying them by import), and pins the canonical layer here.
