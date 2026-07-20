/-
`program-2/series-2/formal/P2S2/ws4.lean`

WS4 - Mutual reading without collapse (the genuinely-uncertain obligation, the knot). Program 2 Series 2 (2.2).

The genuinely open question: when two perspectives each read the other AND themselves, does the mutual reading
COLLAPSE them (recover one from the other), let one TOTALIZE the pair, or leave a RESIDUE. `ws4_mutual_residue`
bundles the honest fork on the witnessed mutual structure: (0) all four readings witnessed (the recursion
genuine); (1) the RESIDUE, load-bearing on MUTUALITY — a relatum `bnd` plain-bisimilar to `oth` (the collapse
engine, Series 07, the honest import structure) yet JOINTLY unattended by two INCOMPARABLE reaches (`bnd ∉
attendsR slf = {slf,oth,p}` AND `bnd ∉ attendsR oth = {slf,oth,q}`, `p ∈ slf∖oth`, `q ∈ oth∖slf`), so the mutual
reading, combining the two reaches, still subtracts it (the C2p2-R1 repair: both conjuncts biting); (2) the reading
order rank-constrained (not free/total, PR1-S1 foreclosed); (3) NOT COLLAPSE (the twoness non-recoverable); (4)
NOT TOTALIZED (the diagonal survives mutual inspection, a DISCLOSED companion, never the whole payoff). ONE and
TOTALIZED are pre-registered (WS5's verdict computes them for other structures). The coherence is NEVER decided.

Design docs: `program-2/series-2/spec/ws4-design.md`; shared objects `spec/README.md` §1-§5.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S2.ws3

universe u

namespace P2S2

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE MUTUAL RESIDUE (WS4, the knot).** On the witnessed mutual structure: (0) all four readings hold (the
recursion self reads other reads self is genuine); (1) the RESIDUE — `bnd` is plain-bisimilar to `oth` (the
collapse engine identifies all atomless relata, Series 07) yet in NEITHER the self's reach `{slf,oth,p}` NOR the
other's reach `{slf,oth,q}`, which are INCOMPARABLE (`p ∈ slf∖oth`, `q ∈ oth∖slf`), so both non-membership
conjuncts are load-bearing (`p` excluded only by the self's, `q` only by the other's) and the mutual reading,
combining two genuinely distinct reaches, subtracts `bnd` (the joint blind spot the mutuality cannot close, the
C2p2-R1 repair); (2) the reading order is rank-constrained (`bnd` strictly outranks what it reads); (3) NOT
COLLAPSE (the twoness `¬ Recoverable`, not ONE); (4) NOT TOTALIZED (no inspection is self-total, the diagonal
surviving mutual inspection — a DISCLOSED companion, structure-independent, never the whole payoff). The
mutuality is load-bearing in (1) via the two incomparable reaches; the coherence of the two readings is NEVER
decided (Series 2.3's question, charter §4.d). -/
theorem ws4_mutual_residue (hinf : ℵ₀ ≤ κ) :
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y)
        ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t) := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩, ?_, ?_,
          ws2_other_non_recoverable hinf,
          fun insp => ws1_no_self_total_hold (outDest hinf attendsR) insp⟩
  · exact ⟨bnd,
      ws1_atomless_bisim (outDest hinf attendsR) oth bnd (ws1_rcar_SHNE hinf oth) (ws1_rcar_SHNE hinf bnd),
      by decide, by decide⟩
  · intro z hz
    rw [attendsR_bnd] at hz
    fin_cases hz
    decide

end P2S2
