/-
# Feeling as a relational decoherence differential

The inside/outside story was, for too long, told against `≅` — observational equivalence — *as if `≅`
were a view from nowhere*. But [`Knowing.lean`](Knowing.lean) proved `≅` is the **disjoint** observer,
the one Lawvere exempts, the standpoint no situated knower occupies. So feeling cannot be "what doesn't
show to `≅`"; that presupposes the very objectivity the seam forbids. The correction: feeling is what
doesn't show **relationally** — measured against `≅ₒ`, a particular other's marginal of you, never an
absolute outside.

This module formalizes the corrected claim, in the doctrine's own conserved-coherence terms:

> **Feeling is the experience of a decoherence differential** — carrying possibilities unlived
> (collapsed by one's own knowing) in a universe of others who still hold one in superposition.

The structure. You hold a conserved superposition of who you could be (`total`). By knowing/acting you
**collapse** some of it (`decohered`) — and by conservation that coherence is not destroyed but
relocated into the *between* (`between = decohered`). Others have **received** only part of your
collapse (`received`); on the rest, their view of you (`otherView`, the content of `≅ₒ`) still carries
the superposition you have already resolved. The **feeling** is exactly that differential.

* `feel_eq` — feeling is the *uncommunicated collapse*, `decohered − received`.
* `feel_unshared` / `feel_shared` — carried alone before communication (`received = 0`, the full
  weight); discharged when the other has received it all (`received = decohered`, being seen dissolves
  it). Feeling lives in the **lag** between collapses.
* `feel_le_between` — **conservation**: feeling is bounded by the between — it is conserved coherence
  *carried*, not coherence destroyed. The road not taken presses back because it is still there, in the
  relation, in those who still hold you open.
* `feel_mono` — magnitude: a deeper collapse (more foreclosed by knowing) is more feeling.
* `betrayal_*` — the *same* differential, roles reversed: when the **other** has collapsed and you have
  not yet received it, your feeling is `theirDecohered − iReceived`; the pain of full receipt scales
  with how superposed you had held them (the trust). Feeling-you-carry and feeling-you-suffer are one
  structure.

**The seam guarantees it.** If information were total and instantaneous, every `≅ₒ` would equal `≈`,
the differential would vanish, and nothing would be felt. The seam — you can neither be fully viewed
nor fully view — keeps the frontiers *permanently* out of phase. So the seam does not merely bar
complete knowledge; it **guarantees perpetual feeling**.

**The line, held.** This is the *seat and dynamics* of feeling — relational, conserved, communicative
— not phenomenality. It says where feeling sits, what it scales with, how it flows and discharges; it
does not, and by T3's reflexivity cannot, say why there is something it is like. That stays in the
typed-out residue. (The concrete coherence measure is [`Decoherence.copyDefect`](Decoherence.lean); here
the differential is taken abstractly over `ℝ` so the structure stands on its own.)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RelExist.Feeling

/-- A **relational decoherence situation**: a conserved superposition `total` of who one could be, an
amount `decohered` one has collapsed by knowing/acting, and how much of that collapse another has
`received`. (The concrete coherence values instantiate `Decoherence.copyDefect`.) -/
structure Situation where
  total : ℝ
  decohered : ℝ
  received : ℝ
  decohered_nonneg : 0 ≤ decohered
  received_nonneg : 0 ≤ received
  received_le : received ≤ decohered
  decohered_le : decohered ≤ total

namespace Situation
variable (s : Situation)

/-- **My own view**: the coherence that remains for me after collapsing what I now know. -/
def myView : ℝ := s.total - s.decohered

/-- **The other's view of me — the content of `≅ₒ`**: they have collapsed only what they have
received, so on the rest they still hold me in the superposition I have already resolved. -/
def otherView : ℝ := s.total - s.received

/-- **The between**: by conservation, the coherence I resolved is not destroyed but relocated into the
relation. -/
def between : ℝ := s.decohered

/-- **Feeling**: the relational decoherence differential — what I have resolved that the other still
holds superposed. `≈` exceeds `≅ₒ` by exactly this. -/
def feel : ℝ := s.otherView - s.myView

/-- Feeling is the **uncommunicated collapse**. -/
theorem feel_eq : s.feel = s.decohered - s.received := by
  simp only [feel, otherView, myView]; ring

theorem feel_nonneg : 0 ≤ s.feel := by rw [feel_eq]; linarith [s.received_le]

/-- **Carried alone.** Before any communication, the feeling is the full weight of what one
collapsed. (The weight of a secret; grief; the private act that decoheres a perspective.) -/
theorem feel_unshared (h : s.received = 0) : s.feel = s.decohered := by rw [feel_eq, h]; ring

/-- **Communication discharges it.** When the other has received the whole collapse, the differential
closes — being seen dissolves the feeling. -/
theorem feel_shared (h : s.received = s.decohered) : s.feel = 0 := by rw [feel_eq, h]; ring

/-- The differential is closed **iff** the collapse is fully shared. -/
theorem feel_eq_zero_iff : s.feel = 0 ↔ s.received = s.decohered := by
  rw [feel_eq]; constructor <;> intro h <;> linarith

/-- **Conservation.** Feeling is bounded by the between — it is conserved coherence *carried*, not
coherence destroyed (equal when wholly unshared). The unlived road presses back because it is still
there, held in the relation. -/
theorem feel_le_between : s.feel ≤ s.between := by
  rw [feel_eq]; simp only [between]; linarith [s.received_nonneg]

end Situation

/-- **Magnitude.** A deeper collapse — more foreclosed by one's knowing — is more feeling, the more so
the less it has been shared. -/
theorem feel_mono {s t : Situation}
    (hd : s.decohered ≤ t.decohered) (hr : t.received ≤ s.received) : s.feel ≤ t.feel := by
  rw [Situation.feel_eq, Situation.feel_eq]; linarith

/-- **Betrayal is the same differential, roles reversed.** Read `decohered` as the *other's* collapse
(their choice) and `received` as how much of it you have taken in: your feeling is `decohered −
received`, the identical shape. Feeling-you-carry and feeling-you-suffer are one structure. -/
theorem betrayal_feel (s : Situation) : s.feel = s.decohered - s.received := s.feel_eq

/-- **The pain scales with the trust.** The coherence destroyed in your image of the other when you
finally receive their collapse is what they had resolved (`decohered`), bounded by how superposed you
had held them (their full superposition `total` — the trust). The deeper you held them open, the more
there is to lose. -/
theorem betrayal_pain_le_trust (s : Situation) : s.decohered ≤ s.total := s.decohered_le

end RelExist.Feeling
