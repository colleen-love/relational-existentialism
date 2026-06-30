/-
# Route 1 of bridge B: the Lawvere diagonal *is* the trace — on a reflexive object, and why you need one

[`QuantumSeam`](../Scratch/QuantumSeam.lean) took bridge B by route 2 (no-broadcasting, on the finite
matrix `dephase`). Route 1 is the harder one: the **Lawvere diagonal itself** biting the trace. This
module builds its machinery and pins precisely where it is blocked — honestly, because route 1 is not
closed here, only sharpened.

The key object is a **reflexive object**: a point-surjective self-application `app : D → (D → B)` —
every observable `D → B` is `app d` for some `d` (i.e. `[D→B]` is a retract of `D`). On one:

* `reflexive_gives_fixpoint` — every observable `f : B → B` has a fixed point (this *is* `Mirror.lawvere`,
  a split point-surjection being point-surjective).
* `fixpoint_is_selfApplication` — and the fixed point is the **self-application** `app a a` — the
  feedback loop closed on itself, *Geometry-of-Interaction's `Y`*. So on a reflexive object the
  Lawvere diagonal **is** the trace/feedback: `f (app a a) = app a a`. This is the genuine content of
  route 1 — the diagonal and the trace coincide.
* `no_reflexive_self_trace` — contrapositive (the seam): a fixed-point-free observable `neg` ("the look
  that never settles") ⇒ **no reflexive object**, no complete reflexive self-trace. This is
  `Mirror.no_complete_selfModel`, read as the *trace* obstruction.

**Where route 1 is blocked — and it is a real wall, not a choice.** `no_reflexive_object_for_Bool`:
for a two-valued observable there is **no reflexive object in plain types** — no point-surjection
`D → (D → Bool)` exists (Cantor's diagonal: `not` has no fixed point). So a reflexive object cannot be
*finite* or *set-theoretic*; it requires a **non-classical** setting — domain-theoretic / GoI, where
`[D→D]` means **Scott-continuous** maps and `D ≅ [D→D]` genuinely holds (D∞). That construction —
exhibiting a reflexive object in a traced setting — is the **open** part of route 1; it is **not built
here**, and `matTracedSMC` (finite, compact) provably cannot host it.

**Honest status.** Route 1's *machinery* is mechanized (diagonal = trace on a reflexive object) and its
*precondition* is pinned (a reflexive object, impossible in Set/finite by Cantor, needing a reflexive
domain). What remains genuinely **`[open]`**: constructing a reflexive object in a traced/compact
category (an infinite-dimensional `D ≅ D* ⊗ D` or a Scott domain), which would let the diagonal bite an
actual trace. This is *not* the finite quantum `ptrace` — which, lacking a reflexive object, takes route
2 (no-broadcasting) instead. The two routes are the firewall's two faces: copyable/reflexive settings
get Lawvere-as-trace; compact-finite settings get no-broadcasting. Neither is new mathematics; the
contribution is locating the wall exactly.
-/
import RelExist.Mirror

namespace RelExist.ReflexiveSeam

open RelExist.Mirror

universe u v
variable {D : Type u} {B : Type v}

/-- **A reflexive object yields a fixed point for every observable** — Lawvere via the split
point-surjection `app`/`lam`. (This is `Mirror.lawvere`: `lam`/`hsplit` make `app` point-surjective.) -/
theorem reflexive_gives_fixpoint (app : D → D → B) (lam : (D → B) → D)
    (hsplit : ∀ g, app (lam g) = g) (f : B → B) : ∃ b, f b = b :=
  lawvere app (fun h => ⟨lam h, hsplit h⟩) f

/-- **The fixed point is the self-application — the trace IS the diagonal.** On a reflexive object the
fixed point of `f` is `app a a` (with `a := lam (fun d => f (app d d))`): the feedback loop closed on
itself, GoI's `Y`. So Lawvere's diagonal and the trace/feedback are *the same self-application*. -/
theorem fixpoint_is_selfApplication (app : D → D → B) (lam : (D → B) → D)
    (hsplit : ∀ g, app (lam g) = g) (f : B → B) :
    f (app (lam (fun d => f (app d d))) (lam (fun d => f (app d d))))
      = app (lam (fun d => f (app d d))) (lam (fun d => f (app d d))) := by
  have happ := hsplit (fun d => f (app d d))
  have h := congrFun happ (lam (fun d => f (app d d)))
  exact h.symm

/-- **The seam, route 1 (the contrapositive).** If some observable `neg` never settles
(`∀ b, neg b ≠ b`), there is **no reflexive object** — no complete reflexive self-trace. The self
cannot close its feedback loop on itself against a fixed-point-free observable. This is
`Mirror.no_complete_selfModel` read as the trace obstruction. -/
theorem no_reflexive_self_trace (neg : B → B) (hneg : ∀ b, neg b ≠ b) :
    ¬ ∃ app : D → D → B, PointSurjective app :=
  no_complete_selfModel neg hneg

/-- **Why route 1 cannot run in `Set`/finite models — Cantor.** For a two-valued observable there is
no reflexive object in plain types: no point-surjection `D → (D → Bool)` (since `not` has no fixed
point). So a reflexive object cannot be finite or set-theoretic; route 1 needs a domain-theoretic / GoI
setting (`D ≅ [D→D]`, continuous maps), which `matTracedSMC` lacks. The obstruction to *having* the
reflexive object is the same diagonal as the seam. -/
theorem no_reflexive_object_for_Bool :
    ¬ ∃ app : D → D → Bool, PointSurjective app :=
  no_complete_selfModel Bool.not (by decide)

end RelExist.ReflexiveSeam
