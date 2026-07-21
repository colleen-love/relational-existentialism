# WS4 design — the fork (CONE vs NO-CONE) (2.9)

**Prove the fork on two carriers, both genuine, neither by fiat. A carrier with a genuine finite attention bound has a NON-TRIVIAL cone (a finite rate, some events inside and some outside — relativity's cone). A carrier whose reification is instantaneous (attention total) has a TRIVIAL cone (everything reachable at once — no finite speed). Both readings genuinely reachable from the SAME `rate`/`ball`, the verdict discriminating.**

## 1. Objects (shared, `spec/README.md` §2)

```
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S := ...
def rate (att : S → Finset S) : ℕ := ...
def attSlow : S → Finset S := ...    -- forward neighbor  (rate 1) — CONE
def attAll  : S → Finset S := fun _ => {0,1,2,3,4}   -- attend everyone (rate 4) — NO-CONE (instantaneous)
```

## 2. Payoff

```
-- CONE-REACHABLE: a genuine finite rate, a NON-TRIVIAL cone (some event strictly outside at depth 1).
theorem ws4_cone_reachable :
    rate attSlow = 1 ∧ (∃ y, y ∉ ball attSlow p0 1)

-- NO-CONE-REACHABLE: the reification is instantaneous — the cone is the whole world at depth 1 (no finite speed).
theorem ws4_nocone_reachable :
    (∀ y, y ∈ ball attAll p0 1)

-- (companion) the NO-CONE cone is literally everything.
theorem ws4_nocone_trivial :
    ball attAll p0 1 = Finset.univ
```

`ws4_cone_reachable`: `decide` (rate 1; `p4 ∉ ball attSlow p0 1`). `ws4_nocone_reachable`: `decide` (rate attAll = 4; `dist p0 y ≤ 4` for all `y`). `ws4_nocone_trivial`: `decide`.

## 3. Triage

- **Both sides genuine, no fiat (audit b).** CONE is not built into `ball` (attAll gives `univ`); NO-CONE is not built in (attSlow leaves `p4` outside). Same `rate`, same `ball`, same `dist` — only the directed attention differs. The verdict discriminates on the attention-world.
- **The CONE side (charter WS4 `ws4_cone_reachable`).** `attSlow` has a finite rate (1) and a non-trivial cone (`p4` outside) — a genuine finite speed, relativity's cone.
- **The NO-CONE side (charter WS4 `ws4_nocone_reachable`).** `attAll` (total attention) reifies the whole world in one tick: the cone at depth 1 is `univ`, no event causally disconnected — the honest non-relativistic pole ("instantaneous, every event reachable at once"), reported, not relabelled.
- **Earned, not smuggled.** Both rates are `univ.sup (span att)` (WS1); neither is a postulated `c`. The NO-CONE rate is LARGE because the attention is total, not because a ceiling was chosen.
- **Strip test.** Delete "cone"/"light"/"speed": `ws4_cone_reachable` is "a `dist`-`sup` is 1 and some `univ` element fails the depth-1 filter"; `ws4_nocone_reachable` is "every `univ` element passes the depth-1 filter" — bare facts about `attSlow`/`attAll`.
- **Outcome class.** Cone reachable ⇒ `coneReachable = true`; nocone reachable ⇒ `noconeReachable = true`. Both true ⇒ `cone` (the fork genuine, CONE recovered), by WS5.
- **Names (audit e).** The definitions are `ball`, `rate`, `attSlow`, `attAll`; the theorem names `ws4_cone_reachable`, `ws4_nocone_reachable` are underscore-wrapped (grep-safe). No forbidden identifier.
