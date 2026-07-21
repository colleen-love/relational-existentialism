/-
`program-2/series-7/formal/P2S7.lean` — Program 2 Series 7 (2.7), THE LEDGER (aggregator).

Imports the five workstreams. Series 2.7 asks whether the universe keeps a ledger. It DEFINES a self-relative
measure of distinction `Q := rankM` (WS1, the risky ground, de-risked on paper first — non-trivial, the difference a
genuine import). It then finds, HONESTLY, that the measure is NOT conserved: the tick strictly RAISES it (WS2, the
arrow), and `rankM` is not plain-bisimulation-invariant, so the only conserved measures are trivial (WS3, no
ledger); the rise is genuine internally-manufactured import-content (WS4, all creation, on the P1 diagonal). The
verdict is computed (WS5): MONOTONE-ONLY — the universe has an arrow and keeps no conserved ledger, even locally.
(An earlier landing computed CONSERVED-RELATIVE; the Tier-1 landing review found that a costume — the "in-sight
conservation" was the collapse engine identifying the states, not a `Q`-invariance — and the series was reground to
the honest MONOTONE-ONLY. See `charter-status.md` finding T1-S1.)
-/
import P2S7.ws1
import P2S7.ws2
import P2S7.ws3
import P2S7.ws4
import P2S7.ws5
