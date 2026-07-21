/-
`program-2/series-10/formal/P2S10.lean` — Program 2 Series 10 (2.10), THE REVERSAL (aggregator).

Imports the five workstreams. Series 2.10 is the second tier-1 probe of Phase 3 and the most consequential. It asks
the question underneath Series 2.7's result (the tick strictly RAISES the measure, keeps no ledger): does the tick have
an INVERTIBLE CORE — a sub-dynamics that is a measure-preserving bijection, one you could run BACKWARD — or is
reification irreversibly one-way at every scale? It adds exactly one thing to the imported chain: the invertibility
question about the BUILT tick (`tick x = reifyM {x}`), made precise as a measure-preserving bijection against the BUILT
rank (`mu = P2S7.rankM`), and the sharp distinction between a decodable SECTION and a genuine dynamical REVERSAL.

It finds, HONESTLY: the tick genuinely moves and raises the measure (WS1); the full tick is not a measure-preserving
bijection — non-injective under the collapse and rank-raising (WS2); the reification section DECODES the pattern but
does NOT preserve the measure, so decodability is strictly weaker than reversal, and the core criterion is the higher
bar — a rank-preserving bijection (WS3); and the fork is genuine — the criterion is satisfiable on the built rank (a
control swap has a core) yet the BUILT tick has NO nonempty measure-preserving bijective sub-dynamics (WS4). The
verdict is computed (WS5): `noCore` — the built tick raises the measure at every scale, the section only decodes, no
sub-dynamics can be run backward measure-preservingly. The arrow is fundamental (the NOT-RECOVERED specification): the
next iteration must add a reversible substrate beneath the tick, or accept fundamental irreversibility and recover
physics statistically. No inverse is smuggled; the decodable section is never passed off as a reversal.
-/
import P2S10.ws1
import P2S10.ws2
import P2S10.ws3
import P2S10.ws4
import P2S10.ws5
