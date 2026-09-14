import LatticeSystem.Quantum.SpinS.ParityReachConnectedStepDown
import LatticeSystem.Quantum.SpinS.ParityReachableWithinSector
import LatticeSystem.Quantum.SpinS.ParityReachableSymm

/-!
# Connected-graph totality of parity-block reachability (scaffold)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-1 of the connectivity/reachability
arc. This module will hold the connected-graph capstones
`parityReachableS_total_of_connected`, `ionParityReachableS_total_of_connected` and
`bondParityReachableS_total_of_connected`: on a graph `G` with `G.Connected` (plus `Nontrivial V`
for the bond-only relation), any two configurations of equal `magSumS`-parity are related. Unlike
their complete-bipartite counterparts (`parityReachableS_total`,
`ionParityReachableS_total`, `bondParityReachableS_total`), these carry **no** bipartiteness or
balanced-sublattice hypothesis: reachability is purely graph-theoretic and does not need them.
The complete-bipartite trio is not superseded — the two families take different graph arguments
and both remain in use.

No declarations yet: this is a Red-fixture placeholder for TDD (see
`LatticeSystem/Tests/ParityReachabilityConnected.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/
