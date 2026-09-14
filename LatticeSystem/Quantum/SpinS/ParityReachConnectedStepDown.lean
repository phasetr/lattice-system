import LatticeSystem.Quantum.SpinS.ConnectedRaiseLower
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBond
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIon
import LatticeSystem.Quantum.SpinS.ParityReachWitness
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.ParityReachStepDownFull

/-!
# Connected-graph step-down engine for parity-block reachability (scaffold)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-1 of the connectivity/reachability
arc. This module will hold the connected-graph analogue of the step-down lemmas used by the
complete-bipartite `_total` theorems (`BipartiteCompleteGraphStructural.lean`,
`ParityReachableNoParityBondTotal.lean`, `ParityReachableNoSingleIonTotal.lean`): given
`G.Connected` and `2 ≤ magSumS σ`, produce a strictly smaller-`magSumS` configuration reachable
from `σ` in each of the three relations (`ParityReachableS`, `IonParityReachableS`,
`BondParityReachableS`).

No declarations yet: this is a Red-fixture placeholder for TDD (see
`LatticeSystem/Tests/ParityReachabilityConnected.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/
