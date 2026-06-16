import LatticeSystem.Quantum.SpinS.ParityReachToMinMagSum
import LatticeSystem.Quantum.SpinS.ParityReachableWithinSector
import LatticeSystem.Quantum.SpinS.ParityReachableSymm
import LatticeSystem.Quantum.SpinS.ParityReachableMagSum

/-!
# Full `ParityReachableS` totality on the bipartite complete graph

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`parityReachableS_total_legacy`: for any two configurations sharing the same total-magnetization
parity
(`magSumS σ ≡ magSumS σ' (mod 2)`), `ParityReachableS` connects them.

This closes the (d.3) reachability totality plan by chaining:
1. `parityReachableS_to_min_magSum` (#3822) on each side to reach sector-min canonical
   (`magSumS < 2`).
2. Parity preservation (`parityReachableS_magSumS_parity_eq`, #3786) forces the two sector-min
   canonicals to have equal `magSumS` (∈ {0, 1} as dictated by the shared parity).
3. Within-sector reachability lift (`parityReachableS_bipartiteCompleteGraph_of_eq_magSumS`,
   #3817) connects the two same-`magSumS` canonicals.
4. `ParityReachableS` symmetry (#3816) reverses the second side's chain.
5. Compose via `ParityReachableS.trans`.

This is exactly the totality hypothesis needed by the parity-block matrix irreducibility theorem
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total` (#3797),
discharging (e) PR5 of Tasaki §2.5 Theorem 2.4 obligation (1).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

end LatticeSystem.Quantum
