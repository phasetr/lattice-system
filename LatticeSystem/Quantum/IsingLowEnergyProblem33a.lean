import LatticeSystem.Quantum.IsingChainMatrixElements

/-!
# The `2L`-dimensional low-energy basis of Tasaki Problem 3.3.a

Red-fixture skeleton for Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Problem 3.3.a (statement p. 59, solution pp. 498-501), eqs. (S.24)-(S.30): the `2L`-dimensional
low-energy space spanned by `|Φ↑⟩`, `|Φ↓⟩`, `|Φ_j^↑↓⟩`, `|Φ_j^↓↑⟩` (`j = 1, …, L - 1`) for the
open-chain quantum Ising Hamiltonian `quantumIsingHamiltonian N (1/4) (λ/2)` on `L = N + 1`
sites, and its compression to that space (the `2L × 2L` matrix `lowEnergyMatrix`), which the
source shows equals `E_GS^(0)` plus a *tight-binding ring on the basis labels* `ZMod (2 * (N +
1))` — **not** a physically periodic lattice; the underlying chain stays open
(`LatticeSystem.Quantum.IsingChainMatrixElements`, design §2/§9 pitfall P1).

This module currently contains **only this import**, so that
`LatticeSystem/Tests/Problem33aLowEnergy.lean` can import a resolving module while its
signature-pin and numeric fixtures for the not-yet-implemented `2L`-basis API
(`lowEnergyConfig`, `wallSite`, `lowEnergyConfig_natCast_le`, `lowEnergyConfig_natCast_add`,
`lowEnergyConfig_injective`, `lowEnergyConfig_succ_eq_siteFlipAt`,
`lowEnergyConfig_ne_of_not_adjacent`, `lowEnergyMatrix`, `ringPotential`, `tightBindingRing`,
`lowEnergyMatrix_eq_add_tightBindingRing`) still fail on the *identifier* (TDD Red). These
declarations are added in follow-up commits of PR-005b.
-/
