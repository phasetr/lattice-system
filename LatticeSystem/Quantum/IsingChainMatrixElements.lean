import LatticeSystem.Quantum.IsingChain
import LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance

/-!
# Configuration-basis matrix elements of the open-chain quantum Ising Hamiltonian

Red-fixture skeleton for Tasaki Problem 3.3.a, *Physics and Mathematics of Quantum Many-Body
Systems*, p. 59 (solution pp. 498-501, eqs. (S.24)-(S.41)): the entries of
`quantumIsingHamiltonian N J h`, viewed as a matrix over configurations `Λ → Fin 2` with
`Λ = Fin (N + 1)`, in terms of the domain-wall bond count and `siteFlipAt`
(`LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance`).

This module is pure reuse (`quantumIsingHamiltonian`, `siteFlipAt`,
`onSite_pauliX_mulVec_apply`, `mulVec_basisVec_apply`); no new spin-flip or sign convention is
introduced (design §5 reuse plan). It currently contains **only these imports**, so that
`LatticeSystem/Tests/Problem33aLowEnergy.lean` can import a resolving module while its
signature-pin fixtures for the not-yet-implemented matrix-element lemmas
(`quantumIsingHamiltonian_mulVec_apply`, `quantumIsingHamiltonian_apply_diag`,
`quantumIsingHamiltonian_apply_siteFlip`, `quantumIsingHamiltonian_apply_eq_zero`) still fail on
the *identifier* (TDD Red). The four lemmas are added in follow-up commits of PR-005a.
-/
