import LatticeSystem.Quantum.HeisenbergLattice.CompanionsCore

/-!
# Heisenberg-lattice expectation companions: 3D cubic lattice

The 3D cubic-lattice Heisenberg Gibbs expectation companions,
each a one-line specialization of a generic primitive in
`Quantum/GibbsState.lean` / `Quantum/GibbsState/Covariance.lean`
to the concrete index type
`(Fin (N + 1) × Fin (N + 1)) × Fin (N + 1)`.

The 2D square-lattice and 2D square-torus companions live in
`CompanionsCore.lean`, which this module imports.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## 3D cubic-lattice Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem cubicLatticeHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (cubicLatticeCoupling N J)) A
      = ((Fintype.card
            ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) → Fin 2) : ℂ))⁻¹
          * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (cubicLatticeCoupling N J)) A

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        ((heisenbergHamiltonian (cubicLatticeCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J)
    (cubicLatticeHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ)
    {A B : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (cubicLatticeHeisenberg_isHermitian N J) hA hB β

/-- Rényi-n trace identity. -/
theorem cubicLatticeHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((cubicLatticeHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (cubicLatticeCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (cubicLatticeCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (cubicLatticeCoupling N J)) n

end LatticeSystem.Quantum
