import LatticeSystem.Quantum.HeisenbergLattice
import LatticeSystem.Quantum.GibbsState.Covariance

/-!
# Heisenberg-lattice expectation companions: 2D (foundation)

The 2D square-lattice and 2D square-torus Heisenberg Gibbs expectation companions, each a
one-line specialization of a generic primitive in `Quantum/GibbsState.lean` /
`Quantum/GibbsState/Covariance.lean` to the concrete index types
`Fin (N + 1) × Fin (N + 1)` and `Fin (N + 2) × Fin (N + 2)`.

The 3D cubic-lattice companions live in `Companions.lean`, which imports this module.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## 2D square-lattice Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem squareLatticeHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareLatticeCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) × Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (squareLatticeCoupling N J)) A

/-- For Hermitian `O`, `(⟨O⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O).im
      = 0 :=
  gibbsExpectation_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- Conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J) * A
          - A * heisenbergHamiltonian (squareLatticeCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (squareLatticeCoupling N J)) A

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β n

/-- Energy variance is real: `(Var_β(H)).im = 0`. -/
theorem squareLatticeHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β

/-! ## 2D square-torus Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem squareTorusHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareTorusCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) × Fin (N + 2) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (squareTorusCoupling N J)) A

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem squareTorusHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        ((heisenbergHamiltonian (squareTorusCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (squareTorusHeisenberg_isHermitian N J) hA hB β

end LatticeSystem.Quantum
