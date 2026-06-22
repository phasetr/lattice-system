import LatticeSystem.Quantum.HeisenbergLattice
import LatticeSystem.Quantum.GibbsState.Covariance

/-!
# Heisenberg-lattice expectation companions: 2D (foundation)

Foundational layer extracted from `Companions.lean` for build speed.  This file collects
the 2D square-lattice and 2D square-torus Heisenberg expectation companion lemmas.

The 3D cubic-lattice Heisenberg expectation companions are kept in the capstone module
`Companions.lean`.
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

/-- For Hermitian `O`, `(⟨H · O⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- `(⟨H^2⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (squareLatticeHeisenberg_isHermitian N J) hA hB β

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (squareLatticeHeisenberg_isHermitian N J) hA hB β

/-- Energy variance is real: `(Var_β(H)).im = 0`. -/
theorem squareLatticeHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem squareLatticeHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- Rényi-n trace identity: `Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem squareLatticeHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((squareLatticeHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (squareLatticeCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (squareLatticeCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (squareLatticeCoupling N J)) n

/-! ## 2D square-torus Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem squareTorusHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareTorusCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) × Fin (N + 2) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (squareTorusCoupling N J)) A

/-- For Hermitian `O`, `(⟨O⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O).im
      = 0 :=
  gibbsExpectation_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- Conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J) * A
          - A * heisenbergHamiltonian (squareTorusCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (squareTorusCoupling N J)) A

/-- For Hermitian `O`, `(⟨H · O⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- `(⟨H^2⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        ((heisenbergHamiltonian (squareTorusCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β

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

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (squareTorusHeisenberg_isHermitian N J) hA hB β

/-- Energy variance is real. -/
theorem squareTorusHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem squareTorusHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- Rényi-n trace identity. -/
theorem squareTorusHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((squareTorusHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (squareTorusCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (squareTorusCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (squareTorusCoupling N J)) n

end LatticeSystem.Quantum
