import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.LagrangeFormula
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationInput

/-!
# Tasaki Problem 2.5.c: lifted z-axis rotation commutation

This module supplies the concrete Hamiltonian-side input for the
phase-invariant Problem 2.5.c wrappers: the lifted spin-`S` z-axis rotation
commutes with the Heisenberg Hamiltonian.  The proof identifies the tensor
product rotation with the exponential of the total `Ŝ_tot^(3)` generator and
then uses the existing Heisenberg commutator with `Ŝ_tot^(3)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace Complex

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Diagonal forms -/

/-- The single-site z-axis spin-`S` rotation is diagonal in the standard basis. -/
theorem spinSRot3_eq_diagonal (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ =
      Matrix.diagonal
        (fun k : Fin (N + 1) =>
          NormedSpace.exp (-((θ : ℂ) * Complex.I) * spinSOp3Eigen N k)) := by
  unfold spinSRot3
  rw [spinSOp3_eq_diagonal_eigen, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext k' k
  by_cases h : k' = k
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Pi.coe_exp]
    rw [Pi.smul_apply, smul_eq_mul]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-- The total z-spin operator is diagonal with eigenvalue `magEigenvalueS`. -/
theorem totalSpinSOp3_eq_diagonal_magEigenvalueS :
    totalSpinSOp3 V N = Matrix.diagonal (magEigenvalueS (Λ := V) (N := N)) := by
  ext σ' σ
  by_cases h : σ' = σ
  · subst h
    rw [totalSpinSOp3_apply_diag, Matrix.diagonal_apply_eq]
  · rw [totalSpinSOp3_apply_off_diag h, Matrix.diagonal_apply_ne _ h]

/-- The total z-spin exponential is diagonal with exponent
`-iθ * magEigenvalueS σ`. -/
theorem exp_smul_totalSpinSOp3_eq_diagonal (θ : ℝ) :
    NormedSpace.exp (-((θ : ℂ) * Complex.I) • totalSpinSOp3 V N) =
      Matrix.diagonal
        (fun σ : V → Fin (N + 1) =>
          NormedSpace.exp (-((θ : ℂ) * Complex.I) * magEigenvalueS σ)) := by
  rw [totalSpinSOp3_eq_diagonal_magEigenvalueS, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  ext σ' σ
  by_cases h : σ' = σ
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Pi.coe_exp]
    rw [Pi.smul_apply, smul_eq_mul]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

omit [DecidableEq V] in
/-- The sum of single-site `Ŝ³` eigenvalues is the total magnetization eigenvalue. -/
theorem sum_spinSOp3Eigen_eq_magEigenvalueS (σ : V → Fin (N + 1)) :
    (∑ x : V, spinSOp3Eigen N (σ x)) = magEigenvalueS σ := by
  unfold spinSOp3Eigen magEigenvalueS magSumS
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  push_cast
  rw [nsmul_eq_mul]
  ring

omit [DecidableEq V] in
/-- Product form of the diagonal entries of the lifted z-axis rotation. -/
theorem prod_spinSRot3_diag_eq_total_exp (θ : ℝ) (σ : V → Fin (N + 1)) :
    (∏ x : V,
        NormedSpace.exp (-((θ : ℂ) * Complex.I) * spinSOp3Eigen N (σ x))) =
      NormedSpace.exp (-((θ : ℂ) * Complex.I) * magEigenvalueS σ) := by
  rw [← NormedSpace.exp_sum]
  congr 1
  rw [← Finset.mul_sum, sum_spinSOp3Eigen_eq_magEigenvalueS]

/-- The lifted tensor z-axis rotation is the exponential of total z-spin. -/
theorem manyBodyTensorS_spinSRot3_eq_exp_totalSpinSOp3 (θ : ℝ) :
    manyBodyTensorS (fun _ : V => spinSRot3 N θ) =
      NormedSpace.exp (-((θ : ℂ) * Complex.I) • totalSpinSOp3 V N) := by
  ext σ' σ
  rw [manyBodyTensorS_apply, exp_smul_totalSpinSOp3_eq_diagonal]
  by_cases h : σ' = σ
  · subst h
    simp_rw [spinSRot3_eq_diagonal, Matrix.diagonal_apply_eq]
    exact prod_spinSRot3_diag_eq_total_exp (θ := θ) σ'
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ x)]
    rw [spinSRot3_eq_diagonal, Matrix.diagonal_apply_ne _ hx]

/-! ## Hamiltonian commutation -/

/-- The spin-`S` Heisenberg Hamiltonian commutes with the lifted z-axis rotation. -/
theorem heisenbergHamiltonianS_commute_manyBodySpinSRot3
    (J : V → V → ℂ) (θ : ℝ) :
    Commute (heisenbergHamiltonianS J N)
      (manyBodyTensorS (fun _ : V => spinSRot3 N θ)) := by
  rw [manyBodyTensorS_spinSRot3_eq_exp_totalSpinSOp3]
  have hcomm : Commute (heisenbergHamiltonianS J N) (totalSpinSOp3 V N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp3 J N)
  exact (hcomm.smul_right (-((θ : ℂ) * Complex.I))).exp_right

end LatticeSystem.Quantum
