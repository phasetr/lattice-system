import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg

/-!
# Gauge equivalence of the anisotropic and axis-swapped Hamiltonians

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

An `AxisSwapUnitaryS` is a single-site `π/2` rotation about axis 1: an invertible `U` with
`U Ŝ¹ U⁻¹ = Ŝ¹`, `U Ŝ² U⁻¹ = Ŝ³`, `U Ŝ³ U⁻¹ = −Ŝ²`.  Lifting it to the many-body tensor
unitary `Θ_U = ⊗_x U` and using the single-site conjugation (#3751), the anisotropic
Hamiltonian (2.5.14) is carried to its axis-swapped image (2.5.15):
`Θ_U Ĥ Θ_{U⁻¹} = Ĥ'`.  By the similarity invariant (#3746) the two then have equal
ground-state degeneracy — this is the gauge step of Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.15).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- A single-site **axis-swap unitary** (`π/2` rotation about axis 1): invertible `U` with
`U Ŝ¹ U⁻¹ = Ŝ¹`, `U Ŝ² U⁻¹ = Ŝ³`, `U Ŝ³ U⁻¹ = −Ŝ²`. -/
structure AxisSwapUnitaryS (N : ℕ) where
  /-- The single-site unitary. -/
  U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  /-- Its inverse. -/
  Uinv : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  /-- `U Uinv = 1`. -/
  U_mul_Uinv : U * Uinv = 1
  /-- `Uinv U = 1`. -/
  Uinv_mul_U : Uinv * U = 1
  /-- `U Ŝ¹ U⁻¹ = Ŝ¹`. -/
  conj_spinSOp1 : U * spinSOp1 N * Uinv = spinSOp1 N
  /-- `U Ŝ² U⁻¹ = Ŝ³`. -/
  conj_spinSOp2 : U * spinSOp2 N * Uinv = spinSOp3 N
  /-- `U Ŝ³ U⁻¹ = −Ŝ²`. -/
  conj_spinSOp3 : U * spinSOp3 N * Uinv = -spinSOp2 N

namespace AxisSwapUnitaryS

variable (G : AxisSwapUnitaryS N)

/-- The many-body lift `Θ_U = ⊗_x U`. -/
noncomputable def tensor (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : ManyBodyOpS Λ N :=
  manyBodyTensorS (fun _ : Λ => G.U)

/-- The inverse many-body lift `Θ_{U⁻¹} = ⊗_x U⁻¹`. -/
noncomputable def tensorInv (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : ManyBodyOpS Λ N :=
  manyBodyTensorS (fun _ : Λ => G.Uinv)

/-- `Θ_{U⁻¹} Θ_U = 1`. -/
theorem tensorInv_mul_tensor : G.tensorInv Λ * G.tensor Λ = 1 := by
  rw [tensorInv, tensor, manyBodyTensorS_mul]
  simp only [G.Uinv_mul_U]
  exact manyBodyTensorS_one

/-- Conjugation by `Θ_U` distributes over products. -/
theorem tensor_conj_mul (P Q : ManyBodyOpS Λ N) :
    G.tensor Λ * (P * Q) * G.tensorInv Λ =
      (G.tensor Λ * P * G.tensorInv Λ) * (G.tensor Λ * Q * G.tensorInv Λ) := by
  rw [show (G.tensor Λ * P * G.tensorInv Λ) * (G.tensor Λ * Q * G.tensorInv Λ)
      = G.tensor Λ * P * (G.tensorInv Λ * G.tensor Λ) * (Q * G.tensorInv Λ) by
    simp only [mul_assoc], tensorInv_mul_tensor]
  simp only [mul_one, mul_assoc]

/-- Conjugation by `Θ_U` of a single-site operator. -/
theorem tensor_conj_onSiteS (z : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    G.tensor Λ * onSiteS z A * G.tensorInv Λ = onSiteS z (G.U * A * G.Uinv) := by
  rw [tensor, tensorInv, manyBodyTensorS_conj_onSiteS G.U_mul_Uinv]

/-- `Θ_U` carries the XXZ bond term to the axis-swapped bond term. -/
theorem tensor_conj_spinSDotXXZ (x y : Λ) (lam : ℂ) :
    G.tensor Λ * spinSDotXXZ x y lam N * G.tensorInv Λ = spinSDotXXZSwap x y lam N := by
  rw [spinSDotXXZ, spinSDotXXZSwap]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    G.tensor_conj_mul, G.tensor_conj_onSiteS, G.conj_spinSOp1, G.conj_spinSOp2,
    G.conj_spinSOp3, onSiteS_neg, neg_mul_neg]
  abel

/-- `Θ_U` carries the single-ion `(Ŝ³)²` term to the axis-swapped `(Ŝ²)²` term. -/
theorem tensor_conj_singleIonAnisotropyS (D : ℂ) :
    G.tensor Λ * singleIonAnisotropyS D N * G.tensorInv Λ = singleIonAnisotropyS2 (Λ := Λ) D N := by
  rw [singleIonAnisotropyS, singleIonAnisotropyS2, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [G.tensor_conj_mul, G.tensor_conj_onSiteS, G.conj_spinSOp3, onSiteS_neg, neg_mul_neg]

/-- **Gauge equivalence**: `Θ_U Ĥ Θ_{U⁻¹} = Ĥ'` (the anisotropic Hamiltonian (2.5.14) is
carried to its axis-swapped image (2.5.15)). -/
theorem tensor_conj_anisotropicHeisenbergS (J : Λ → Λ → ℂ) (lam D : ℂ) :
    G.tensor Λ * anisotropicHeisenbergS J lam D N * G.tensorInv Λ =
      axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N := by
  rw [anisotropicHeisenbergS, axisSwappedAnisotropicHeisenbergS, Matrix.mul_add, Matrix.add_mul,
    G.tensor_conj_singleIonAnisotropyS]
  congr 1
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, G.tensor_conj_spinSDotXXZ]

end AxisSwapUnitaryS

end LatticeSystem.Quantum
