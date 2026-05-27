import LatticeSystem.Quantum.SpinS.AxisSwapGaugeEquiv
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank

/-!
# Equal ground-state degeneracy of the anisotropic and axis-swapped Hamiltonians

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Given an `AxisSwapUnitaryS`, the gauge equivalence `Θ_U Ĥ Θ_{U⁻¹} = Ĥ'` (#3752) and the
similarity invariant (#3746) give that every `μ`-eigenspace of the anisotropic Hamiltonian
(2.5.14) and of its axis-swapped image (2.5.15) have equal dimension.  This is the bridge
that transfers the parity-sector Perron–Frobenius degeneracy bound (proved on `Ĥ'`) back to
the original `Ĥ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

namespace AxisSwapUnitaryS

variable (G : AxisSwapUnitaryS N)

/-- `Θ_U Θ_{U⁻¹} = 1`. -/
theorem tensor_mul_tensorInv : G.tensor Λ * G.tensorInv Λ = 1 := by
  rw [tensor, tensorInv, manyBodyTensorS_mul]
  simp only [G.U_mul_Uinv]
  exact manyBodyTensorS_one

include G in
/-- **Equal degeneracy**: every `μ`-eigenspace of the anisotropic Hamiltonian and of its
axis-swapped image have equal dimension. -/
theorem anisotropic_axisSwapped_eigenspace_finrank_eq (J : Λ → Λ → ℂ) (lam D : ℂ) (μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) =
      finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) := by
  have hsim : axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N =
      G.tensor Λ * anisotropicHeisenbergS J lam D N * G.tensorInv Λ :=
    (G.tensor_conj_anisotropicHeisenbergS J lam D).symm
  exact matrix_similar_eigenspace_finrank_eq G.tensorInv_mul_tensor G.tensor_mul_tensorInv hsim μ

end AxisSwapUnitaryS

end LatticeSystem.Quantum
