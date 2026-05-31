import LatticeSystem.Quantum.SpinS.AxisSwapGaugeEquiv
import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import LatticeSystem.Quantum.SpinS.MatrixSimilaritySpectrum
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg

/-!
# `hermitianMinEigenvalue` agrees on `Ĥ` and `Ĥ'` (axis-swap bridge)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) IVT crossing argument.

For the anisotropic Hamiltonian `Ĥ = anisotropicHeisenbergS J λ D N` and its
axis-swapped image `Ĥ' = axisSwappedAnisotropicHeisenbergS J λ D N`, related by
the axis-swap unitary `U = G.tensor Λ` via `Ĥ' = U · Ĥ · U⁻¹`, their minimum
eigenvalues coincide:
`hermitianMinEigenvalue Ĥ = hermitianMinEigenvalue Ĥ'`.

Composes:
- `tensor_conj_anisotropicHeisenbergS` (PR #3752, gauge equivalence).
- `matrix_similar_spectrum_real_eq` (existing, similarity preserves real spectrum).
- `hermitianMinEigenvalue_eq_of_spectrum_eq` (PR #3863, min eigenvalue
  spectrum-equality-invariance).

This is the bridge that lets PR #3888's obligation (1) bound — stated at the
axis-swapped `Ĥ'`'s per-parity min — be transferred to the original `Ĥ`'s
global min, the form needed by the obligation (2) IVT crossing argument's
final algebraic step.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

namespace AxisSwapUnitaryS

variable (G : AxisSwapUnitaryS N)

include G in
/-- **Spectrum equality `Ĥ` ↔ `Ĥ'` (axis-swap)**: under the gauge equivalence
`Ĥ' = U · Ĥ · U⁻¹`, the real spectra of `Ĥ` and `Ĥ'` coincide. -/
theorem anisotropic_axisSwapped_spectrum_real_eq (J : Λ → Λ → ℂ) (lam D : ℂ) :
    spectrum ℝ (anisotropicHeisenbergS (Λ := Λ) J lam D N) =
      spectrum ℝ (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N) := by
  -- Ĥ = Uinv · Ĥ' · U  (rearrange `tensor_conj_anisotropicHeisenbergS`).
  have hsim : anisotropicHeisenbergS (Λ := Λ) J lam D N =
      G.tensorInv Λ * axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N * G.tensor Λ := by
    have := G.tensor_conj_anisotropicHeisenbergS J lam D
    -- this : tensor * H * tensorInv = axisSwapped
    -- Multiply both sides by tensorInv on left and tensor on right:
    -- tensorInv * (tensor * H * tensorInv) * tensor = tensorInv * axisSwapped * tensor
    -- Using tensorInv * tensor = 1 and tensorInv * tensor = 1:
    -- (tensorInv * tensor) * H * (tensorInv * tensor) = tensorInv * axisSwapped * tensor
    -- 1 * H * 1 = tensorInv * axisSwapped * tensor
    have hL : G.tensorInv Λ * (G.tensor Λ * anisotropicHeisenbergS J lam D N * G.tensorInv Λ) *
        G.tensor Λ =
        G.tensorInv Λ * axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N * G.tensor Λ := by
      rw [this]
    rw [show G.tensorInv Λ *
          (G.tensor Λ * anisotropicHeisenbergS J lam D N * G.tensorInv Λ) * G.tensor Λ =
        (G.tensorInv Λ * G.tensor Λ) * anisotropicHeisenbergS J lam D N *
          (G.tensorInv Λ * G.tensor Λ) by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      simp only [Matrix.mul_assoc]] at hL
    rw [G.tensorInv_mul_tensor, Matrix.one_mul, Matrix.mul_one] at hL
    exact hL
  -- Apply the similarity-preserves-spectrum lemma with U := G.tensor, Uinv := G.tensorInv.
  exact (LatticeSystem.Quantum.matrix_similar_spectrum_real_eq
    G.tensor_mul_tensorInv G.tensorInv_mul_tensor hsim).symm

include G in
/-- **`hermitianMinEigenvalue` agrees on `Ĥ` and `Ĥ'` (axis-swap)**: for the
anisotropic Hamiltonian at real `(J, λ, D)`, the min eigenvalue of `Ĥ` equals
the min eigenvalue of the axis-swapped `Ĥ'`. -/
theorem hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    {lam : ℂ} (hlam : star lam = lam) {D : ℂ} (hD : star D = D)
    [Nonempty (Λ → Fin (N + 1))] :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) hJ hlam hD N) =
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) hJ hlam hD N) :=
  hermitianMinEigenvalue_eq_of_spectrum_eq
    (anisotropicHeisenbergS_isHermitian_of_real hJ hlam hD N)
    (axisSwappedAnisotropicHeisenbergS_isHermitian_of_real hJ hlam hD N)
    (G.anisotropic_axisSwapped_spectrum_real_eq J lam D)

end AxisSwapUnitaryS

end LatticeSystem.Quantum
