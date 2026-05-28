import LatticeSystem.Quantum.SpinS.DressedAxisSwapHermitian
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.ParityConfig
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Parity-block submatrix Hermiticity

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.1): the parity-`p` submatrix of the bare and dressed axis-swapped Hamiltonians inherits
Hermiticity from the full Hamiltonian via `Matrix.IsHermitian.submatrix`. This is the
starting point for Hermitian spectral analysis of the per-sector matrix — needed to
identify the per-sector PF eigenvalue as the spectrum minimum and ultimately to bridge
the conditional `≤ 2` (g/h chains) to the unconditional ground-state degeneracy bound.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Hermiticity of the bare `Ĥ'` parity-`p` submatrix** for real couplings. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ) :
    ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1)).IsHermitian := by
  have hHerm := axisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
    (J := J) (lam := lam) (D := D)
    (fun x y => by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJ x y)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD)
  exact hHerm.submatrix (fun σ : parityConfigS Λ N p => σ.1)

/-- **Hermiticity of the dressed `Ĥ'` parity-`p` submatrix** for real couplings. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ) :
    ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1)).IsHermitian :=
  (dressedAxisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N) A
    hJ hlam hD).submatrix (fun σ : parityConfigS Λ N p => σ.1)

end LatticeSystem.Quantum
