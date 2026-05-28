import LatticeSystem.Quantum.SpinS.AxisSwapAnisotropicImZero
import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.MarshallSign

/-!
# Real entries of the Marshall-dressed axis-swapped `Ĥ'` under real coefficients

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f.3-finish) step 2: the Marshall-dressed axis-swapped Hamiltonian has all-real entries under
real coefficients, by lifting the bare `axisSwappedAnisotropicHeisenbergS_apply_im_zero` (#3829)
through multiplication by the real (`±1`) Marshall sign factors.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Marshall-dressed `Ĥ'` entries are real under real coefficients**: `dressed σ τ =
marshallSignS A σ * marshallSignS A τ * (axisSwapped J lam D N) σ τ` has imaginary part zero
since each Marshall sign is `±1` (real) and the bare `axisSwapped` entry is real (#3829). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_im_zero
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0) (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0)
    (σ τ : Λ → Fin (N + 1)) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ τ).im = 0 := by
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply]
  simp [Complex.mul_im, marshallSignS_im,
    axisSwappedAnisotropicHeisenbergS_apply_im_zero hJim hJself hlam hDim]

end LatticeSystem.Quantum
