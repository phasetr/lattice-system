import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuousReal
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorIsHermitianReal
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath

/-!
# Continuity of `(λ, D) ↦ hermitianMinEigenvalue Ĥ(λ, D)` (full Hamiltonian)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For real-coupling `J` and real `(λ, D)`, the **global** min eigenvalue
`hermitianMinEigenvalue Ĥ(λ, D)` of the FULL anisotropic Hamiltonian is
continuous on `ℝ × ℝ`. Parallel of PR #3957 (`hermitianMinEigenvalue (Ĥ_M(λ, D))`
continuity, sector version) but applied to the full Hamiltonian — the input
needed by the first-crossing argument's sup analysis.

Composes:
- `continuous_anisotropicHeisenbergS_real` (existing, entry-wise Ĥ continuity).
- `anisotropicHeisenbergS_isHermitian_of_real` (existing, full Ĥ Hermitian).
- `Continuous.hermitianMinEigenvalue_comp` (PR #3953, Lipschitz-composition).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Hermitian instance of full Ĥ at real `(λ, D)`. -/
theorem anisotropicHeisenbergS_full_isHermitian_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N : ℕ) (lam D : ℝ) :
    (anisotropicHeisenbergS (Λ := Λ) J ((lam : ℂ)) ((D : ℂ)) N).IsHermitian :=
  anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
    hJ (star_ofReal_eq lam) (star_ofReal_eq D)

/-- **Full-Hamiltonian global min eigenvalue continuity in real `(λ, D)`**: the
function `(λ, D) ↦ hermitianMinEigenvalue (Ĥ(λ, D))` is continuous on `ℝ × ℝ`. -/
theorem continuous_anisotropicHeisenbergS_full_minEigenvalue_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y) (N : ℕ)
    [Nonempty (Λ → Fin (N + 1))] :
    Continuous (fun p : ℝ × ℝ => hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N p.1 p.2)) :=
  Continuous.hermitianMinEigenvalue_comp
    (continuous_anisotropicHeisenbergS_real J N)
    (fun p => anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N p.1 p.2)

/-- **Composed continuity along the parametric path**: the function
`t ↦ hermitianMinEigenvalue (Ĥ(γ(t)))` is continuous on `ℝ`. -/
theorem continuous_anisotropicHeisenbergS_full_minEigenvalue_alongParametricPath
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y) (N : ℕ)
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ) :
    Continuous (fun t : ℝ => hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2)) :=
  (continuous_anisotropicHeisenbergS_full_minEigenvalue_real (Λ := Λ) hJ N).comp
    (continuous_anisotropicHeisenbergParametricPath lam' D')

end LatticeSystem.Quantum
