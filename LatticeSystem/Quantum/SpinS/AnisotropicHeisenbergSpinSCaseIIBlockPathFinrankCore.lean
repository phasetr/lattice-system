import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIPathGlobalFinrank
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS

/-!
# Case (ii) block-path finrank: path-global bound (foundation)

Foundational layer extracted from `AnisotropicHeisenbergSpinSCaseIIBlockPathFinrank.lean` for build
speed.  This file proves the path-global `finrank` bound from parity-block path bounds.

The case-(ii) target wrappers from parity-block path bounds are kept in the capstone module
`AnisotropicHeisenbergSpinSCaseIIBlockPathFinrank.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Path-global finrank from parity-block path bounds -/

/-- **General spin-S case-(ii) path-global `finrank <= 2` input from
axis-swapped parity-block submatrix simplicity**.

The block-sum theorem is valid at an arbitrary eigenvalue `μ`; here `μ` is
chosen to be the full Hermitian minimum at each point of the deformation path.
Thus two pathwise block-simplicity hypotheses provide the exact path-global
`finrank <= 2` callback required by
`anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_global_finrank_bound`. -/
theorem caseII_path_global_finrank_bound_of_axisSwapped_submatrix_blocks_le_one
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJself : ∀ x, J x x = 0)
    {lam D : ℝ}
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_even :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1)
    (h_odd :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 := by
  intro t ht
  exact anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one_general
    (Λ := Λ) (N := N) (J := J) hJself
    ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
    ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)
    (h_even t ht) (h_odd t ht)

end LatticeSystem.Quantum
