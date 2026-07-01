import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import Mathlib.Topology.Order.IntermediateValue

/-!
# Generic-`M_0` IVT crossing for the parametric gap `E_{M_0}(γ(t)) - E_M(γ(t))`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Generalisation of the PR #3959 `M_0 = 0` parametric gap crossing (since
removed) to an arbitrary ground sector `M_0`. Needed by the actual Tasaki
§2.5 Theorem 2.4 application with `M_0 = balanced = |Λ|·N/2` (the
centered-zero sector that contains the symmetric GS).

Proof structure identical to PR #3959; only the sector label is parameterised.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Generic-`M_0` IVT crossing for the parametric gap**: if the gap `E_{M_0} - E_M`
is strictly negative at `t = 0` (i.e., `E_{M_0}(1, 0) < E_M(1, 0)`) and non-negative
at `t = 1` (i.e., `E_M(λ', D') ≤ E_{M_0}(λ', D')`), then there exists a crossing
`t* ∈ [0, 1]` with `E_{M_0}(γ(t*)) = E_M(γ(t*))`. -/
theorem anisotropicHeisenbergS_parametric_gap_crossing_generic
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_0 M : ℕ)
    [Nonempty (magConfigS Λ N M)] [Nonempty (magConfigS Λ N M_0)]
    (lam' D' : ℝ)
    (h0 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ 1 0) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h1 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam' D') ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ lam' D')) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_0) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := by
  set EM0 : ℝ → ℝ := fun t => hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_0) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2)
  set EM : ℝ → ℝ := fun t => hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2)
  have hEM0 : Continuous EM0 :=
    continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
      (Λ := Λ) hJ N M_0 lam' D'
  have hEM : Continuous EM :=
    continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
      (Λ := Λ) hJ N M lam' D'
  have hg : Continuous (fun t => EM0 t - EM t) := hEM0.sub hEM
  have hpath0 := anisotropicHeisenbergParametricPath_zero lam' D'
  have hpath1 := anisotropicHeisenbergParametricPath_one lam' D'
  have hEM0_0 : EM0 0 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_0) hJ 1 0) := by simp only [EM0, hpath0]
  have hEM_0 : EM 0 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ 1 0) := by simp only [EM, hpath0]
  have hEM0_1 : EM0 1 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_0) hJ lam' D') := by simp only [EM0, hpath1]
  have hEM_1 : EM 1 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ lam' D') := by simp only [EM, hpath1]
  have hg0 : EM0 0 - EM 0 < 0 := by rw [hEM0_0, hEM_0]; linarith
  have hg1 : 0 ≤ EM0 1 - EM 1 := by rw [hEM0_1, hEM_1]; linarith
  obtain ⟨t, htmem, hteq⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (hg.continuousOn : ContinuousOn (fun t => EM0 t - EM t) (Icc (0 : ℝ) 1))
      ⟨le_of_lt hg0, hg1⟩
  refine ⟨t, htmem, ?_⟩
  exact sub_eq_zero.mp hteq

end LatticeSystem.Quantum
