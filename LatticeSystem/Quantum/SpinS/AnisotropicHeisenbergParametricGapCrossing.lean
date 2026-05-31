import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import Mathlib.Topology.Order.IntermediateValue

/-!
# IVT crossing for the parametric gap `E_0(γ(t)) - E_M(γ(t))`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

If at the SU(2) point `(1, 0)` we have `E_0 < E_M` (strict gap, supplied by
Theorem 2.3) and at some target `(λ', D')` we have `E_M ≤ E_0`, then by
intermediate value theorem applied to the continuous gap function
`g(t) := E_0(γ(t)) - E_M(γ(t))` on `[0, 1]`, there is a crossing point
`t* ∈ [0, 1]` at which `E_0(γ(t*)) = E_M(γ(t*))`. This is brick (2-IVT-d)
of the obligation (2) deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **IVT crossing for the parametric gap**: if the gap `E_0 - E_M` is strictly
negative at `t = 0` (i.e., `E_0(1, 0) < E_M(1, 0)`) and non-negative at `t = 1`
(i.e., `E_M(λ', D') ≤ E_0(λ', D')`), then there exists a crossing
`t* ∈ [0, 1]` with `E_0(γ(t*)) = E_M(γ(t*))`.

This packages mathlib `intermediate_value_Icc` for the composed function
`t ↦ hermitianMinEigenvalue (Ĥ_M(γ(t))) - hermitianMinEigenvalue (Ĥ_0(γ(t)))`
on `[0, 1]`. -/
theorem anisotropicHeisenbergS_parametric_gap_crossing
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ)
    [Nonempty (magConfigS Λ N M)] [Nonempty (magConfigS Λ N 0)]
    (lam' D' : ℝ)
    (h0 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := 0) hJ 1 0) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h1 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam' D') ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := 0) hJ lam' D')) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := 0) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := by
  -- Abbreviate the per-sector min eigenvalue along the path.
  set E0 : ℝ → ℝ := fun t => hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := 0) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2)
  set EM : ℝ → ℝ := fun t => hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2)
  -- Continuous gap g(t) = E0(t) - EM(t).
  have hE0 : Continuous E0 :=
    continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
      (Λ := Λ) hJ N 0 lam' D'
  have hEM : Continuous EM :=
    continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
      (Λ := Λ) hJ N M lam' D'
  have hg : Continuous (fun t => E0 t - EM t) := hE0.sub hEM
  -- Endpoint values.
  have hpath0 := anisotropicHeisenbergParametricPath_zero lam' D'
  have hpath1 := anisotropicHeisenbergParametricPath_one lam' D'
  have hE0_0 : E0 0 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := 0) hJ 1 0) := by
    simp only [E0, hpath0]
  have hEM_0 : EM 0 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ 1 0) := by
    simp only [EM, hpath0]
  have hE0_1 : E0 1 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := 0) hJ lam' D') := by
    simp only [E0, hpath1]
  have hEM_1 : EM 1 = hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ lam' D') := by
    simp only [EM, hpath1]
  -- g(0) < 0, g(1) ≥ 0.
  have hg0 : E0 0 - EM 0 < 0 := by
    rw [hE0_0, hEM_0]; linarith
  have hg1 : 0 ≤ E0 1 - EM 1 := by
    rw [hE0_1, hEM_1]; linarith
  -- Apply mathlib intermediate_value_Icc on [0, 1] at y = 0.
  obtain ⟨t, htmem, hteq⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (hg.continuousOn : ContinuousOn (fun t => E0 t - EM t) (Icc (0 : ℝ) 1))
      ⟨le_of_lt hg0, hg1⟩
  refine ⟨t, htmem, ?_⟩
  -- hteq : E0 t - EM t = 0 ⟹ E0 t = EM t.
  exact sub_eq_zero.mp hteq

end LatticeSystem.Quantum
