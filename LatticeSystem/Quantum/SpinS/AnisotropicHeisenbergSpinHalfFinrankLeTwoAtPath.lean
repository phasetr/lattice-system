import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergGlobalMinFinrankLeTwo
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPathStaysInRegion

/-!
# Spin-1/2 `Ĥ` eigenspace `finrank ≤ 2` at `hermitianMinEigenvalue Ĥ(γ(t))` for `t ∈ (0, 1]`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Combines:
- PR #3970 `spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min`
  (fixed `(λ, D)` version).
- PR #3975 `anisotropicHeisenbergParametricPath_in_strict_region` (path stays in
  strict region for `t ∈ (0, 1]`).

Conclusion: at any path point `γ(t)` for `t ∈ (0, 1]` with target `(λ', D')` in
strict region (i), the `Ĥ(γ(t))` eigenspace at its global min eigenvalue has
`finrank ≤ 2`. This is the parametric version of PR #3970, suitable for use at
the IVT crossing point.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 `Ĥ` eigenspace `finrank ≤ 2` at the global min along the path**:
for target `(λ', D')` in strict region (i) and `t ∈ (0, 1]`, the eigenspace of
`Ĥ(γ(t))` at its global min `hermitianMinEigenvalue Ĥ(γ(t))` has `finrank ≤ 2`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])) : ℝ) : ℂ)) ≤ 2 := by
  -- Path point lies in strict region (i).
  obtain ⟨hlb, hub, hDpos⟩ :=
    anisotropicHeisenbergParametricPath_in_strict_region hlam'_lb hlam'_ub hD' ht_pos ht_le
  -- The path coordinates as ℂ.
  set lam_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
  set D_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ)
  -- Imaginary parts vanish for real-cast values.
  have hlam_t_im : lam_t.im = 0 := by simp [lam_t]
  have hD_t_im : D_t.im = 0 := by simp [D_t]
  -- Real parts match the path coordinates.
  have hlam_t_re : lam_t.re = (anisotropicHeisenbergParametricPath lam' D' t).1 := by
    simp [lam_t]
  have hD_t_re : D_t.re = (anisotropicHeisenbergParametricPath lam' D' t).2 := by
    simp [D_t]
  -- Star equations.
  have hlam_t_star : star lam_t = lam_t := by
    rw [Complex.star_def]; simp [lam_t]
  have hD_t_star : star D_t = D_t := by
    rw [Complex.star_def]; simp [D_t]
  -- Bounds in terms of .re.
  have hlb_t : -1 < lam_t.re := by rw [hlam_t_re]; exact hlb
  have hub_t : lam_t.re < 1 := by rw [hlam_t_re]; exact hub
  have hDpos_t : 0 < D_t.re := by rw [hD_t_re]; exact hDpos
  -- Apply PR #3970.
  exact spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min
    A hJim hJnn hJpos hJself hJbip
    hlam_t_im hlb_t hub_t hD_t_im hDpos_t
    (hc_strict lam_t D_t) hA_ne hB_ne hJ_star hlam_t_star hD_t_star

end LatticeSystem.Quantum
