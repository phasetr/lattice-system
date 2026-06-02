import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSBalancedSectorPFTarget

/-!
# General spin-S case-(ii) conditional bridge for Tasaki Theorem 2.4

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file records the first case-(ii) API layer.  The linear path from the
SU(2) point to a target `(lambda, D)` stays in the case-(ii) region
`lambda >= 1`, `D <= 0` on `[0, 1]`.  The target wrappers then package the
already available balanced-sector Perron--Frobenius target bridge under
case-(ii) names, while keeping the missing global crossing/degeneracy input
explicit as `balanced_eq_full` and `full finrank <= 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Case-(ii) path region -/

/-- Along the linear path from `(1, 0)` to a case-(ii) target with `1 <= lambda'`,
the first coordinate stays in the half-line `lambda >= 1` for `t >= 0`. -/
theorem anisotropicHeisenbergParametricPath_fst_ge_one_case_ii
    {lam' D' : ℝ} (hlam' : 1 ≤ lam') {t : ℝ} (ht_nn : 0 ≤ t) :
    1 ≤ (anisotropicHeisenbergParametricPath lam' D' t).1 := by
  unfold anisotropicHeisenbergParametricPath
  change 1 ≤ (1 - t) + t * lam'
  have hrewrite : (1 - t) + t * lam' = 1 + t * (lam' - 1) := by ring
  rw [hrewrite]
  have hprod : 0 ≤ t * (lam' - 1) := mul_nonneg ht_nn (by linarith)
  linarith

/-- Along the linear path from `(1, 0)` to a case-(ii) target with `D' <= 0`,
the second coordinate stays in the half-line `D <= 0` for `t >= 0`. -/
theorem anisotropicHeisenbergParametricPath_snd_nonpos_case_ii
    {lam' D' : ℝ} (hD' : D' ≤ 0) {t : ℝ} (ht_nn : 0 ≤ t) :
    (anisotropicHeisenbergParametricPath lam' D' t).2 ≤ 0 := by
  unfold anisotropicHeisenbergParametricPath
  change t * D' ≤ 0
  exact mul_nonpos_of_nonneg_of_nonpos ht_nn hD'

/-- **Combined case-(ii) path-region statement**: for a target satisfying
`1 <= lambda'` and `D' <= 0`, the linear path stays in the case-(ii) region
for every `t ∈ [0, 1]`. -/
theorem anisotropicHeisenbergParametricPath_in_case_ii_region
    {lam' D' : ℝ} (hlam' : 1 ≤ lam') (hD' : D' ≤ 0)
    {t : ℝ} (ht_nn : 0 ≤ t) (_ht_le : t ≤ 1) :
    1 ≤ (anisotropicHeisenbergParametricPath lam' D' t).1 ∧
    (anisotropicHeisenbergParametricPath lam' D' t).2 ≤ 0 :=
  ⟨anisotropicHeisenbergParametricPath_fst_ge_one_case_ii hlam' ht_nn,
    anisotropicHeisenbergParametricPath_snd_nonpos_case_ii hD' ht_nn⟩

/-! ## Case-(ii) conditional target wrappers -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1`,
conditional bridge**.  Under the case-(ii) inequalities `1 <= lambda`, `D <= 0`,
balanced-sector/full-ground equality, and the still-explicit full
`finrank <= 2` input, the existing balanced-sector PF target bridge gives
target uniqueness. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_balanced_eq_full
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_target_finrank_le_one_of_balanced_eq_full
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_balanced_eq_full h_full_le_two

/-- **General spin-S case-(ii) target ground states have zero total
magnetization, conditional bridge**.  This is the case-(ii) named composition
of the balanced-sector PF target bridge with the uniqueness-implies-zero
magnetization theorem, again leaving the missing global inputs explicit. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_balanced_eq_full
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_target_groundState_zero_magnetization_of_balanced_eq_full
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_balanced_eq_full h_full_le_two hΦ_ne hΦ_gs

end LatticeSystem.Quantum
