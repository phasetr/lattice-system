import LatticeSystem.Math.HermitianMaxEigenvalueLeOfPF
import LatticeSystem.Math.HermitianMaxGeOfEigenvector

/-!
# Complex Hermitian max eigenvalue = PF eigenvalue (lift of real symmetric matrix)

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.f): For a real symmetric nonneg matrix `B_real` with a strictly positive
eigenvector `v` at eigenvalue `μ_PF`, the complex Hermitian view
`B_complex := B_real.map (algebraMap ℝ ℂ)` satisfies
`hermitianMaxEigenvalue B_complex.IsHermitian = μ_PF`.

**Proof.** By antisymmetry, combining:
- (j.13.d) `hermitian_max_eigenvalue_ge_of_eigenvector_exists`: `μ_PF ≤
  hermitianMaxEigenvalue B_complex` (using `v` lifted to ℂ as the eigenvector).
- (j.13.e.6) `hermitianMaxEigenvalue_le_of_pos_eigenvector`:
  `hermitianMaxEigenvalue B_complex ≤ μ_PF`.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **(j.13.f) Complex Hermitian max eigenvalue = PF eigenvalue**.

For a real symmetric nonneg matrix `B_real` with strictly positive eigenvector
`v` at `μ_PF`, `hermitianMaxEigenvalue (B_real.map ofReal).IsHermitian = μ_PF`. -/
theorem hermitianMaxEigenvalue_eq_of_pos_eigenvector
    {B_real : Matrix n n ℝ} (hsymm : B_real.IsSymm) (hnn : ∀ i j, 0 ≤ B_real i j)
    {μ_PF : ℝ} {v : n → ℝ} (h_eig : B_real.mulVec v = μ_PF • v) (hv_pos : ∀ i, 0 < v i) :
    LatticeSystem.Math.hermitianMaxEigenvalue
      (isHermitian_map_ofReal_of_isSymm hsymm) = μ_PF := by
  -- Lift v to ℂ: v_complex i := (v i : ℂ).
  set v_complex : n → ℂ := fun i => (v i : ℂ) with hv_def
  -- v_complex ≠ 0 (since v > 0).
  have hv_ne : v_complex ≠ 0 := by
    intro h
    have : (v (Classical.arbitrary n) : ℂ) = 0 := congrFun h (Classical.arbitrary n)
    have h_real : v (Classical.arbitrary n) = 0 := by
      have := congrArg Complex.re this
      simpa using this
    linarith [hv_pos (Classical.arbitrary n)]
  -- v_complex is an eigenvector of B_complex at (μ_PF : ℂ).
  have h_eig_c : (B_real.map (algebraMap ℝ ℂ)).mulVec v_complex = (μ_PF : ℂ) • v_complex := by
    funext i
    have := congrFun h_eig i
    -- (B_complex v_complex) i = (algebraMap ℝ ℂ) ((B_real v) i) (via RingHom.map_mulVec).
    have hmap : (algebraMap ℝ ℂ) ((B_real.mulVec v) i) =
        ((B_real.map (algebraMap ℝ ℂ)).mulVec ((algebraMap ℝ ℂ) ∘ v)) i :=
      RingHom.map_mulVec (algebraMap ℝ ℂ) B_real v i
    have h_v_eq : ((algebraMap ℝ ℂ) ∘ v) = v_complex := rfl
    rw [h_v_eq] at hmap
    rw [← hmap, this]
    change (algebraMap ℝ ℂ) (μ_PF • v i) = ((μ_PF : ℂ) • v_complex) i
    rw [Pi.smul_apply]
    simp [hv_def]
  -- (j.13.d): μ_PF ≤ hermitianMaxEigenvalue.
  have h_ge : μ_PF ≤ LatticeSystem.Math.hermitianMaxEigenvalue
      (isHermitian_map_ofReal_of_isSymm hsymm) :=
    LatticeSystem.Math.hermitian_max_eigenvalue_ge_of_eigenvector_exists
      (isHermitian_map_ofReal_of_isSymm hsymm) hv_ne h_eig_c
  -- (j.13.e.6): hermitianMaxEigenvalue ≤ μ_PF.
  have h_le : LatticeSystem.Math.hermitianMaxEigenvalue
      (isHermitian_map_ofReal_of_isSymm hsymm) ≤ μ_PF :=
    hermitianMaxEigenvalue_le_of_pos_eigenvector hsymm hnn h_eig hv_pos
  exact le_antisymm h_le h_ge

end LatticeSystem.Math.CollatzWielandt
