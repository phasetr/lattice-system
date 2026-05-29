import LatticeSystem.Math.HermitianMaxEqPF
import LatticeSystem.Math.HermitianSpectrumShift

/-!
# Hermitian min eigenvalue = shift − PF eigenvalue

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.h.1) (generic): For a real symmetric matrix `M_real : Matrix n n ℝ`, if the
shift `B_real := c • 1 - M_real` is symmetric, nonneg, and has a strictly positive
PF eigenvector `v` at eigenvalue `μ_PF`, then
`hermitianMinEigenvalue (M_real.map ofReal).IsHermitian = c - μ_PF`.

**Proof.** Combine:
- (j.13.f) `hermitianMaxEigenvalue (B_real.map ofReal).IsHermitian = μ_PF`.
- (j.13.g) `hermitianMinEigenvalue (M_real.map ofReal).IsHermitian = c -
  hermitianMaxEigenvalue ((c • 1) - M_real.map ofReal)`.
- The matrix identity `c • 1 - M_real.map ofReal = B_real.map ofReal` (via Matrix.map
  distributing over `c • 1` and `-`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Fintype n] [Nonempty n] in
/-- **Lifting commutes with `c • 1 - ·` for real `c`**:
`(c • 1 - M).map ofReal = (c : ℂ) • 1 - M.map ofReal`. -/
theorem map_smul_one_sub
    (M_real : Matrix n n ℝ) (c : ℝ) :
    ((c • (1 : Matrix n n ℝ) - M_real)).map (algebraMap ℝ ℂ) =
      (c : ℂ) • (1 : Matrix n n ℂ) - M_real.map (algebraMap ℝ ℂ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [smul_eq_mul]
  · simp [h, smul_eq_mul]

/-- **(j.13.h.1) Hermitian min eigenvalue = `c - μ_PF`** (lift of real symmetric
matrix with PF eigenvector for the shift). -/
theorem hermitianMinEigenvalue_lift_eq_sub_pf
    {M_real : Matrix n n ℝ} (hM_symm : M_real.IsSymm)
    (c : ℝ)
    (hB_nn : ∀ i j, 0 ≤ (c • (1 : Matrix n n ℝ) - M_real) i j)
    (hB_symm : (c • (1 : Matrix n n ℝ) - M_real).IsSymm)
    {μ_PF : ℝ} {v : n → ℝ}
    (h_eig : (c • (1 : Matrix n n ℝ) - M_real).mulVec v = μ_PF • v)
    (hv_pos : ∀ i, 0 < v i) :
    LatticeSystem.Quantum.hermitianMinEigenvalue
        (isHermitian_map_ofReal_of_isSymm hM_symm) = c - μ_PF := by
  -- (j.13.g) at M_complex.
  rw [LatticeSystem.Math.hermitianMinEigenvalue_eq_sub_hermitianMaxEigenvalue_shift
        (isHermitian_map_ofReal_of_isSymm hM_symm) c]
  -- (j.13.f) at B_real: hermitianMaxEigenvalue (B_real.map ofReal) = μ_PF.
  -- But we need to identify (c • 1 - M_complex) with (B_real.map ofReal).
  have hidentity : ((c : ℂ) • (1 : Matrix n n ℂ) - (M_real.map (algebraMap ℝ ℂ))) =
      (c • (1 : Matrix n n ℝ) - M_real).map (algebraMap ℝ ℂ) :=
    (map_smul_one_sub M_real c).symm
  -- For the (j.13.f) application, we use isHermitian_map_ofReal_of_isSymm hB_symm.
  have hHerm_eq : LatticeSystem.Math.hermitianMaxEigenvalue
        (isHermitian_smul_one_sub_of_real (isHermitian_map_ofReal_of_isSymm hM_symm) c) =
      LatticeSystem.Math.hermitianMaxEigenvalue
        (isHermitian_map_ofReal_of_isSymm hB_symm) := by
    -- The two IsHermitian witnesses are for the same underlying matrix.
    congr 1
  rw [hHerm_eq]
  -- (j.13.f) gives hermitianMaxEigenvalue (B_real.map ofReal) = μ_PF.
  rw [hermitianMaxEigenvalue_eq_of_pos_eigenvector hB_symm hB_nn h_eig hv_pos]

end LatticeSystem.Math.CollatzWielandt
