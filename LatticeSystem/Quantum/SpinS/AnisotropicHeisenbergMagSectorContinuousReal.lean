import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity

/-!
# Per-sector continuity of `Ĥ_M(λ, D)` for real `(λ, D)` (entry-wise approach)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

The matrix-valued function `(λ, D) ↦ Ĥ_M(λ, D)` (per-sector restriction) is
continuous on `ℝ × ℝ` via the real-to-complex coercion. Proved by entry-wise
continuity (`continuous_matrix`) to avoid the `Continuous.comp` typeclass-
synthesis timeout encountered with the chained composition approach.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The per-sector restriction `(λ, D) ↦ Ĥ_M(λ, D)` is continuous on `ℝ × ℝ`. -/
theorem continuous_anisotropicHeisenbergS_magSector_submatrix_real
    (J : Λ → Λ → ℂ) (N M : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J ((p.1 : ℂ)) ((p.2 : ℂ)) N M) := by
  refine continuous_matrix (fun i j => ?_)
  -- (Ĥ_M(λ, D))_{ij} = Ĥ(λ, D)_{i.val, j.val}
  unfold anisotropicHeisenbergS_magSector_submatrix
  simp only [Matrix.submatrix_apply]
  -- now reduces to continuity of `(λ, D) ↦ Ĥ(λ, D) i.val j.val`
  unfold anisotropicHeisenbergS
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Continuous.add ?_ ?_
  · refine continuous_finset_sum _ (fun x _ => continuous_finset_sum _ (fun y _ => ?_))
    refine Continuous.mul continuous_const ?_
    unfold spinSDotXXZ
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Continuous.add (Continuous.add continuous_const continuous_const) ?_
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp continuous_fst
  · unfold singleIonAnisotropyS
    simp only [Matrix.smul_apply, smul_eq_mul]
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp continuous_snd

end LatticeSystem.Quantum
