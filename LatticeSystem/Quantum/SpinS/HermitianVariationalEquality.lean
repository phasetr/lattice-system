import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

/-!
# Hermitian variational equality: minimal Rayleigh quotient ⟹ eigenvector

The companion to `hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec`: a
nonzero vector that *attains* the variational lower bound (its Rayleigh quotient
equals the minimum eigenvalue) is a minimum-eigenvalue eigenvector.

Spectral-coordinates proof: write `M = U D Uᴴ` (spectral theorem), set
`a = Uᴴ v`; then `rayleighOnVec M v = Σ ‖a_i‖² λ_i` and
`Σ ‖a_i‖² = ⟨v, v⟩`. Attaining the bound forces `Σ ‖a_i‖² (λ_i − μ) = 0` with
each non-negative summand zero, so `D a = μ a`, whence
`M v = U D Uᴴ v = U (μ a) = μ (U Uᴴ) v = μ v`.

Reference: standard Rayleigh–Ritz / Courant–Fischer equality case; used for the
Tasaki §11.2.1 weak-Nagaoka ferromagnetic-ground-state construction.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Variational equality ⟹ eigenvector.** For a Hermitian matrix `M`, a nonzero
vector `v` whose Rayleigh quotient attains the minimum eigenvalue,
`rayleighOnVec M v = hermitianMinEigenvalue hM · ⟨v, v⟩`, is a minimum-eigenvalue
eigenvector: `M v = (hermitianMinEigenvalue hM) • v`. -/
theorem mulVec_eq_smul_of_rayleighOnVec_eq_min
    {M : Matrix n n ℂ} (hM : M.IsHermitian) {v : n → ℂ}
    (heq : rayleighOnVec M v =
      hermitianMinEigenvalue hM * (dotProduct (star v) v).re) :
    M.mulVec v = ((hermitianMinEigenvalue hM : ℝ) : ℂ) • v := by
  set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) with hU_def
  set lam := hM.eigenvalues with hlam
  set μ : ℝ := hermitianMinEigenvalue hM with hμ
  set a := U.conjTranspose.mulVec v with ha
  have hUU : U * U.conjTranspose = 1 := eigenvectorUnitary_mul_conjTranspose_eq_one hM
  have hspec : M = U * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * U.conjTranspose := by
    have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hray : rayleighOnVec M v = ∑ i, ‖a i‖ ^ 2 * lam i := by
    conv_lhs => rw [hspec, rayleighOnVec_unitary_conj, rayleighOnVec_diagonal_real]
  have hsum : (∑ i, ‖a i‖ ^ 2) = (dotProduct (star v) v).re :=
    sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq hM v
  have hμ_le : ∀ i, μ ≤ lam i := fun i =>
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hzero : (∑ i, ‖a i‖ ^ 2 * (lam i - μ)) = 0 := by
    have h1 : (∑ i, ‖a i‖ ^ 2 * lam i) = μ * ∑ i, ‖a i‖ ^ 2 := by
      rw [← hray, heq, hsum]
    calc (∑ i, ‖a i‖ ^ 2 * (lam i - μ))
        = (∑ i, ‖a i‖ ^ 2 * lam i) - μ * ∑ i, ‖a i‖ ^ 2 := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [h1, sub_self]
  have hterm : ∀ i, ‖a i‖ ^ 2 * (lam i - μ) = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ ‖a i‖ ^ 2 * (lam i - μ) :=
      fun i _ => mul_nonneg (sq_nonneg _) (by linarith [hμ_le i])
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
  have hDa : (Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))).mulVec a = (μ : ℂ) • a := by
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rcases mul_eq_zero.mp (hterm i) with h | h
    · have hai : a i = 0 :=
        norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h)
      rw [hai, mul_zero, mul_zero]
    · have : (lam i : ℂ) = (μ : ℂ) := by exact_mod_cast (sub_eq_zero.mp h)
      rw [this]
  have hstep : M.mulVec v =
      U.mulVec ((Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))).mulVec a) := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hstep, hDa, Matrix.mulVec_smul, ha, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

end LatticeSystem.Quantum
