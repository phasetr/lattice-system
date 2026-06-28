/-
The Hermitian second-eigenvalue variational bound
(Tasaki §6.2 Theorem 6.3, toward the Lieb–Schultz–Mattis spectral gap).

If a Hermitian matrix `M` has a one-dimensional minimum-eigenvalue eigenspace spanned by `φ₀`
(`M φ₀ = E₀ φ₀`), then every vector `ψ` orthogonal to `φ₀` obeys the second-eigenvalue variational
bound `E₁ · ‖ψ‖² ≤ rayleighOnVec M ψ`, where `E₁` lower-bounds every eigenvalue different from `E₀`.
This is the Courant–Fischer second-eigenvalue step: expanding `ψ` in the eigenbasis, orthogonality to
`φ₀` annihilates the `E₀`-eigenvalue components (the ground line is one-dimensional), leaving only
components with eigenvalue `≥ E₁`.
-/
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- The `i`-th component of `Uᴴ ψ` (for `U` the eigenvector unitary) is the inner product of the
`i`-th eigenvector with `ψ`. -/
theorem conjTranspose_eigenvectorUnitary_mulVec_apply {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (ψ : n → ℂ) (i : n) :
    (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ).conjTranspose.mulVec ψ i
      = star (⇑(hM.eigenvectorBasis i) : n → ℂ) ⬝ᵥ ψ := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.IsHermitian.eigenvectorUnitary_apply hM j i]

omit [Nonempty n] in
/-- **Hermitian second-eigenvalue variational bound.**  For a Hermitian `M` with a one-dimensional
`E₀`-eigenspace spanned by `φ₀` (`M φ₀ = E₀ φ₀`, `φ₀ ≠ 0`), and a real `E₁` bounding every
eigenvalue `≠ E₀` from below, every `ψ ⊥ φ₀` satisfies `E₁ · ‖ψ‖² ≤ rayleighOnVec M ψ`. -/
theorem hermitian_second_eigenvalue_variational {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {φ₀ : n → ℂ} {E₀ E₁ : ℝ} (hφ₀_eig : M.mulVec φ₀ = (E₀ : ℂ) • φ₀) (hφ₀_ne : φ₀ ≠ 0)
    (hfin : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' M) (E₀ : ℂ)) ≤ 1)
    (hE₁ : ∀ i, hM.eigenvalues i ≠ E₀ → E₁ ≤ hM.eigenvalues i)
    {ψ : n → ℂ} (hψ_orth : star φ₀ ⬝ᵥ ψ = 0) :
    E₁ * (star ψ ⬝ᵥ ψ).re ≤ rayleighOnVec M ψ := by
  set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) with hU_def
  set w : n → ℂ := U.conjTranspose.mulVec ψ with hw_def
  -- spectral decomposition `M = U D Uᴴ`
  have hspec : M = U * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ))
      * U.conjTranspose := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  -- `rayleighOnVec M ψ = Σ ‖w i‖² · eigenvalues i`
  have hexp : rayleighOnVec M ψ = ∑ i, ‖w i‖ ^ 2 * hM.eigenvalues i := by
    conv_lhs => rw [hspec, rayleighOnVec_unitary_conj, rayleighOnVec_diagonal_real]
  -- `Σ ‖w i‖² = (star ψ ⬝ᵥ ψ).re`
  have hsum : (∑ i, ‖w i‖ ^ 2 : ℝ) = (star ψ ⬝ᵥ ψ).re :=
    sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq hM ψ
  -- the ground line is `span φ₀`: extract a generator
  set E := Module.End.eigenspace (Matrix.toLin' M) (E₀ : ℂ) with hEdef
  have hφ₀_mem : φ₀ ∈ E := by
    rw [hEdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hφ₀_eig
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hfin
  obtain ⟨a, ha⟩ := hv ⟨φ₀, hφ₀_mem⟩
  have ha' : a • (v : n → ℂ) = φ₀ := by
    have h := congrArg ((↑) : ↥E → n → ℂ) ha; simpa using h
  have ha_ne : a ≠ 0 := fun h0 => hφ₀_ne (by rw [← ha', h0, zero_smul])
  -- the `E₀`-eigenvalue components of `ψ` vanish (orthogonality to `φ₀`)
  have hkill : ∀ i, hM.eigenvalues i = E₀ → w i = 0 := by
    intro i hi
    have huᵢ_eig : M.mulVec (⇑(hM.eigenvectorBasis i) : n → ℂ)
        = (E₀ : ℂ) • (⇑(hM.eigenvectorBasis i) : n → ℂ) := by
      rw [hM.mulVec_eigenvectorBasis i, hi]; exact (Complex.coe_smul E₀ _).symm
    have huᵢ_mem : (⇑(hM.eigenvectorBasis i) : n → ℂ) ∈ E := by
      rw [hEdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact huᵢ_eig
    obtain ⟨b, hb⟩ := hv ⟨_, huᵢ_mem⟩
    have hb' : b • (v : n → ℂ) = (⇑(hM.eigenvectorBasis i) : n → ℂ) := by
      have h := congrArg ((↑) : ↥E → n → ℂ) hb; simpa using h
    -- `uᵢ = (b * a⁻¹) • φ₀`
    have huᵢ_eq : (⇑(hM.eigenvectorBasis i) : n → ℂ) = (b * a⁻¹) • φ₀ := by
      rw [← hb', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
    have hwi : w i = star (⇑(hM.eigenvectorBasis i) : n → ℂ) ⬝ᵥ ψ := by
      rw [hw_def, hU_def]; exact conjTranspose_eigenvectorUnitary_mulVec_apply hM ψ i
    rw [hwi, huᵢ_eq, star_smul, smul_dotProduct, hψ_orth, smul_zero]
  -- support lower bound: nonzero components have eigenvalue `≥ E₁`
  have hsupport : ∀ i, w i ≠ 0 → E₁ ≤ hM.eigenvalues i := fun i hwi =>
    hE₁ i (fun h => hwi (hkill i h))
  -- weighted-sum lower bound
  have hweighted : E₁ * (∑ i, ‖w i‖ ^ 2) ≤ ∑ i, ‖w i‖ ^ 2 * hM.eigenvalues i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : w i = 0
    · simp [hi]
    · rw [mul_comm E₁]
      exact mul_le_mul_of_nonneg_left (hsupport i hi) (sq_nonneg _)
  rw [hexp, ← hsum]
  exact hweighted

end LatticeSystem.Quantum
