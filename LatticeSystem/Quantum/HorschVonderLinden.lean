import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

/-!
# Tasaki §3.4: the Horsch–von der Linden theorem (Theorem 3.1)

Tasaki's Theorem 3.1 (Horsch–von der Linden) states that a ground state with long-range order but
without spontaneous symmetry breaking inevitably has a low-lying excited energy eigenstate: from the
Horsch–von der Linden trial state `|Γ⟩` (orthogonal to the ground state and with energy
`⟨Γ|Ĥ|Γ⟩ ≤ E_GS + C·L^{-d}`, eq. (3.4.12)) one extracts an energy eigenstate `|Ψ⟩ ⊥ |Φ_GS⟩` with
`E_GS ≤ E ≤ E_GS + C·L^{-d}`.

The proof is elementary and finite-dimensional: expand `|Γ⟩` in the energy eigenbasis,
`⟨Γ|Ĥ|Γ⟩ = Σ_j |c_j|² E_j` with `Σ|c_j|² = 1` and `c_{GS} = 0` (orthogonality); if every excited
state in the support had `E_j > E_GS + δ` the energy expectation would exceed `E_GS + δ`, a
contradiction.  We discharge exactly this core here (axiom-free) using the spectral/Rayleigh
machinery; the `C·L^{-d}` bound from the long-range-order variational estimate is the application
context (the thermodynamic/infinite-volume input `δ`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, Theorem 3.1, eqs. (3.4.7)–(3.4.12), pp. 66–67.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Tasaki Theorem 3.1 (Horsch–von der Linden), finite-dimensional core.**  Let `H` be a Hermitian
matrix with minimum eigenvalue `E₀ = hH.eigenvalues i₀` (witnessed by `hmin`).  If a normalized
state `Γ` is orthogonal to the ground eigenvector (its `i₀`-component in the eigenbasis vanishes,
`hortho`)
and has Rayleigh energy `⟨Γ, H Γ⟩ ≤ E₀ + δ`, then there is an energy eigenstate `j ≠ i₀` (an excited
state orthogonal to the ground state) with `E₀ ≤ E_j ≤ E₀ + δ` — a low-lying excited state.

Proof: expand the Rayleigh quotient in the eigenbasis, `⟨Γ, H Γ⟩ = Σ_j ‖w_j‖² E_j` with
`Σ_j ‖w_j‖² = 1` and `w_{i₀} = 0`; if every `j` in the support had `E_j > E₀ + δ` the weighted sum
would exceed `E₀ + δ`, contradicting the hypothesis. -/
theorem horsch_vonderLinden_lowLying
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (i₀ : n)
    (hmin : ∀ j, hH.eigenvalues i₀ ≤ hH.eigenvalues j)
    {Γ : n → ℂ} (hunit : dotProduct (star Γ) Γ = 1)
    (hortho : (Matrix.IsHermitian.eigenvectorUnitary hH : Matrix n n ℂ).conjTranspose.mulVec Γ i₀
      = 0)
    {δ : ℝ} (hvar : rayleighOnVec H Γ ≤ hH.eigenvalues i₀ + δ) :
    ∃ j, j ≠ i₀ ∧ hH.eigenvalues i₀ ≤ hH.eigenvalues j ∧
      hH.eigenvalues j ≤ hH.eigenvalues i₀ + δ := by
  set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hH : Matrix n n ℂ) with hU_def
  set w : n → ℂ := U.conjTranspose.mulVec Γ with hw_def
  -- spectral expansion of the Rayleigh quotient
  have hspec : H = U * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
      * U.conjTranspose := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hexp : rayleighOnVec H Γ = ∑ j, ‖w j‖ ^ 2 * hH.eigenvalues j := by
    conv_lhs => rw [hspec, rayleighOnVec_unitary_conj, rayleighOnVec_diagonal_real]
  have hsum : (∑ j, ‖w j‖ ^ 2 : ℝ) = 1 := by
    rw [hw_def, sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq hH Γ, hunit, Complex.one_re]
  by_contra hcon
  push Not at hcon
  -- every support index has energy strictly above E₀ + δ
  have hgt : ∀ j, w j ≠ 0 → hH.eigenvalues i₀ + δ < hH.eigenvalues j := by
    intro j hwj
    have hji0 : j ≠ i₀ := by rintro rfl; exact hwj hortho
    exact hcon j hji0 (hmin j)
  -- a support index exists, since Σ ‖w_j‖² = 1 ≠ 0
  have hex : ∃ k, ‖w k‖ ^ 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero (fun j _ => hall j)] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨k, hwk⟩ := hex
  have hwk0 : w k ≠ 0 := fun h => hwk (by rw [h, norm_zero]; norm_num)
  have hwkpos : 0 < ‖w k‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hwk)
  -- the weighted energy then exceeds E₀ + δ, contradicting hvar
  have hstrict : hH.eigenvalues i₀ + δ < ∑ j, ‖w j‖ ^ 2 * hH.eigenvalues j := by
    have hle_term : ∀ j ∈ Finset.univ,
        ‖w j‖ ^ 2 * (hH.eigenvalues i₀ + δ) ≤ ‖w j‖ ^ 2 * hH.eigenvalues j := by
      intro j _
      rcases eq_or_ne (w j) 0 with hj | hj
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hgt j hj)) (by positivity)
    have hlt_term : ∃ j ∈ Finset.univ,
        ‖w j‖ ^ 2 * (hH.eigenvalues i₀ + δ) < ‖w j‖ ^ 2 * hH.eigenvalues j :=
      ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (hgt k hwk0) hwkpos⟩
    calc hH.eigenvalues i₀ + δ
        = (∑ j, ‖w j‖ ^ 2) * (hH.eigenvalues i₀ + δ) := by rw [hsum, one_mul]
      _ = ∑ j, ‖w j‖ ^ 2 * (hH.eigenvalues i₀ + δ) := by rw [Finset.sum_mul]
      _ < ∑ j, ‖w j‖ ^ 2 * hH.eigenvalues j := Finset.sum_lt_sum hle_term hlt_term
  rw [← hexp] at hstrict
  exact absurd hvar (not_le.mpr hstrict)

end LatticeSystem.Quantum
