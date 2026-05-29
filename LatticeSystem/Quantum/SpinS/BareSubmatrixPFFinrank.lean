import LatticeSystem.Quantum.SpinS.MarshallSubmatrixMinEq
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank

/-!
# Bare submatrix `finrank ℂ ≤ 1` at PF ν via Marshall finrank similarity

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.10): combines #3831 (dressed submatrix `finrank ≤ 1` at PF ν) with #3746
`matrix_similar_eigenspace_finrank_eq` via the Marshall similarity (j.8) #3865 to give
the bare submatrix `finrank ≤ 1` at the same ν.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare submatrix `finrank ℂ ≤ 1` at PF ν** via Marshall similarity from the dressed
submatrix bound (#3831). -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_pf_eigenspace_finrank_le_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 := by
  -- Dressed bound from #3831.
  obtain ⟨ν, hν_dressed⟩ :=
    complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, ?_⟩
  -- Apply #3746 similarity finrank equality: bare.submatrix = Θ_p * dressed.submatrix * Θ_p
  -- (or equivalently dressed = Θ_p * bare * Θ_p via (j.8)).
  -- finrank ℂ (eig dressed.submatrix μ) = finrank ℂ (eig bare.submatrix μ).
  have h_similarity_finrank :=
    matrix_similar_eigenspace_finrank_eq
      (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
      (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
      (dressedAxisSwapped_submatrix_eq_marshall_conj_bare A J lam D p) (ν : ℂ)
  -- h_similarity_finrank : finrank dressed.submatrix = finrank bare.submatrix.
  rw [h_similarity_finrank] at hν_dressed
  exact hν_dressed

end LatticeSystem.Quantum
