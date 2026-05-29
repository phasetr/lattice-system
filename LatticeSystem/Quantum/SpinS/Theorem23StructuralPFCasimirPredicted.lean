import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFJointCasimir

/-!
# Structural Theorem 2.3 PF GS Casimir = predicted (no `h_intermediate`)

(Thm23-#3887.8): structural variant of
`tasaki23_pf_groundState_casimir_eq_predicted_of_witness` using
`tasaki23_pf_groundState_casimir_eigenvector_structural` (Thm23-#3887.7).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural PF GS Casimir = predicted via witness (no `h_intermediate`)**. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_of_witness_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hw_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨γ, hγ⟩ :=
    tasaki23_pf_groundState_casimir_eigenvector_structural A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hv_pos hH
  have hγ_real : star γ = γ :=
    isHermitian_eigenvalue_star_eq (totalSpinSSquared_isHermitian V N) hγ
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
  have hpred_real :
      star ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hγ_eq : γ = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) :=
    tasaki23_marshallPositive_casimir_eigenvalue_eq A hv_pos hw_pos hγ_real
      hpred_real hγ hw_cas
  rw [← hγ_eq]
  exact hγ

end LatticeSystem.Quantum
