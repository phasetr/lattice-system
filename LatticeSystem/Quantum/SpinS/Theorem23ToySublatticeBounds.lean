import LatticeSystem.Quantum.SpinS.Theorem23PFToyJointCasimir
import LatticeSystem.Quantum.SpinS.SublatticeCasimirSpectralBound
import LatticeSystem.Quantum.SpinS.Theorem23Casimir

/-!
# Sublattice Casimir bounds for the toy ground state

Issue #3674 (the abstract variational lower bound completing the toy-ground-state
predicted-Casimir witness; Issue #3658 PR 4 / #3542).

The toy ground state is a joint Casimir eigenvector (#3657) and its
Marshall-dressed embedding is non-zero, so the sublattice Casimir spectral max
bounds (`sublatticeSpinSquaredS_eigenvalue_re_le_sA`, #3672) apply to its `(Ŝ_A)²`
and `(Ŝ_¬A)²` eigenvalues: `γ_A.re ≤ s_A(s_A+1)`, `γ_B.re ≤ s_B(s_B+1)`.  These
discharge two of the hypotheses of the toy total-Casimir pin
(`tasaki23_total_casimir_re_eq_predicted_of_bounds`, #3676).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sublattice Casimir bounds for the toy ground state**: the per-sector
Marshall-positive ground state of `Ĥ_toy` is a joint Casimir eigenvector whose
`(Ŝ_A)²` and `(Ŝ_¬A)²` eigenvalues `γ_A, γ_B` obey `γ_A.re ≤ s_A(s_A+1)` and
`γ_B.re ≤ s_B(s_B+1)` (`s_A = |A|·N/2`, `s_B = |¬A|·N/2`). -/
@[deprecated "Superseded by the h_intermediate-free canonical variant (Phase E refactor #3921); retained for backwards compatibility" (since := "2026-05-30")]

theorem tasaki23_toy_groundState_sublattice_casimir_re_le_legacy
    (A : V → Bool) (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    (∃ γ_A : ℂ,
        (sublatticeSpinSquaredS N A).mulVec
            (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
          γ_A • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) ∧
        γ_A.re ≤
          ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1)) ∧
    (∃ γ_B : ℂ,
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
          γ_B • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) ∧
        γ_B.re ≤
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) := by
  obtain ⟨_, ⟨γ_A, hγ_A⟩, ⟨γ_B, hγ_B⟩⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector_legacy A N c hc_strict h_intermediate hv_pos hH
  have hne := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos
  exact ⟨⟨γ_A, hγ_A, sublatticeSpinSquaredS_eigenvalue_re_le_sA A hne hγ_A⟩,
    ⟨γ_B, hγ_B, sublatticeSpinSquaredS_eigenvalue_re_le_sA (fun x => ! A x) hne hγ_B⟩⟩

end LatticeSystem.Quantum
