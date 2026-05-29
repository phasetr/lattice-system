import LatticeSystem.Quantum.SpinS.Theorem23PFToyJointCasimir
import LatticeSystem.Quantum.SpinS.Theorem23StructuralCasimirEigenvec

/-!
# Structural Theorem 2.3 PF ground state commuting + joint Casimir eigenvector (no `h_intermediate`)

Extension of #3887 fix to:
- `tasaki23_pf_groundState_commuting_eigenvector`
- `tasaki23_toy_groundState_joint_casimir_eigenvector`

Both use `tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_structural`
(Thm23-#3887.3) instead of the original h_intermediate-bearing variant.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural PF ground state commuting eigenvector (no `h_intermediate`)**. -/
theorem tasaki23_pf_groundState_commuting_eigenvector_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (B : ManyBodyOpS V N)
    (hHB : Commute (heisenbergHamiltonianS J N) B)
    (h3B : Commute (totalSpinSOp3 V N) B)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    ∃ γ : ℂ,
      B.mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  set Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hΦdef
  set φ : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * v σ with hφdef
  have hΦ_mem :
      Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS _
  have hΨ_eig :
      (heisenbergHamiltonianS J N).mulVec (B.mulVec Φ) = (μ : ℂ) • B.mulVec Φ :=
    mulVec_preserves_eigenvalue_of_commuteS hHB hH
  have hΨ_mem :
      B.mulVec Φ ∈
        magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    rw [mem_magSubspaceS_iff] at hΦ_mem ⊢
    exact mulVec_preserves_eigenvalue_of_commuteS h3B hΦ_mem
  have hΨ_supp : ∀ σ, magSumS σ ≠ M → B.mulVec Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ_mem hσ
  have hΦ_supp : ∀ σ, magSumS σ ≠ M → Φ σ = 0 :=
    fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΦ_mem hσ
  have hΨr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) (B.mulVec Φ)) =
        (μ : ℂ) • magSectorRestriction (M := M) (B.mulVec Φ) :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hΨ_eig hΨ_supp
  have hΦr_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Φ) =
        (μ : ℂ) • magSectorRestriction (M := M) Φ :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH hΦ_supp
  have hφ_eig :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ := by
    have := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hΦr_eig
    have hre : (fun σ => (magSectorRestriction (M := M) Φ σ).re) = φ := by
      funext σ
      have hval : magSectorRestriction (M := M) Φ σ =
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ) := by
        rw [hΦdef]
        exact magSectorEmbedding_apply_subtype _ σ
      rw [hval, hφdef, Complex.ofReal_re]
    rwa [hre] at this
  have hφ_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * φ σ := by
    intro σ
    rw [hφdef]
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    have : (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) = v σ := by
      rw [← mul_assoc, hsq, one_mul]
    rw [this]; exact hv_pos σ
  have hΨr_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hΨr_eig
  have hΨr_im :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
      N hJ_real hΨr_eig
  obtain ⟨a, ha⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_structural A c hJ_real
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hφ_eig hφ_pos hΨr_re
  obtain ⟨b, hb⟩ :=
    tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_structural A c hJ_real
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hφ_eig hφ_pos hΨr_im
  refine ⟨⟨a, b⟩, ?_⟩
  funext ρ
  by_cases hρ : magSumS ρ = M
  · set σ : magConfigS V N M := ⟨ρ, hρ⟩ with hσdef
    have hre_eq : (B.mulVec Φ ρ).re = a * φ σ := by
      have := congrFun ha σ
      simpa [Pi.smul_apply, smul_eq_mul, magSectorRestriction, hσdef] using this
    have him_eq : (B.mulVec Φ ρ).im = b * φ σ := by
      have := congrFun hb σ
      simpa [Pi.smul_apply, smul_eq_mul, magSectorRestriction, hσdef] using this
    have hΦρ : Φ ρ = ((φ σ : ℝ) : ℂ) := by
      have hval : Φ σ.1 = (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ) := by
        rw [hΦdef]
        exact magSectorEmbedding_apply_subtype _ σ
      rw [hφdef]
      simpa [hσdef] using hval
    apply Complex.ext
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, hΦρ, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      rw [hre_eq]
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, hΦρ, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add]
      rw [him_eq]
  · rw [hΨ_supp ρ hρ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hΦ_supp ρ hρ, mul_zero]

/-- **Structural toy ground state joint Casimir eigenvector (no `h_intermediate`)**. -/
theorem tasaki23_toy_groundState_joint_casimir_eigenvector_structural
    (A : V → Bool) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hH :
      (heisenbergHamiltonianS (bipartiteCoupling A) N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    (∃ γ : ℂ, (totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
      (∃ γ : ℂ, (sublatticeSpinSquaredS N A).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
      (∃ γ : ℂ, (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        γ • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  have hJ_real : ∀ x y, (bipartiteCoupling A x y).im = 0 := bipartiteCoupling_im A
  have hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y →
      0 < (bipartiteCoupling A x y).re := by
    intro x y hadj
    rw [bipartiteCompleteGraphOf_adj_iff] at hadj
    exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2
  have hJ_nn : ∀ x y, 0 ≤ (bipartiteCoupling A x y).re := fun x y => bipartiteCoupling_nonneg A x y
  have hJ_sym : ∀ x y, bipartiteCoupling A x y = bipartiteCoupling A y x := bipartiteCoupling_symm A
  have hJ_bipartite : ∀ x y, A x = A y → bipartiteCoupling A x y = 0 :=
    fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h
  refine ⟨?_, ?_, ?_⟩
  · exact tasaki23_pf_groundState_commuting_eigenvector_structural A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN (totalSpinSSquared V N)
      (heisenbergToyHamiltonianS_commute_totalSpinSSquared (N := N) (A := A))
      (totalSpinSSquared_commute_totalSpinSOp3 (Λ := V) (N := N)).symm hv_pos hH
  · exact tasaki23_pf_groundState_commuting_eigenvector_structural A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN (sublatticeSpinSquaredS N A)
      (heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS (N := N) (A := A))
      (sublatticeSpinSquaredS_commute_totalSpinSOp3 (Λ := V) (N := N) A).symm hv_pos hH
  · exact tasaki23_pf_groundState_commuting_eigenvector_structural A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN (sublatticeSpinSquaredS N (fun x => ! A x))
      (heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS_complement (N := N) (A := A))
      (sublatticeSpinSquaredS_commute_totalSpinSOp3 (Λ := V) (N := N) (fun x => ! A x)).symm
      hv_pos hH

end LatticeSystem.Quantum
