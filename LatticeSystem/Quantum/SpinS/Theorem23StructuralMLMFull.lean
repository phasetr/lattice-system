import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem23StructuralFullHilbertEigenvec
import LatticeSystem.Quantum.SpinS.Theorem23StructuralUniqueness

/-!
# Structural Tasaki §2.5 Theorem 2.2 bundled full-Hilbert form (no `h_intermediate`)

(Thm23-#3887.15): structural variant of
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full` bundling
- existence (Thm23-#3887.13 `exists_marshallSign_eigenvector_heisenbergHamiltonianS_full_structural`)
- support (zero outside sector — direct from `magSectorEmbedding_apply_of_not_mem`)
- uniqueness (Thm23-#3887.14
  `marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector_structural`)
into the textbook statement of the §2.5 Theorem 2.2 ground state on the actual quantum
Heisenberg Hamiltonian, with `(hA_ne, hB_ne, hN)` instead of `h_intermediate`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.2, pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural Tasaki §2.5 Theorem 2.2 bundled (no `h_intermediate`)**. -/
theorem marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full_structural
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianS_full_structural
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  refine ⟨μ, v, hμ, hv_pos, hmul, ?_, ?_⟩
  · intro σ hne
    exact magSectorEmbedding_apply_of_not_mem _ hne
  · intro μ' Ψ' hΨ' hΨ'_supp hΨ'_marshall_pos
    have hΨ'_sec :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction
        J hΨ' hΨ'_supp
    have hsec_ground :
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) =
          (μ : ℂ) • (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
      funext τ
      change (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ' : magConfigS V N M =>
            (((marshallSignS A τ'.1).re * v τ' : ℝ) : ℂ)) τ =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [← heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype J _ τ]
      have hμembed := congrFun hmul τ.1
      rw [hμembed]
      change ((μ : ℂ) • magSectorEmbedding _) τ.1 =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [Pi.smul_apply, magSectorEmbedding_apply_subtype, smul_eq_mul]
    obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
      marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector_structural
        (N := N) (M := M) A c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        hA_ne hB_ne hN hsec_ground (by
          intro τ
          rw [Complex.ofReal_re]
          have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
            marshallSignS_re_sq A τ.1
          rw [← mul_assoc, hsq, one_mul]
          exact hv_pos τ)
        hΨ'_sec hΨ'_marshall_pos
    refine ⟨hμ_eq.symm, r, hr_pos, fun τ => ?_⟩
    have hτ := hrel τ
    change (magSectorRestriction Ψ' τ).re = r * ((marshallSignS A τ.1).re * v τ)
    rw [hτ]
    rw [Complex.ofReal_re]

end LatticeSystem.Quantum
