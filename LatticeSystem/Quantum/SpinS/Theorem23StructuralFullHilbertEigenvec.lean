import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem23StructuralComplexSectorEigenvec

/-!
# Structural full-Hilbert-space Marshall eigenvector (no `h_intermediate`)

(Thm23-#3887.13): structural variant of
`exists_marshallSign_eigenvector_heisenbergHamiltonianS_full_legacy` lifting
`exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector`
(Thm23-#3887.12) via `heisenbergHamiltonianS_mulVec_magSectorEmbedding`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.2, pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural full-Hilbert-space Marshall ground-state existence (no `h_intermediate`)**. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianS_full
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      hA_ne hB_ne hN
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianS_mulVec_magSectorEmbedding J _ hmul⟩

end LatticeSystem.Quantum
