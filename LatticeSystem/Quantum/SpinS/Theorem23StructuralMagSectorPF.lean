import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall
import LatticeSystem.Quantum.SpinS.Theorem23StructuralReach

/-!
# Structural sector PF positive eigenvector wrappers (no `h_intermediate`)

(Thm23-#3887.9): structural variants of the sector PF positive-eigenvector
existence theorems using `isIrreducible_shiftedDressedSReMatrixOnMagSector_structural`
(Thm23-#3887.1).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobeniusMain

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural shifted-dressed sector PF positive eigenvector (no `h_intermediate`)**. -/
theorem exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ (r : ℝ) (v : magConfigS V N M → ℝ),
      0 < r ∧ (∀ σ, 0 < v σ) ∧
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v := by
  have hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible :=
    isIrreducible_shiftedDressedSReMatrixOnMagSector_structural (N := N) (M := M)
      A c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
  exact LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible hIrred

/-- **Structural dressed Heisenberg sector PF positive eigenvector (no `h_intermediate`)**. -/
theorem exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
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
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v := by
  obtain ⟨r, v, hr_pos, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector_structural
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
  refine ⟨c - r, v, by linarith, hv_pos, ?_⟩
  exact dressedHeisenbergSReMatrixOnMagSector_mulVec_of_shifted_eigenvec A J N c hmul

/-- **Structural Heisenberg sector Marshall-sign eigenvector (no `h_intermediate`)**. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
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
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector_structural
      (N := N) (M := M) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
      A N hJ_real hmul⟩

end LatticeSystem.Quantum
