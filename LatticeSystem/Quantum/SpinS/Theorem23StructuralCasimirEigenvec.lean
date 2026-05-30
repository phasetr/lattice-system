import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirEigenvector
import LatticeSystem.Quantum.SpinS.Theorem23StructuralReach

/-!
# Structural Theorem 2.3 eigenvector proportionality (no `h_intermediate`)

Extension of #3887 fix to `tasaki23_shiftedDressed_sector_eigenvec_proportional` /
`tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive` via
`isIrreducible_shiftedDressedSReMatrixOnMagSector`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobenius

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural shifted-dressed sector eigenvector proportionality (no `h_intermediate`)**. -/
theorem tasaki23_shiftedDressed_sector_eigenvec_proportional_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {r : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = r • w) :
    ∃ s : ℝ, w = s • v :=
  eigenvec_proportional_of_pos_eigenvec
    (isIrreducible_shiftedDressedSReMatrixOnMagSector A c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN)
    hv hv_pos hw

/-- **Structural Heisenberg sector eigenvector proportionality (no `h_intermediate`)**. -/
theorem tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive_structural
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {φ w : magConfigS V N M → ℝ}
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ)
    (hφ_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * φ σ)
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w) :
    ∃ s : ℝ, w = s • φ := by
  have hφs :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hφ)
  have hws :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hw)
  obtain ⟨s, hs⟩ :=
    tasaki23_shiftedDressed_sector_eigenvec_proportional_structural A c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN hφs hφ_pos hws
  refine ⟨s, ?_⟩
  funext σ
  have hi := congrFun hs σ
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  calc
    w σ = ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * w σ := by
          rw [hsq, one_mul]
    _ = (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * w σ) := by ring
    _ = (marshallSignS A σ.1).re * (s * ((marshallSignS A σ.1).re * φ σ)) := by rw [hi]
    _ = s * ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re * φ σ) := by ring
    _ = s * φ σ := by rw [hsq, one_mul]

end LatticeSystem.Quantum
