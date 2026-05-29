import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirEigenvector
import LatticeSystem.Quantum.SpinS.Theorem23StructuralReach

/-!
# Structural Theorem 2.3 eigenvector proportionality (no `h_intermediate`)

Extension of #3887 fix to `tasaki23_shiftedDressed_sector_eigenvec_proportional` /
`tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive` via
`isIrreducible_shiftedDressedSReMatrixOnMagSector_structural`.

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
    (isIrreducible_shiftedDressedSReMatrixOnMagSector_structural A c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN)
    hv hv_pos hw

end LatticeSystem.Quantum
