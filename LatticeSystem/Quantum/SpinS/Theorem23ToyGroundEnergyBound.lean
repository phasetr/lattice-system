import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.ToyHamiltonian

/-!
# Variational upper bound on the toy ground energy

Issue #3674 (Issue #3658 PR 4 / #3542): the variational comparison reducing the
reference energy bound `hμ` to the existence of a single reference eigenvector.

The Marshall-positive toy ground state (energy `μ`) is the **minimal**-energy
sector state: for any sector eigenvector `φ` at real energy `E`, `μ ≤ E`.  This
is `heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive`
specialised to the bipartite toy coupling `J = bipartiteCoupling A`.

Combined with the witness capstone (#3679), the entire route reduces to exhibiting
one sector eigenvector `φ` at the predicted ground energy
`predicted − s_A(s_A+1) − s_B(s_B+1)`: then `μ ≤` that value is exactly the
hypothesis `hμ` of #3679.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Toy ground energy is minimal in its sector**: the Marshall-positive toy
ground state (energy `μ`) has `μ ≤ E` for every sector eigenvector `φ ≠ 0` of the
toy Heisenberg sector matrix at real energy `E`. -/
theorem tasaki23_toy_sector_groundEnergy_le_of_witness
    (A : V → Bool) (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    {μ E : ℝ} {w φ : magConfigS V N M → ℝ}
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec w = μ • w)
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ = E • φ) :
    μ ≤ E := by
  refine heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
    A N c (bipartiteCoupling_im A) ?_ (fun x y => bipartiteCoupling_nonneg A x y)
    (bipartiteCoupling_symm A) (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
    hc_strict hw hw_marshall_pos hφ_ne hφ
  intro x y
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.mpr (bipartiteCoupling_im A x y)

end LatticeSystem.Quantum
