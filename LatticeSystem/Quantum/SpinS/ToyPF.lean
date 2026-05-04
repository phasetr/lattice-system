import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.ToyHamiltonian

/-!
# Spin-`S` MLM matrix-level Tasaki (2.5.4) for the toy Hamiltonian

Spin-`S` analog of `Quantum/MarshallLiebMattis/ToyPF.lean`. Specialises
the matrix-level MLM result for the spin-`S` shifted dressed
Heisenberg matrix on a magnetization sector
(`exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector` and
`pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector` from
`DressedMatrixOnMagSector.lean`) to the **toy Hamiltonian** with
`J = bipartiteCoupling A` (Tasaki §2.5 eq. (2.5.10) without the
`1/|Λ|` factor).

For `c` strictly larger than every diagonal entry of the dressed toy
matrix `M_toy_S = dressedHeisenbergSReMatrix A (bipartiteCoupling A) N`
and a non-empty magnetization sector `magConfigS V N M`, the shifted
toy matrix `B_toy_S = c · I − M_toy_S` admits a
**unique-up-to-positive-scalar strictly positive eigenvector** for
some real eigenvalue.

Together with the Casimir identity (PR #1056) and the closed form of
`Ĥ_toy_S` (PR #1060), this is the spin-`S` instance of the
matrix-level MLM (Tasaki §2.5 (2.5.4)). Subsequent PRs use this to
derive `S_tot = 0` for the AFM Heisenberg ground state in
`magConfigS V N (|V|·N/2)` and to extend to Tasaki §2.5 Theorem 2.3
(`|A| ≠ |B|`).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 pp. 40–41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bipartite coupling has positive real part on every edge of
`bipartiteCompleteGraphOf A`: distinct vertices on opposite
sublattices. -/
private theorem bipartiteCoupling_pos_on_bipartiteCompleteGraph
    (A : V → Bool) :
    ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y →
      0 < (bipartiteCoupling A x y).re := by
  intro x y hadj
  rw [bipartiteCompleteGraphOf_adj_iff] at hadj
  exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2

/-- **Spin-`S` matrix-level Tasaki (2.5.4) for the toy Hamiltonian**:
existence of a strictly positive Perron eigenvector for the shifted
dressed toy matrix on a magnetization sector. -/
theorem dressedHeisenbergSShifted_toy_exists_pos_eigenvec_max
    (A : V → Bool) (N : ℕ) (c : ℝ) (M : ℕ)
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (r : ℝ) (v : magConfigS V N M → ℝ),
      0 < r ∧ (∀ σ, 0 < v σ) ∧
      (shiftedDressedSReMatrixOnMagSector A
        (bipartiteCoupling A) N c M).mulVec v = r • v :=
  exists_positive_eigenvector_shiftedDressedSReMatrixOnMagSector
    A N c (bipartiteCoupling_im A)
    (bipartiteCoupling_pos_on_bipartiteCompleteGraph A)
    (fun x y => bipartiteCoupling_nonneg A x y)
    (bipartiteCoupling_symm A)
    (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
    hc_strict
    h_intermediate

/-- **Uniqueness up to positive scalar** for the spin-`S` toy
Hamiltonian's PF eigenvector on a magnetization sector. -/
theorem dressedHeisenbergSShifted_toy_pos_eigenvec_unique
    (A : V → Bool) (N : ℕ) (c : ℝ) (M : ℕ)
    [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A
        (bipartiteCoupling A) N c M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A
        (bipartiteCoupling A) N c M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector
    A N c (bipartiteCoupling_im A)
    (bipartiteCoupling_pos_on_bipartiteCompleteGraph A)
    (fun x y => bipartiteCoupling_nonneg A x y)
    (bipartiteCoupling_symm A)
    (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
    hc_strict
    h_intermediate
    hv hv_pos hw hw_pos

end LatticeSystem.Quantum
