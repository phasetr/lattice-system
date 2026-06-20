import LatticeSystem.Quantum.SpinS.ConnectedSectorIrreducible
import LatticeSystem.Quantum.SpinS.Theorem24SectorPFFromTheorem23

/-!
# Connected-coupling per-sector ground-state uniqueness (`finrank <= 1`)

(Issue #4617, step 1): the connected-graph analogue of
`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive`
(`Theorem24SectorPFFromTheorem23.lean`).

The complete-bipartite version derives the Perron–Frobenius irreducibility of the
shifted dressed sector matrix from the *complete* strict positivity hypothesis
`hJ_pos` (on `(bipartiteCompleteGraphOf A).Adj`).  Every other step of that proof
— the Marshall-positive eigenvector, the shift correspondence, the
real-to-complex transfer, and the Marshall diagonal similarity — depends only on
the irreducibility fact and the positive eigenvector, not on the graph.

This file mirrors that proof verbatim, replacing only the irreducibility input by
the connected analogue `isIrreducible_shiftedDressedSReMatrixOnMagSector_connected`
(`ConnectedSectorIrreducible.lean`).  Strict positivity of `J` is therefore
required only on the edges of a *connected* bipartite graph `G` (`hJ_pos_G`); the
complete-graph data `hA_ne`/`hB_ne`/`hN` are no longer needed and are dropped.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3--2.4, pp. 42-44; E. Lieb and D. Mattis,
J. Math. Phys. 3 (1962), 749.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Connected-coupling sector-matrix PF simplicity from a Marshall-positive
sector witness**: if the Marshall-signed vector `σ ↦ marshallSignS A σ * v σ` is a
real Heisenberg sector eigenvector at `μ` and `v` is strictly positive, then for a
*connected* bipartite coupling graph `G` the bare complex Heisenberg sector matrix
has eigenspace `finrank <= 1` at `μ`.

Connected-graph analogue of
`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive`:
strict positivity of `J` is required only on the edges of the connected bipartite
graph `G` (`hJ_pos_G`), and the complete-graph data `hA_ne`/`hB_ne`/`hN` are
dropped. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
    (A : V → Bool) {G : SimpleGraph V} {J : V → V → ℂ}
    (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hv_heis : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) (μ : ℂ)) ≤ 1 := by
  classical
  let w : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * v σ
  have hw_heis : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w =
      μ • w := by
    simpa [w] using hv_heis
  let u : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * w σ
  have hu_pos : ∀ σ, 0 < u σ := by
    intro σ
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    have hu_eq : u σ = v σ := by
      dsimp [u, w]
      rw [← mul_assoc, hsq, one_mul]
    simpa [hu_eq] using hv_pos σ
  have hu_dressed : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec u =
      μ • u := by
    have h := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
      (N := N) (M := M) A hJ_real hw_heis
    simpa [u, w] using h
  have hu_shifted :
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec u = (c - μ) • u :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c hu_dressed
  have hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible :=
    isIrreducible_shiftedDressedSReMatrixOnMagSector_connected (N := N) (M := M)
      A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc_strict
  have h_shift :
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (shiftedDressedSReMatrixOnMagSector A J N c M)) (c - μ)) ≤ 1 :=
    LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
      hIrred hu_shifted hu_pos
  have h_dressed_real :
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (dressedHeisenbergSReMatrixOnMagSector A J N M)) μ) ≤ 1 := by
    have hdef := shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed A J N c M
    rw [hdef] at h_shift
    rw [eigenspace_smul_one_sub_finrank_eq] at h_shift
    convert h_shift using 4 <;> ring_nf
  have h_complex_dressed :=
    matrix_complex_eigenspace_finrank_le_one_of_real
      (dressedHeisenbergSReMatrixOnMagSector A J N M) μ h_dressed_real
  have h_similarity_finrank :=
    matrix_similar_eigenspace_finrank_eq
      (marshallDiagonalOnMagSector_mul_self (V := V) (N := N) A M)
      (marshallDiagonalOnMagSector_mul_self (V := V) (N := N) A M)
      (dressedHeisenbergSReMatrixOnMagSector_map_eq_marshall_conj_heisenberg
        (V := V) A N M hJ_real) (μ : ℂ)
  rw [h_similarity_finrank] at h_complex_dressed
  exact h_complex_dressed

end LatticeSystem.Quantum
