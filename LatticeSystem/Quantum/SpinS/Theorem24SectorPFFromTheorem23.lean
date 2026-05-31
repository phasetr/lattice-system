import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall
import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Quantum.SpinS.Theorem23StructuralReach

/-!
# Sector Perron--Frobenius simplicity from a Theorem 2.3 witness

This file packages the remaining sector Perron--Frobenius simplicity input
needed by the Tasaki §2.5 Theorem 2.4 SU(2)-endpoint bridge.  A
Marshall-positive real sector ground vector gives a positive eigenvector of the
shifted dressed non-negative irreducible sector matrix; Perron--Frobenius
geometric simplicity, the shift correspondence, real-to-complex transfer, and
the sector Marshall diagonal similarity give `finrank <= 1` for the bare
complex Heisenberg sector matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3--2.4, pp. 42-44; E. Lieb and D. Mattis,
J. Math. Phys. 3 (1962), 749.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The Marshall diagonal sign matrix on a fixed magnetization sector. -/
noncomputable def marshallDiagonalOnMagSector (A : V → Bool) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℂ :=
  Matrix.diagonal (fun σ : magConfigS V N M => ((marshallSignS A σ.1).re : ℂ))

/-- The sector Marshall diagonal is involutive. -/
theorem marshallDiagonalOnMagSector_mul_self (A : V → Bool) (M : ℕ) :
    marshallDiagonalOnMagSector (V := V) (N := N) A M *
      marshallDiagonalOnMagSector (V := V) (N := N) A M = 1 := by
  rw [marshallDiagonalOnMagSector, Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : magConfigS V N M =>
        ((marshallSignS A σ.1).re : ℂ) * ((marshallSignS A σ.1).re : ℂ)) =
      (fun _ => (1 : ℂ)) from by
        funext σ
        have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
          marshallSignS_re_sq A σ.1
        calc
          ((marshallSignS A σ.1).re : ℂ) * ((marshallSignS A σ.1).re : ℂ) =
              (((marshallSignS A σ.1).re * (marshallSignS A σ.1).re : ℝ) : ℂ) := by
                norm_num
          _ = 1 := by rw [hsq]; norm_num]
  exact Matrix.diagonal_one

/-- The complexified dressed real sector matrix is the Marshall conjugate of
the bare complex Heisenberg sector matrix. -/
theorem dressedHeisenbergSReMatrixOnMagSector_map_eq_marshall_conj_heisenberg
    (A : V → Bool) {J : V → V → ℂ} (N M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).map ((↑) : ℝ → ℂ) =
      marshallDiagonalOnMagSector (V := V) (N := N) A M *
        heisenbergHamiltonianSMatrixOnMagSector J N M *
        marshallDiagonalOnMagSector (V := V) (N := N) A M := by
  ext σ τ
  rw [Matrix.map_apply, marshallDiagonalOnMagSector, Matrix.mul_diagonal,
    Matrix.diagonal_mul, dressedHeisenbergSReMatrixOnMagSector_apply,
    heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal N M hJ_real,
    dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg A N hJ_real,
    heisenbergHamiltonianSReMatrixOnMagSector_apply]
  push_cast
  ring_nf

/-- **Sector-matrix PF simplicity from a Marshall-positive sector witness**:
if the Marshall-signed vector `σ ↦ marshallSignS A σ * v σ` is a real
Heisenberg sector eigenvector at `μ` and `v` is strictly positive, then the
bare complex Heisenberg sector matrix has eigenspace `finrank <= 1` at `μ`. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive
    (A : V → Bool) {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
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
    isIrreducible_shiftedDressedSReMatrixOnMagSector (N := N) (M := M)
      A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hA_ne hB_ne hN
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
