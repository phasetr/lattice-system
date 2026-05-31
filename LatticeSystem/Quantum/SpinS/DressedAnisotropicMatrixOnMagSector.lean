import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergImZero
import LatticeSystem.Quantum.SpinS.Theorem24SectorPFFromTheorem23

/-!
# Dressed anisotropic sector matrix

This file starts the target-sector Perron--Frobenius input for Tasaki §2.5
Theorem 2.4.  On a fixed magnetization sector, the anisotropic Hamiltonian has
real entries under real coefficients.  Marshall conjugation therefore gives a
real dressed sector matrix whose off-diagonal entries agree with the isotropic
Heisenberg dressed sector matrix, because the anisotropy and single-ion terms
are diagonal in the configuration basis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Real and dressed sector matrices -/

/-- The real part of the anisotropic Hamiltonian restricted to a fixed
magnetization sector. -/
noncomputable def anisotropicHeisenbergSReMatrixOnMagSector
    (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) :
    Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ :=
  fun σ τ => (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ).re

/-- Component-wise unfolding of `anisotropicHeisenbergSReMatrixOnMagSector`. -/
theorem anisotropicHeisenbergSReMatrixOnMagSector_apply
    (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ)
    (σ τ : magConfigS Λ N M) :
    anisotropicHeisenbergSReMatrixOnMagSector J lam D N M σ τ =
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ).re := rfl

/-- The complexification of the real anisotropic sector matrix is the bare
complex sector matrix when all entries are real. -/
theorem anisotropicHeisenbergSReMatrixOnMagSector_map_eq_submatrix
    {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0) (N M : ℕ) :
    (anisotropicHeisenbergSReMatrixOnMagSector (Λ := Λ) J lam D N M).map
        ((↑) : ℝ → ℂ) =
      anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M := by
  ext σ τ
  rw [Matrix.map_apply, anisotropicHeisenbergSReMatrixOnMagSector_apply]
  exact Complex.ext (by simp) (by
    simp [anisotropicHeisenbergS_magSector_submatrix_im_zero hJim hlam hDim M σ τ])

/-- The Marshall-dressed real anisotropic Hamiltonian on a fixed magnetization
sector. -/
noncomputable def dressedAnisotropicHeisenbergSReMatrixOnMagSector
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) :
    Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ :=
  fun σ τ =>
    (marshallSignS A σ.1).re *
      anisotropicHeisenbergSReMatrixOnMagSector J lam D N M σ τ *
        (marshallSignS A τ.1).re

/-- Component-wise unfolding of the dressed anisotropic sector matrix. -/
theorem dressedAnisotropicHeisenbergSReMatrixOnMagSector_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ)
    (σ τ : magConfigS Λ N M) :
    dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ τ =
      (marshallSignS A σ.1).re *
        anisotropicHeisenbergSReMatrixOnMagSector J lam D N M σ τ *
          (marshallSignS A τ.1).re := rfl

/-- Off the diagonal, the dressed anisotropic sector matrix agrees with the
dressed isotropic Heisenberg sector matrix. -/
theorem dressedAnisotropicHeisenbergSReMatrixOnMagSector_offdiag_eq_dressedHeisenberg
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (lam D : ℂ) (N M : ℕ) {σ τ : magConfigS Λ N M} (hne : σ ≠ τ) :
    dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ τ =
      dressedHeisenbergSReMatrixOnMagSector A J N M σ τ := by
  have hne_val : σ.1 ≠ τ.1 := fun h => hne (Subtype.ext h)
  rw [dressedAnisotropicHeisenbergSReMatrixOnMagSector_apply,
    anisotropicHeisenbergSReMatrixOnMagSector_apply,
    anisotropicHeisenbergS_magSector_submatrix, Matrix.submatrix_apply,
    anisotropicHeisenbergS_apply_offdiag_eq_heisenberg J lam D hne_val,
    dressedHeisenbergSReMatrixOnMagSector_apply,
    dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg A N hJ_real,
    heisenbergHamiltonianSReMatrix_apply]
  ring

/-- The dressed anisotropic sector matrix is symmetric for real coefficients. -/
theorem dressedAnisotropicHeisenbergSReMatrixOnMagSector_isSymm
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, star (J x y) = J x y)
    (hlam : lam.im = 0) (hDim : D.im = 0)
    (N M : ℕ) :
    (dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M).IsSymm := by
  have hH : (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M).IsHermitian :=
    anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
      (Λ := Λ) (N := N) (M := M) hJ
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hDim)
  ext σ τ
  rw [Matrix.transpose_apply, dressedAnisotropicHeisenbergSReMatrixOnMagSector_apply,
    dressedAnisotropicHeisenbergSReMatrixOnMagSector_apply,
    anisotropicHeisenbergSReMatrixOnMagSector_apply,
    anisotropicHeisenbergSReMatrixOnMagSector_apply]
  have hswap := congrFun (congrFun hH τ) σ
  rw [Matrix.conjTranspose_apply] at hswap
  have hmid : (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M τ σ).re =
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ).re := by
    rw [← hswap, Complex.star_def, Complex.conj_re]
  rw [hmid]
  ring

/-- The complexified dressed anisotropic sector matrix is the Marshall
conjugate of the bare complex anisotropic sector matrix. -/
theorem dressedAnisotropicHeisenbergSReMatrixOnMagSector_map_eq_marshall_conj
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0) (N M : ℕ) :
    (dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M).map
        ((↑) : ℝ → ℂ) =
      marshallDiagonalOnMagSector (V := Λ) (N := N) A M *
        anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M *
          marshallDiagonalOnMagSector (V := Λ) (N := N) A M := by
  ext σ τ
  rw [Matrix.map_apply, marshallDiagonalOnMagSector, Matrix.mul_diagonal,
    Matrix.diagonal_mul, dressedAnisotropicHeisenbergSReMatrixOnMagSector_apply,
    anisotropicHeisenbergSReMatrixOnMagSector_apply]
  have him := anisotropicHeisenbergS_magSector_submatrix_im_zero
    (Λ := Λ) (N := N) hJim hlam hDim M σ τ
  have hentry : (((anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ).re : ℂ) =
      anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ) := by
    exact Complex.ext (by simp) (by simp [him])
  push_cast
  rw [hentry]

/-! ## Shifted matrix -/

/-- The shifted dressed anisotropic sector matrix `c • 1 - dressed`. -/
noncomputable def shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) (c : ℝ) :
    Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ :=
  c • 1 - dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M

/-- Component-wise unfolding of the shifted dressed anisotropic sector matrix. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) (c : ℝ)
    (σ τ : magConfigS Λ N M) :
    shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c σ τ =
      (c • 1 - dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M) σ τ := rfl

/-- The shifted dressed anisotropic sector matrix is definitionally
`c • 1 - dressed`. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_eq_smul_sub_dressed
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) (c : ℝ) :
    shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c =
      c • 1 - dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M := rfl

/-- Diagonal entries of the shifted dressed anisotropic sector matrix. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) (c : ℝ)
    (σ : magConfigS Λ N M) :
    shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c σ σ =
      c - dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ := by
  rw [shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply]
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- Off-diagonal entries of the shifted dressed anisotropic sector matrix. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_off_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N M : ℕ) (c : ℝ)
    {σ τ : magConfigS Λ N M} (hne : σ ≠ τ) :
    shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c σ τ =
      -dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ τ := by
  rw [shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply]
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- The shifted dressed anisotropic sector matrix is entrywise non-negative
under the standard bipartite antiferromagnetic hypotheses and a strict diagonal
shift. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (lam D : ℂ) (N M : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ : magConfigS Λ N M,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ < c)
    (σ τ : magConfigS Λ N M) :
    0 ≤ shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c σ τ := by
  by_cases hστ : σ = τ
  · subst hστ
    rw [shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_diag]
    linarith [hc_strict σ]
  · rw [shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_off_diag
      A J lam D N M c hστ,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector_offdiag_eq_dressedHeisenberg
        A hJ_real lam D N M hστ,
      dressedHeisenbergSReMatrixOnMagSector_apply]
    have hne_val : σ.1 ≠ τ.1 := fun h => hστ (Subtype.ext h)
    have hnonneg := shiftedDressedSReMatrix_apply_off_diag_nonneg
      (V := Λ) A (N := N) (c := c) hJ_real hJ_nn hJ_sym hJ_bipartite hne_val
    rw [shiftedDressedSReMatrix_apply_off_diag A J N c hne_val] at hnonneg
    exact hnonneg

/-- The shifted dressed anisotropic sector matrix is strictly positive on a
bipartite raise/lower step. -/
theorem shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_step_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (lam D : ℂ) (N M : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : Λ, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : magConfigS Λ N M}
    (hstep : RaiseLowerStepSMagSector (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c τ σ := by
  have hne_val : τ.1 ≠ σ.1 := by
    obtain ⟨x, _y, _hadj, hshift, _hagree⟩ := hstep
    intro heq
    rcases hshift with ⟨hxr, _⟩ | ⟨hxl, _⟩
    · have : (τ.1 x).val = (σ.1 x).val := by rw [heq]
      omega
    · have : (τ.1 x).val = (σ.1 x).val := by rw [heq]
      omega
  have hne : τ ≠ σ := fun h => hne_val (congrArg Subtype.val h)
  rw [shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_off_diag
      A J lam D N M c hne,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector_offdiag_eq_dressedHeisenberg
        A hJ_real lam D N M hne]
  rw [dressedHeisenbergSReMatrixOnMagSector_apply]
  have hpos := shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector
    (V := Λ) A (N := N) (c := c) (M := M) hJ_real hJ_pos hJ_sym hstep
  rw [shiftedDressedSReMatrixOnMagSector_apply,
    shiftedDressedSReMatrix_apply_off_diag A J N c hne_val] at hpos
  exact hpos

/-- Matrix-power positivity for the shifted dressed anisotropic sector matrix
from raise/lower reachability. -/
theorem exists_matrixPow_pos_of_anisotropic_magConfigS_bipartite
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (lam D : ℂ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : Λ, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ : magConfigS Λ N M,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (σ σ' : magConfigS Λ N M) :
    ∃ k : ℕ,
      0 < (shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector
        A J lam D N M c ^ k) σ' σ := by
  apply exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector
  · intro σ τ
    exact shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_nonneg
      A lam D N M c hJ_real hJ_nn hJ_sym hJ_bipartite hc_strict σ τ
  · intro σ τ hstep
    exact shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_step_pos
      A lam D N M c hJ_real hJ_pos hJ_sym hstep
  · exact raiseLowerReachableSMagSector_bipartiteCompleteGraph A
      hA_ne hB_ne hN σ σ'

/-- Strict positive-length matrix-power positivity for distinct sector
configurations. -/
theorem exists_matrixPow_pos_length_of_anisotropic_magConfigS_bipartite
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (lam D : ℂ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : Λ, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ : magConfigS Λ N M,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {σ σ' : magConfigS Λ N M} (hne : σ ≠ σ') :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector
        A J lam D N M c ^ k) σ' σ := by
  obtain ⟨k, hpos⟩ := exists_matrixPow_pos_of_anisotropic_magConfigS_bipartite
    (N := N) (M := M) A lam D c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict hA_ne hB_ne hN σ σ'
  refine ⟨k, ?_, hpos⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pow_zero, Matrix.one_apply, if_neg (Ne.symm hne)] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hkpos

/-- The shifted dressed anisotropic sector matrix is irreducible under the
canonical structural reachability hypotheses. -/
theorem isIrreducible_shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (lam D : ℂ) (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : Λ, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ : magConfigS Λ N M,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    (shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_nonneg
      A lam D N M c hJ_real hJ_nn hJ_sym hJ_bipartite hc_strict)]
  intro σ τ
  by_cases hne : σ = τ
  · subst hne
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one, shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_apply_diag]
    linarith [hc_strict σ]
  · obtain ⟨k, hk_pos, hpos⟩ :=
      exists_matrixPow_pos_length_of_anisotropic_magConfigS_bipartite
        (N := N) (M := M) A lam D c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict hA_ne hB_ne hN (Ne.symm hne)
    exact ⟨k, hk_pos, hpos⟩

end LatticeSystem.Quantum
