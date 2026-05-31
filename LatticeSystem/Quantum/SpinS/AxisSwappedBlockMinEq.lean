import LatticeSystem.Quantum.SpinS.BlockSumFinrankEq
import LatticeSystem.Quantum.SpinS.BlockEigBotBelowJointMin
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian

/-!
# axisSwapped `hermitianMinEigenvalue` = `min` over parity-block min eigenvalues

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For the axis-swapped anisotropic Hamiltonian `Ĥ'` at real `(J, λ, D)` with both
parity sectors non-empty, the global minimum eigenvalue equals the minimum of
the two parity-block min eigenvalues.

Combines:
- `axisSwappedAnisotropicHeisenbergS_eigenspace_eq_bot_of_real_lt_both_block_mins`
  (existing, joint-min upper bound on `axisSwap global min`).
- `matrix_eigenspace_finrank_eq_sum_parity_blocks` (PR #3842, block-sum
  finrank equality).
- `exists_nonzero_eigenvector_hermitianMinEigenvalue` (PR #3962, min eigenvec
  existence).

Used by the obligation (2) IVT crossing argument: combined with the axis-swap
bridge (PR #3968), transfers the obligation (1) `≤ 2` bound from the axis-swapped
per-parity form (PR #3888) to the original `Ĥ`'s global min eigenvalue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The full axisSwapped Hamiltonian is Hermitian under real `(J, λ, D)`
expressed via `im = 0`. Adapter to the existing `_isHermitian_of_real`
(which uses `star`). -/
private theorem axisSwapped_full_isHermitian_im
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) :
    (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).IsHermitian :=
  axisSwappedAnisotropicHeisenbergS_isHermitian_of_real
    (fun x y => by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJ x y)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD)
    N

/-- **axisSwap global min ≥ min of parity-block mins** (direction 1): if the
global min were strictly less than both block mins, the eigenspace at that
energy would be bot (via the joint-min ⊥-below lemma), contradicting that the
min eigenvalue IS an eigenvalue. -/
theorem hermitianMinEigenvalue_axisSwapped_ge_min_block_mins
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)] :
    min (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJ hlam hD 0))
        (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJ hlam hD 1)) ≤
      hermitianMinEigenvalue (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) := by
  classical
  by_contra hlt
  push_neg at hlt
  have h0_lt : hermitianMinEigenvalue (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) <
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJ hlam hD 0) := lt_of_lt_of_le hlt (min_le_left _ _)
  have h1_lt : hermitianMinEigenvalue (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) <
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJ hlam hD 1) := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨v, hv_ne, hv_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD)
  have hbot := axisSwappedAnisotropicHeisenbergS_eigenspace_eq_bot_of_real_lt_both_block_mins
    hJ hlam hD hJself h0_lt h1_lt
  apply hv_ne
  have hv_mem : v ∈ End.eigenspace (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((hermitianMinEigenvalue
          (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) : ℝ) : ℂ) := by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hv_eig
  rw [hbot] at hv_mem
  exact hv_mem

/-- **axisSwap global min ≤ each parity-block min** (direction 2): each block
min eigenvalue is in the full axisSwapped spectrum via the block-sum finrank
equality. -/
theorem hermitianMinEigenvalue_axisSwapped_le_parity_block_min
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)] (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hp : p = 0 ∨ p = 1) :
    hermitianMinEigenvalue (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) ≤
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJ hlam hD p) := by
  classical
  set μp := hermitianMinEigenvalue
    (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
      (Λ := Λ) (N := N) hJ hlam hD p) with hμp_def
  obtain ⟨v_block, hv_ne, hv_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJ hlam hD p)
  have hbs := matrix_eigenspace_finrank_eq_sum_parity_blocks
    (M := axisSwappedAnisotropicHeisenbergS J lam D N)
    (by
      intro σ τ hne_par
      have hne : σ ≠ τ := fun h => hne_par (by rw [h])
      have hodd : Odd (magSumS σ + magSumS τ) := by
        rw [Nat.odd_iff]
        have h1 : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have h2 : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      exact axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hne hodd)
    (axisSwappedAnisotropicHeisenbergS_commute_magParityDiagS hJself lam D)
    ((μp : ℝ) : ℂ)
  have hpos_p : 1 ≤ finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) ((μp : ℝ) : ℂ)) := by
    have hv_mem : v_block ∈ End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) ((μp : ℝ) : ℂ) := by
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hv_eig
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v_block, hv_mem⟩, by
      intro h
      apply hv_ne
      exact congrArg Subtype.val h⟩
  have hfull_pos : 1 ≤ finrank ℂ (End.eigenspace (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) ((μp : ℝ) : ℂ)) := by
    rcases hp with rfl | rfl
    · rw [hbs]; omega
    · rw [hbs]; omega
  have hne_bot : End.eigenspace (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) ((μp : ℝ) : ℂ) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hfull_pos
    simp at hfull_pos
  have hHerm := axisSwapped_full_isHermitian_im (N := N) hJ hlam hD
  have hHE : Module.End.HasEigenvalue (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) ((μp : ℝ) : ℂ) := hne_bot
  have h_mem_C : ((μp : ℝ) : ℂ) ∈ spectrum ℂ
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N) := by
    rw [← Matrix.spectrum_toLin']
    exact hHE.mem_spectrum
  have h_mem_R : μp ∈ spectrum ℝ
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N) := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]; exact h_mem_C
  rw [hHerm.spectrum_real_eq_range_eigenvalues] at h_mem_R
  obtain ⟨i, hi⟩ := h_mem_R
  rw [← hi]
  exact hermitian_min_eigenvalue_le hHerm i

/-- **axisSwap `hermitianMinEigenvalue` = min over parity-block min eigenvalues**. -/
theorem hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)] :
    hermitianMinEigenvalue (axisSwapped_full_isHermitian_im (N := N) hJ hlam hD) =
      min (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1)) := by
  apply le_antisymm
  · exact le_min
      (hermitianMinEigenvalue_axisSwapped_le_parity_block_min hJ hlam hD hJself 0 (Or.inl rfl))
      (hermitianMinEigenvalue_axisSwapped_le_parity_block_min hJ hlam hD hJself 1 (Or.inr rfl))
  · exact hermitianMinEigenvalue_axisSwapped_ge_min_block_mins hJ hlam hD hJself

end LatticeSystem.Quantum
