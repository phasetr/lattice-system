import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPathFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergAxisSwapMinEigenvalue
import LatticeSystem.Quantum.SpinS.AxisSwappedBlockMinEq
import LatticeSystem.Quantum.SpinS.BareSubmatrixBoundAtMin

/-!
# Case (ii): parity-block simplicity from PF/min path data

This file is part of the Tasaki §2.5 Theorem 2.4 case-(ii) bridge.
PR #4106 reduced the target statement to axis-swapped parity-block submatrix
`finrank <= 1` at the full ground energy along the deformation path.  The
lemmas here turn the existing bare-submatrix conditional theorem into exactly
that pathwise input: if a parity block has a PF `finrank <= 1` bound at a real
number `ν` and `ν` is the Hermitian minimum of that block, then the same block
has `finrank <= 1` at the full anisotropic ground energy.  If the full ground
energy is lower than that block minimum, the block eigenspace is `⊥` by the
Hermitian below-minimum exclusion.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Parity-block `finrank <= 1` at the full ground energy from PF/min data**.

For `p = 0` or `p = 1`, assume a bare axis-swapped parity block has a
`finrank <= 1` bound at `ν`, and that `ν` is the Hermitian minimum eigenvalue
of that block.  Since the full anisotropic ground energy equals the minimum of
the two axis-swapped parity-block minima, either it is this block minimum
itself, or it is strictly below this block minimum and the block eigenspace is
`⊥`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min
    {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0)
    (hJself : ∀ x, J x x = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ} (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hp : p = 0 ∨ p = 1)
    (ν : ℝ)
    (hν_bound : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1)
    (hν_eq_min : ν = hermitianMinEigenvalue
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) p)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) : ℝ) : ℂ)) ≤
      1 := by
  classical
  let hBlock : ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)).IsHermitian :=
    axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
      (Λ := Λ) (N := N) hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) p
  have h_at_block_min :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)))
        ((hermitianMinEigenvalue hBlock : ℝ) : ℂ)) ≤ 1 := by
    exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
      (Λ := Λ) (N := N) (J := J) (lam := (lam : ℂ)) (D := (D : ℂ))
      hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) p ν hν_bound hν_eq_min
  have hblock_eq := hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    (Λ := Λ) (N := N) (J := J) (lam := (lam : ℂ)) (D := (D : ℂ))
    hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) hJself
  have hswap_eq := axisSwapUnitarySSpinS_hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    (Λ := Λ) (N := N) (J := J) (lam := (lam : ℂ)) (D := (D : ℂ))
    hJ_star (star_ofReal_eq lam) (star_ofReal_eq D)
  have henergy_eq :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) =
        min (hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) 0))
            (hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) 1)) := by
    rw [hswap_eq, hblock_eq]
  have hle_full_block :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) ≤
        hermitianMinEigenvalue hBlock := by
    rcases hp with rfl | rfl
    · rw [henergy_eq]
      exact min_le_left _ _
    · rw [henergy_eq]
      exact min_le_right _ _
  rcases lt_or_eq_of_le hle_full_block with hlt | heq
  · have hbot : End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) : ℝ) :
            ℂ) = ⊥ :=
      hermitian_eigenspace_eq_bot_of_real_lt_min hBlock hlt
    rw [hbot]
    simp
  · rw [heq]
    exact h_at_block_min

/-- **Pathwise parity-block inputs from PF/min callbacks**.

This packages the previous lemma for the two parity blocks along the case-(ii)
deformation path.  The remaining callbacks are exactly the PF simplicity bound
and PF/min identification for the even and odd bare axis-swapped parity blocks. -/
theorem caseII_axisSwapped_submatrix_blocks_path_of_pf_min
    {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0)
    (hJself : ∀ x, J x x = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (h_even_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 0 => σ.1)
              (fun σ : parityConfigS Λ N 0 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 0))
    (h_odd_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 1 => σ.1)
              (fun σ : parityConfigS Λ N 1 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 1)) :
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1) ∧
      (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1) := by
  constructor
  · intro t ht
    rcases h_even_pf t ht with ⟨ν, hν_bound, hν_eq_min⟩
    exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min
      (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star
      (lam := (anisotropicHeisenbergParametricPath lam D t).1)
      (D := (anisotropicHeisenbergParametricPath lam D t).2)
      0 (Or.inl rfl) ν hν_bound hν_eq_min
  · intro t ht
    rcases h_odd_pf t ht with ⟨ν, hν_bound, hν_eq_min⟩
    exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min
      (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star
      (lam := (anisotropicHeisenbergParametricPath lam D t).1)
      (D := (anisotropicHeisenbergParametricPath lam D t).2)
      1 (Or.inr rfl) ν hν_bound hν_eq_min

/-- **General spin-S case-(ii) target uniqueness from pathwise parity-block
PF/min callbacks**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_block_pf_min_path
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M lam D 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2))
    (h_even_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 0 => σ.1)
              (fun σ : parityConfigS Λ N 0 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 0))
    (h_odd_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 1 => σ.1)
              (fun σ : parityConfigS Λ N 1 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 1)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  rcases caseII_axisSwapped_submatrix_blocks_path_of_pf_min
      (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star h_even_pf h_odd_pf with
    ⟨h_even, h_odd⟩
  exact anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_axisSwapped_submatrix_blocks_path
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2 h_even h_odd

set_option linter.style.longLine false in
/-- **General spin-S case-(ii) target zero magnetization from pathwise
parity-block PF/min callbacks**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_block_pf_min_path
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M lam D 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2))
    (h_even_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 0 => σ.1)
              (fun σ : parityConfigS Λ N 0 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 0))
    (h_odd_pf :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∃ ν : ℝ,
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
              (fun σ : parityConfigS Λ N 1 => σ.1)
              (fun σ : parityConfigS Λ N 1 => σ.1))) (ν : ℂ)) ≤ 1 ∧
            ν = hermitianMinEigenvalue
              (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
                (Λ := Λ) (N := N) hJim
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).1)
                  (Complex.ofReal_im (anisotropicHeisenbergParametricPath lam D t).2) 1))
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  rcases caseII_axisSwapped_submatrix_blocks_path_of_pf_min
      (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star h_even_pf h_odd_pf with
    ⟨h_even, h_odd⟩
  exact anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_axisSwapped_submatrix_blocks_path
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2 h_even h_odd hΦ_ne hΦ_gs

end LatticeSystem.Quantum
