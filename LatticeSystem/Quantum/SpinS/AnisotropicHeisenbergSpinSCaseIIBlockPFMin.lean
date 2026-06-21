import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIConditionalBridge
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPathFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityBlockPFMin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergAxisSwapMinEigenvalue
import LatticeSystem.Quantum.SpinS.AxisSwappedBlockMinEq
import LatticeSystem.Quantum.SpinS.BareSubmatrixBoundAtMin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPFMinCore

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

omit [Fintype Λ] [DecidableEq Λ] in
/-- Coupling support vanishes off the bipartite complete graph from no
self-coupling and the usual bipartite support predicate. -/
lemma caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y) :
    ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0 := by
  intro x y hnot
  by_contra hJxy_ne
  have hxy : x ≠ y := by
    intro hxy
    exact hJxy_ne (by simpa [hxy] using hJself x)
  exact hnot ⟨hxy, hJbip x y hJxy_ne⟩

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
  exact
      anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_axisSwapped_submatrix_blocks_path
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2 h_even h_odd hΦ_ne hΦ_gs

/-- **General spin-S case-(ii) target uniqueness from raw-support PF/min
inputs**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_raw_support_pf_min_path
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
    (h_even_strict :
      axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_lambda_one :
      axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_D_zero :
      axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_strict :
      axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_lambda_one :
      axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_D_zero :
      axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  have hJsupp :=
    caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj
      (Λ := Λ) A hJself hJbip
  rcases caseII_axisSwapped_parityBlockPFMinPath_of_raw_support
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii h_even_strict h_even_lambda_one h_even_D_zero
      h_even_corner h_odd_strict h_odd_lambda_one h_odd_D_zero h_odd_corner with
    ⟨h_even_pf, h_odd_pf⟩
  exact anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_block_pf_min_path
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2 h_even_pf h_odd_pf

/-- **General spin-S case-(ii) target zero magnetization from raw-support
PF/min inputs**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_raw_support_pf_min_path
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
    (h_even_strict :
      axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_lambda_one :
      axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_D_zero :
      axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D 0)
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_strict :
      axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_lambda_one :
      axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_D_zero :
      axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D 1)
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  have huniq :=
    anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_raw_support_pf_min_path
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
      h_strict_gap_at_SU2 h_GS_at_SU2 h_even_strict h_even_lambda_one
      h_even_D_zero h_even_corner h_odd_strict h_odd_lambda_one h_odd_D_zero
      h_odd_corner
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

/-- **General spin-S case-(ii) target uniqueness from reachability PF/min
inputs**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_reachability_pf_min_path
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
    (h_even_strict_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_lambda_one_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_D_zero_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_strict_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_lambda_one_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_D_zero_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  have hJsupp :=
    caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj
      (Λ := Λ) A hJself hJbip
  rcases caseII_axisSwapped_parityBlockPFMinPath_of_reachability
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii h_even_strict_reach h_even_lambda_one_reach
      h_even_D_zero_reach h_even_corner h_odd_strict_reach h_odd_lambda_one_reach
      h_odd_D_zero_reach h_odd_corner with
    ⟨h_even_pf, h_odd_pf⟩
  exact anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_block_pf_min_path
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2 h_even_pf h_odd_pf

/-- **General spin-S case-(ii) target zero magnetization from reachability
PF/min inputs**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_reachability_pf_min_path
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
    (h_even_strict_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_lambda_one_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_D_zero_reach :
      ∀ σ' σ : parityConfigS Λ N 0, σ' ≠ σ →
        bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_strict_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_lambda_one_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_D_zero_reach :
      ∀ σ' σ : parityConfigS Λ N 1, σ' ≠ σ →
        bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  have huniq :=
    anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_reachability_pf_min_path
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced hlam_case_ii hD_case_ii h_centered_nonzero
      h_strict_gap_at_SU2 h_GS_at_SU2 h_even_strict_reach h_even_lambda_one_reach
      h_even_D_zero_reach h_even_corner h_odd_strict_reach h_odd_lambda_one_reach
      h_odd_D_zero_reach h_odd_corner
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
