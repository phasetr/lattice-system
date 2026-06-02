import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIConditionalBridge
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPathFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityBlockPFMin
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

/-- PF simplicity and PF/min identification for one bare axis-swapped parity
block at fixed real anisotropic parameters. -/
abbrev axisSwappedParityBlockPFMinAt
    (J : Λ → Λ → ℂ) (hJim : ∀ x y, (J x y).im = 0)
    (lam D : ℝ) (p : ℕ) [Nonempty (parityConfigS Λ N p)] : Prop :=
  ∃ ν : ℝ,
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 ∧
      ν = hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim (Complex.ofReal_im lam) (Complex.ofReal_im D) p)

/-- Pathwise PF simplicity and PF/min identification for one bare
axis-swapped parity block along the case-(ii) deformation path. -/
abbrev axisSwappedParityBlockPFMinPath
    (J : Λ → Λ → ℂ) (hJim : ∀ x y, (J x y).im = 0)
    (lam D : ℝ) (p : ℕ) [Nonempty (parityConfigS Λ N p)] : Prop :=
  ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
    axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
      (anisotropicHeisenbergParametricPath lam D t).1
      (anisotropicHeisenbergParametricPath lam D t).2 p

/-- Strict-interior raw-support data along the case-(ii) path for one
axis-swapped parity block. -/
abbrev axisSwappedParityBlockStrictRawSupportPath
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] : Prop :=
  ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
    1 < (anisotropicHeisenbergParametricPath lam D t).1 →
    (anisotropicHeisenbergParametricPath lam D t).2 < 0 →
      ∃ c : ℝ,
        (∀ σ : parityConfigS Λ N p,
          dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N
            σ.1 σ.1 < c) ∧
          (∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
            parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')

/-- `lambda = 1` ion-only raw-support data along the case-(ii) path for one
axis-swapped parity block. -/
abbrev axisSwappedParityBlockLambdaOneRawSupportPath
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] : Prop :=
  ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
    (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
    (anisotropicHeisenbergParametricPath lam D t).2 < 0 →
      ∃ c : ℝ,
        (∀ σ : parityConfigS Λ N p,
          dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J
            1 ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N
            σ.1 σ.1 < c) ∧
          (∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
            ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')

/-- `D = 0` bond-only raw-support data along the case-(ii) path for one
axis-swapped parity block. -/
abbrev axisSwappedParityBlockDZeroRawSupportPath
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] : Prop :=
  ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
    1 < (anisotropicHeisenbergParametricPath lam D t).1 →
    (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
      ∃ c : ℝ,
        (∀ σ : parityConfigS Λ N p,
          dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ) 0 N
            σ.1 σ.1 < c) ∧
          (∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
            bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ')

/-- A finite parity block has a strict real upper bound for any dressed diagonal
function. -/
lemma exists_parityBlock_dressed_diag_strict_upper_bound
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    ∃ c : ℝ, ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c := by
  classical
  let f : parityConfigS Λ N p → ℝ :=
    fun σ => dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1
  obtain ⟨σ₀, _hσ₀, hσ₀_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (parityConfigS Λ N p)) f
      Finset.univ_nonempty
  refine ⟨f σ₀ + 1, fun σ => ?_⟩
  have hle : f σ ≤ f σ₀ := hσ₀_max σ (Finset.mem_univ σ)
  linarith

/-- Strict-interior raw-support path data from strict block reachability
totality. -/
theorem axisSwappedParityBlockStrictRawSupportPath_of_reachability
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hreach_total :
      ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
        parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D p := by
  intro t _ht _hlam_gt _hD_lt
  obtain ⟨c, hc⟩ :=
    exists_parityBlock_dressed_diag_strict_upper_bound
      (Λ := Λ) (N := N) A J
      ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) p
  exact ⟨c, hc, hreach_total⟩

/-- `lambda = 1` raw-support path data from ion-only block reachability
totality. -/
theorem axisSwappedParityBlockLambdaOneRawSupportPath_of_reachability
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hreach_total :
      ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
        ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D p := by
  intro t _ht _hlam_eq _hD_lt
  obtain ⟨c, hc⟩ :=
    exists_parityBlock_dressed_diag_strict_upper_bound
      (Λ := Λ) (N := N) A J 1
      ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) p
  exact ⟨c, hc, hreach_total⟩

/-- `D = 0` raw-support path data from bond-only block reachability totality. -/
theorem axisSwappedParityBlockDZeroRawSupportPath_of_reachability
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℝ)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hreach_total :
      ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
        bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D p := by
  intro t _ht _hlam_gt _hD_eq
  obtain ⟨c, hc⟩ :=
    exists_parityBlock_dressed_diag_strict_upper_bound
      (Λ := Λ) (N := N) A J
      ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ) 0 p
  exact ⟨c, hc, hreach_total⟩

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

/-- **Pathwise parity-block PF/min callbacks from case-(ii) raw support**.

For a fixed parity block along the case-(ii) deformation path, this selects the
appropriate raw-support PF/min consumer at each path point: the strict
case-(ii) region, the `lambda = 1` boundary, or the `D = 0` boundary.  The
corner `(lambda, D) = (1, 0)` remains explicit as `hcorner`, since the strict
raw-support hypotheses used by the three consumers vanish there. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_path_of_caseII_raw_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hstrict : axisSwappedParityBlockStrictRawSupportPath (Λ := Λ) (N := N) A J lam D p)
    (hlambda_one :
      axisSwappedParityBlockLambdaOneRawSupportPath (Λ := Λ) (N := N) A J lam D p)
    (hD_zero : axisSwappedParityBlockDZeroRawSupportPath (Λ := Λ) (N := N) A J lam D p)
    (hcorner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 p) :
    axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D p := by
  intro t ht
  have ht_nn : 0 ≤ t := ht.1
  have hlam_ge :
      1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 :=
    anisotropicHeisenbergParametricPath_fst_ge_one_case_ii hlam_case_ii ht_nn
  have hD_le :
      (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 :=
    anisotropicHeisenbergParametricPath_snd_nonpos_case_ii hD_case_ii ht_nn
  rcases lt_or_eq_of_le hlam_ge with hlam_gt | hlam_eq
  · rcases lt_or_eq_of_le hD_le with hD_lt | hD_eq
    · rcases hstrict t ht hlam_gt hD_lt with ⟨c, hc_strict, hreach_total⟩
      exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
        (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
        (by simp)
        (by
          simp
          linarith)
        (by simpa using hlam_gt)
        (D := ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ))
        (by simp)
        (by simpa using hD_lt)
        (p := p) hc_strict hreach_total
    · rcases hD_zero t ht hlam_gt hD_eq with ⟨c, hc_strict, hreach_total⟩
      change axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2 p
      rw [hD_eq]
      exact
        axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_D_zero
          (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
          (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
          (by simp)
          (by
            simp
            linarith)
          (by simpa using hlam_gt)
          (p := p) hc_strict hreach_total
  · rcases lt_or_eq_of_le hD_le with hD_lt | hD_eq
    · rcases hlambda_one t ht hlam_eq.symm hD_lt with ⟨c, hc_strict, hreach_total⟩
      change axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2 p
      rw [← hlam_eq]
      exact
        axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_lambda_one
          (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
          (D := ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ))
          (by simp)
          (by simpa using hD_lt)
          (p := p) hc_strict hreach_total
    · exact hcorner t ht hlam_eq.symm hD_eq

/-- **Even and odd PF/min callbacks from case-(ii) raw support**.

This applies the single-block selector to both parity blocks.  The strict,
`lambda = 1`, `D = 0`, and corner inputs stay separated by parity so later
connectivity proofs can discharge them independently. -/
theorem caseII_axisSwapped_parityBlockPFMinPath_of_raw_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
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
    axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 0 ∧
      axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 1 := by
  constructor
  · exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_path_of_caseII_raw_support
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii 0 h_even_strict h_even_lambda_one h_even_D_zero
      h_even_corner
  · exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_path_of_caseII_raw_support
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii 1 h_odd_strict h_odd_lambda_one h_odd_D_zero
      h_odd_corner

/-- **Pathwise parity-block full-min bounds from case-(ii) raw support**.

This combines the raw-support PF/min selector for the even and odd blocks with
the block-minimum transfer to the full ground energy along the path. -/
theorem caseII_axisSwapped_submatrix_blocks_path_of_raw_support_pf_min
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
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
  rcases caseII_axisSwapped_parityBlockPFMinPath_of_raw_support
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii h_even_strict h_even_lambda_one h_even_D_zero
      h_even_corner h_odd_strict h_odd_lambda_one h_odd_D_zero h_odd_corner with
    ⟨h_even_pf, h_odd_pf⟩
  exact caseII_axisSwapped_submatrix_blocks_path_of_pf_min
    (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star h_even_pf h_odd_pf

/-- **Even and odd PF/min callbacks from case-(ii) reachability inputs**.

This removes the diagonal-shift component of the raw-support input surface:
finite parity blocks supply the strict shift automatically, so only the strict,
ion-only, bond-only reachability totality hypotheses and the corner PF/min
callbacks remain explicit. -/
theorem caseII_axisSwapped_parityBlockPFMinPath_of_reachability
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
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
    axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 0 ∧
      axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 1 := by
  exact caseII_axisSwapped_parityBlockPFMinPath_of_raw_support
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
    hlam_case_ii hD_case_ii
    (axisSwappedParityBlockStrictRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 0 h_even_strict_reach)
    (axisSwappedParityBlockLambdaOneRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 0 h_even_lambda_one_reach)
    (axisSwappedParityBlockDZeroRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 0 h_even_D_zero_reach)
    h_even_corner
    (axisSwappedParityBlockStrictRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 1 h_odd_strict_reach)
    (axisSwappedParityBlockLambdaOneRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 1 h_odd_lambda_one_reach)
    (axisSwappedParityBlockDZeroRawSupportPath_of_reachability
      (Λ := Λ) (N := N) A J lam D 1 h_odd_D_zero_reach)
    h_odd_corner

/-- **Pathwise parity-block full-min bounds from case-(ii) reachability
inputs**.

This is the reachability-level version of
`caseII_axisSwapped_submatrix_blocks_path_of_raw_support_pf_min`: it supplies
the strict diagonal shifts on finite parity blocks before applying the
raw-support PF/min selector. -/
theorem caseII_axisSwapped_submatrix_blocks_path_of_reachability_pf_min
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
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
  rcases caseII_axisSwapped_parityBlockPFMinPath_of_reachability
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
      hlam_case_ii hD_case_ii h_even_strict_reach h_even_lambda_one_reach
      h_even_D_zero_reach h_even_corner h_odd_strict_reach h_odd_lambda_one_reach
      h_odd_D_zero_reach h_odd_corner with
    ⟨h_even_pf, h_odd_pf⟩
  exact caseII_axisSwapped_submatrix_blocks_path_of_pf_min
    (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star h_even_pf h_odd_pf

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
  exact anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_axisSwapped_submatrix_blocks_path
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
