import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHermitianGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorSupport
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround

/-!
# The Γ-reflection preserves the balanced `Ŝ³ = 0` sector (Tasaki §10.2.4)

Terminal layer PR40e-pre2b toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The
Lieb spin-reflection-positivity endgame needs the Hermitian-`W` ground representative supported on
the **balanced** per-spin sector `N̂_↑ = N̂_↓ = k` (electron number `2k`), because only there is the
reconciliation coefficient `blockWCoeff` supported on a *principal* block `S_k × S_k` (the plain
number sector gives an anti-diagonal band on which the connected-block argument fails).

This is the per-spin refinement of `LiebAttractiveThetaSector.lean`. The Γ-reflection
`Θ = gammaWState ∘ conjTranspose ∘ blockWCoeff` is species-independent, so the #4909 Θ-Hermitization
core (`gammaThetaVec`, `blockWCoeff_isHermitian_iff_gammaThetaFixed`, `gammaThetaSymm_eigenvector`,
the `x + Θx` vs `I·x + Θ(I·x)` case split) is reused verbatim. The only new input is that
conjugate transpose swaps `(u, h) ↦ (h, u)` and therefore preserves the *balanced* block
`|u| = |h| = k` (it swaps `N̂_↑ ↔ N̂_↓`), so `Θ` preserves the balanced eigenspace.

## Main results

* `mulVec_eq_smul_upNumber_of_apply_eq_zero` / `_downNumber` — converse of the per-spin support: a
  vector supported on up-count-`k` (resp. down-count-`k`) configs is an `N̂_↑` (resp. `N̂_↓`)
  eigenvector at `k`.
* `blockWCoeff_apply_eq_zero_of_updowncount_ne` — the balanced `blockWCoeff` support
  `|u| = |h| = k`.
* `gammaWState_mem_balancedSector_of_block_supported` — a balanced-block-supported `W` gives a
  balanced sector state.
* `gammaThetaVec_preserves_balanced` — `Θ` preserves the balanced `N̂_↑ = N̂_↓ = k` sector.
* `exists_hermitianW_ground_in_balanced_sector` — the balanced Hermitian-`W` ground representative,
  obtained by Θ-symmetrizing the balanced ground `exists_attractive_balanced_ground`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.9), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Converse of the up-count support.** A vector vanishing off the up-count-`k` configurations is
an `N̂_↑`-eigenvector at `k` (the spin-up number operator is diagonal with entry the up occupation
count). Per-spin analog of `mulVec_eq_smul_number_of_apply_eq_zero`. -/
theorem mulVec_eq_smul_upNumber_of_apply_eq_zero (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (h : ∀ w, (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) ≠ k → v w = 0) :
    (fermionTotalUpNumber N).mulVec v = k • v := by
  funext w
  rw [fermionTotalUpNumber_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = k
  · rw [hc]
  · rw [h w hc, mul_zero, mul_zero]

/-- **Converse of the down-count support.** A vector vanishing off the down-count-`k` configurations
is an `N̂_↓`-eigenvector at `k`. Per-spin analog of `mulVec_eq_smul_number_of_apply_eq_zero`. -/
theorem mulVec_eq_smul_downNumber_of_apply_eq_zero (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (h : ∀ w, (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) ≠ k → v w = 0) :
    (fermionTotalDownNumber N).mulVec v = k • v := by
  funext w
  rw [fermionTotalDownNumber_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) = k
  · rw [hc]
  · rw [h w hc, mul_zero, mul_zero]

/-- **The balanced `blockWCoeff` support.** For a state `ψ` with `N̂_↑ ψ = k·ψ` and `N̂_↓ ψ = k·ψ`,
`blockWCoeff ψ u h = 0` whenever `|u| ≠ k` or `|h| ≠ k`. The entry reads
`ψ` at `(blockMerge u h) ∘ π⁻¹`, whose up-count is `|u|` and down-count is `|h|` (by
`hubbardBlockToSpinfulOrbitalEquiv_symm_spinfulIndex` + the block-merge species reads), so the
per-spin vanishing lemmas apply. Per-spin refinement of `blockWCoeff_apply_eq_zero_of_count_ne`. -/
theorem blockWCoeff_apply_eq_zero_of_updowncount_ne (k : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hUp : (fermionTotalUpNumber N).mulVec ψ = (k : ℂ) • ψ)
    (hDn : (fermionTotalDownNumber N).mulVec ψ = (k : ℂ) • ψ)
    (u h : hubbardSpinConfig N)
    (hne : (∑ x : Fin (N + 1), ((u x).val : ℂ)) ≠ (k : ℂ)
        ∨ (∑ x : Fin (N + 1), ((h x).val : ℂ)) ≠ (k : ℂ)) :
    blockWCoeff N ψ u h = 0 := by
  have hbw : blockWCoeff N ψ u h
      = (hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ
          (hubbardBlockMergeConfig N u h) := by
    rw [blockWCoeff_eq_linearEquiv]
    simp only [hubbardBlockCoeffLinearEquiv, LinearEquiv.coe_mk]
    rfl
  rw [hbw, hubbardBlockToSpinfulPermutationOperator,
    permutationOperator_conjTranspose_mulVec_apply]
  have hzero : ψ ((hubbardBlockMergeConfig N u h)
      ∘ (hubbardBlockToSpinfulOrbitalEquiv N).symm) = 0 := by
    rcases hne with hu | hd
    · refine mulVec_apply_eq_zero_of_upNumber_ne ψ (k : ℂ) hUp _ ?_
      rw [show (∑ i : Fin (N + 1), (((hubbardBlockMergeConfig N u h)
            ∘ (hubbardBlockToSpinfulOrbitalEquiv N).symm) (spinfulIndex N i 0)).val : ℂ)
          = ∑ x : Fin (N + 1), ((u x).val : ℂ) from
          Finset.sum_congr rfl (fun i _ => by
            rw [Function.comp_apply, hubbardBlockToSpinfulOrbitalEquiv_symm_spinfulIndex,
              hubbardBlockMergeConfig_blockIndex_zero])]
      exact hu
    · refine mulVec_apply_eq_zero_of_downNumber_ne ψ (k : ℂ) hDn _ ?_
      rw [show (∑ i : Fin (N + 1), (((hubbardBlockMergeConfig N u h)
            ∘ (hubbardBlockToSpinfulOrbitalEquiv N).symm) (spinfulIndex N i 1)).val : ℂ)
          = ∑ x : Fin (N + 1), ((h x).val : ℂ) from
          Finset.sum_congr rfl (fun i _ => by
            rw [Function.comp_apply, hubbardBlockToSpinfulOrbitalEquiv_symm_spinfulIndex,
              hubbardBlockMergeConfig_blockIndex_one])]
      exact hd
  rw [hzero, mul_zero]

/-- **A balanced-block-supported coefficient matrix gives a balanced sector state.** If `W u h = 0`
whenever `|u| ≠ k` or `|h| ≠ k`, then `gammaWState N W` lies in the balanced `N̂_↑ = N̂_↓ = k`
sector. The species-`0` block-index read `π(hubbardBlockIndex i 0) = spinfulIndex i 0` makes the
up-count of `(gammaWState W)`'s support equal `|u|` (and species `1` gives `|h|`). Per-spin
refinement of `gammaWState_mem_numberSector_of_band_supported`. -/
theorem gammaWState_mem_balancedSector_of_block_supported (k : ℕ)
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ)
    (hW : ∀ u h : hubbardSpinConfig N, (∑ x : Fin (N + 1), ((u x).val : ℂ)) ≠ (k : ℂ)
        ∨ (∑ x : Fin (N + 1), ((h x).val : ℂ)) ≠ (k : ℂ) → W u h = 0) :
    (fermionTotalUpNumber N).mulVec (gammaWState N W) = (k : ℂ) • gammaWState N W
    ∧ (fermionTotalDownNumber N).mulVec (gammaWState N W) = (k : ℂ) • gammaWState N W := by
  constructor
  · refine mulVec_eq_smul_upNumber_of_apply_eq_zero (gammaWState N W) (k : ℂ) (fun c hc => ?_)
    rw [gammaWState, hubbardBlockToSpinfulPermutationOperator, permutationOperator_mulVec_apply]
    set π := hubbardBlockToSpinfulOrbitalEquiv N with hπ
    have hup : (∑ x : Fin (N + 1), ((hubbardBlockUpConfig N (c ∘ π) x).val : ℂ)) ≠ (k : ℂ) := by
      rw [show (∑ x : Fin (N + 1), ((hubbardBlockUpConfig N (c ∘ π) x).val : ℂ))
          = ∑ i : Fin (N + 1), ((c (spinfulIndex N i 0)).val : ℂ) from
          Finset.sum_congr rfl (fun x _ => by
            simp only [hubbardBlockUpConfig, Function.comp_apply, hπ,
              hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex])]
      exact hc
    have hWzero : ((hubbardBlockCoeffLinearEquiv N).symm W) (c ∘ π) = 0 :=
      hW (hubbardBlockUpConfig N (c ∘ π)) (hubbardBlockDownConfig N (c ∘ π)) (Or.inl hup)
    rw [hWzero, mul_zero]
  · refine mulVec_eq_smul_downNumber_of_apply_eq_zero (gammaWState N W) (k : ℂ) (fun c hc => ?_)
    rw [gammaWState, hubbardBlockToSpinfulPermutationOperator, permutationOperator_mulVec_apply]
    set π := hubbardBlockToSpinfulOrbitalEquiv N with hπ
    have hdn : (∑ x : Fin (N + 1), ((hubbardBlockDownConfig N (c ∘ π) x).val : ℂ)) ≠ (k : ℂ) := by
      rw [show (∑ x : Fin (N + 1), ((hubbardBlockDownConfig N (c ∘ π) x).val : ℂ))
          = ∑ i : Fin (N + 1), ((c (spinfulIndex N i 1)).val : ℂ) from
          Finset.sum_congr rfl (fun x _ => by
            simp only [hubbardBlockDownConfig, Function.comp_apply, hπ,
              hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex])]
      exact hc
    have hWzero : ((hubbardBlockCoeffLinearEquiv N).symm W) (c ∘ π) = 0 :=
      hW (hubbardBlockUpConfig N (c ∘ π)) (hubbardBlockDownConfig N (c ∘ π)) (Or.inr hdn)
    rw [hWzero, mul_zero]

/-- **The Γ-reflection preserves the balanced `N̂_↑ = N̂_↓ = k` sector.** If `N̂_↑ ψ = k·ψ` and
`N̂_↓ ψ = k·ψ`, then `N̂_↑ (Θψ) = k·Θψ` and `N̂_↓ (Θψ) = k·Θψ`. The coefficient of `Θψ` is
`(blockWCoeff ψ)ᴴ`, which swaps `(u, h) ↦ (h, u)` and hence stays supported on the balanced block
`|u| = |h| = k`. Per-spin refinement of `gammaThetaVec_preserves_fermionTotalNumber`. -/
theorem gammaThetaVec_preserves_balanced (k : ℕ)
    {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hUp : (fermionTotalUpNumber N).mulVec ψ = (k : ℂ) • ψ)
    (hDn : (fermionTotalDownNumber N).mulVec ψ = (k : ℂ) • ψ) :
    (fermionTotalUpNumber N).mulVec (gammaThetaVec N ψ) = (k : ℂ) • gammaThetaVec N ψ
    ∧ (fermionTotalDownNumber N).mulVec (gammaThetaVec N ψ) = (k : ℂ) • gammaThetaVec N ψ := by
  rw [gammaThetaVec]
  refine gammaWState_mem_balancedSector_of_block_supported k _ (fun u h huh => ?_)
  rw [Matrix.conjTranspose_apply,
    blockWCoeff_apply_eq_zero_of_updowncount_ne k ψ hUp hDn h u huh.symm, star_zero]

/-- **The balanced Hermitian-`W` ground representative.** For symmetric real hopping `T` and any
site attraction `U`, there is a nonzero vector `φ` in the balanced sector (`N̂_↑ φ = N̂_↓ φ = k·φ`)
whose reconciliation coefficient `blockWCoeff φ` is Hermitian and which is an eigenvector of the
attractive Hamiltonian at the *balanced sector compression's* minimum eigenvalue. It is obtained by
Θ-symmetrizing the balanced ground `exists_attractive_balanced_ground`: the symmetrization
`x + Θx` (or the `I·x + Θ(I·x)` fallback) has Hermitian `W`
(`blockWCoeff_isHermitian_iff_gammaThetaFixed`) and, by `gammaThetaVec_preserves_balanced`, stays in
the balanced sector. This is the balanced (`Ŝ³ = 0`) analog of `exists_hermitianW_ground_in_sector`;
its `blockWCoeff` is supported on the principal `S_k × S_k` block that the SRP endgame consumes. -/
theorem exists_hermitianW_ground_in_balanced_sector (k : ℕ) [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (blockWCoeff N φ).IsHermitian
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ := by
  obtain ⟨ψ₀, hψ₀, hUp, hDn, hE⟩ := exists_attractive_balanced_ground k T U hT
  set E : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardBalancedSectorPred N k) (attractiveHubbardHamiltonian_isHermitian T U hT))
  -- The `Θ`-symmetrization `x ↦ x + Θx` keeps both spin numbers.
  have hsector : ∀ x : (Fin (2 * N + 2) → Fin 2) → ℂ,
      (fermionTotalUpNumber N).mulVec x = (k : ℂ) • x →
      (fermionTotalDownNumber N).mulVec x = (k : ℂ) • x →
      (fermionTotalUpNumber N).mulVec (x + gammaThetaVec N x)
          = (k : ℂ) • (x + gammaThetaVec N x)
      ∧ (fermionTotalDownNumber N).mulVec (x + gammaThetaVec N x)
          = (k : ℂ) • (x + gammaThetaVec N x) := fun x hx hy => by
    obtain ⟨hgu, hgd⟩ := gammaThetaVec_preserves_balanced k hx hy
    exact ⟨by rw [Matrix.mulVec_add, hx, hgu, smul_add],
      by rw [Matrix.mulVec_add, hy, hgd, smul_add]⟩
  have hIE : (attractiveHubbardHamiltonian N T U).mulVec (Complex.I • ψ₀)
      = (E : ℂ) • (Complex.I • ψ₀) := by rw [Matrix.mulVec_smul, hE, smul_comm]
  have hIUp : (fermionTotalUpNumber N).mulVec (Complex.I • ψ₀)
      = (k : ℂ) • (Complex.I • ψ₀) := by rw [Matrix.mulVec_smul, hUp, smul_comm]
  have hIDn : (fermionTotalDownNumber N).mulVec (Complex.I • ψ₀)
      = (k : ℂ) • (Complex.I • ψ₀) := by rw [Matrix.mulVec_smul, hDn, smul_comm]
  by_cases h0 : ψ₀ + gammaThetaVec N ψ₀ = 0
  · obtain ⟨hu, hd⟩ := hsector _ hIUp hIDn
    refine ⟨Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀), ?_, hu, hd,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U _ E hIE⟩
    have hθ : gammaThetaVec N ψ₀ = -ψ₀ := by
      rw [eq_neg_iff_add_eq_zero, add_comm (gammaThetaVec N ψ₀) ψ₀]; exact h0
    have hθI : gammaThetaVec N (Complex.I • ψ₀) = Complex.I • ψ₀ := by
      rw [gammaThetaVec_smul, Complex.conj_I, hθ, neg_smul, smul_neg, neg_neg]
    have hval : Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀)
        = (2 : ℂ) • (Complex.I • ψ₀) := by rw [hθI, ← two_smul ℂ]
    rw [hval]
    exact smul_ne_zero (by norm_num) (smul_ne_zero Complex.I_ne_zero hψ₀)
  · obtain ⟨hu, hd⟩ := hsector _ hUp hDn
    exact ⟨ψ₀ + gammaThetaVec N ψ₀, h0, hu, hd,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U ψ₀ E hE⟩

end LatticeSystem.Fermion
