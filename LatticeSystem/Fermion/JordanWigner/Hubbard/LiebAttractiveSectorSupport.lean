import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundStateCore

/-!
# The `blockWCoeff` sector support `|u| + |h| = Ne` (Tasaki §10.2.4)

Layer PR40a toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The
Lieb uniqueness/singlet argument lives on the fixed electron-number sector. For a state
`ψ` in the `Ne`-sector (`N̂ ψ = Ne·ψ`), the reconciliation coefficient `blockWCoeff ψ`
is supported on the **anti-diagonal band** `|u| + |h| = Ne`:

  `blockWCoeff ψ u h = (Uᴴψ)(blockMerge u h)`,  `count(blockMerge u h) = |u| + |h|`,

and `Uᴴ` (an orbital relabeling) preserves the count, so the entry vanishes off the band.
The genuine invariant square block is the balanced sector `|u| = |h| = Ne/2`
(`Even Ne`), handled in the next layer.

## Main results

* `permutationOperator_conjTranspose_mulVec_apply` — the entrywise `Uᴴ` action.
* `hubbardBlockMergeConfig_count` — `count(blockMerge u h) = |u| + |h|`.
* `blockWCoeff_apply_eq_zero_of_count_ne` — the band support.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The entrywise action of the conjugate-transposed signed permutation operator:
`(Uᴴ ψ)(τ) = ε(π, τ)·ψ(τ ∘ π⁻¹)`. -/
theorem permutationOperator_conjTranspose_mulVec_apply {M : ℕ} (π : Equiv.Perm (Fin (M + 1)))
    (ψ : (Fin (M + 1) → Fin 2) → ℂ) (τ : Fin (M + 1) → Fin 2) :
    (permutationOperator π)ᴴ.mulVec ψ τ = translationJwSign π τ * ψ (τ ∘ π.symm) := by
  change ∑ σ : Fin (M + 1) → Fin 2, (permutationOperator π)ᴴ τ σ * ψ σ
      = translationJwSign π τ * ψ (τ ∘ π.symm)
  rw [Finset.sum_eq_single (τ ∘ π.symm)]
  · rw [Matrix.conjTranspose_apply, permutationOperator, Matrix.of_apply, if_pos rfl,
      translationJwSign_star]
  · intro σ _ hσ
    rw [Matrix.conjTranspose_apply, permutationOperator, Matrix.of_apply,
      if_neg hσ, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The block index `(i, σ) ↦ hubbardBlockIndex i σ` as an equivalence. -/
noncomputable def hubbardBlockIndexEquiv (N : ℕ) :
    Fin (N + 1) × Fin 2 ≃ Fin (2 * N + 2) :=
  Equiv.ofBijective (fun p => hubbardBlockIndex N p.1 p.2) (by
    constructor
    · rintro ⟨a, σ⟩ ⟨b, τ⟩ hab
      fin_cases σ <;> fin_cases τ <;>
        simp_all [hubbardBlockIndex_zero_inj, hubbardBlockIndex_one_inj,
          hubbardBlockIndex_one_ne_zero, hubbardBlockIndex_zero_ne_one]
    · intro k
      obtain ⟨i, σ, hiσ⟩ := exists_hubbardBlockIndex N k
      exact ⟨(i, σ), hiσ.symm⟩)

/-- The block-index equivalence applies as the block index `hubbardBlockIndex i σ`. -/
@[simp]
theorem hubbardBlockIndexEquiv_apply (N : ℕ) (p : Fin (N + 1) × Fin 2) :
    hubbardBlockIndexEquiv N p = hubbardBlockIndex N p.1 p.2 := rfl

/-- The total occupation of `blockMerge u h` splits as `|u| + |h|`. -/
theorem hubbardBlockMergeConfig_count (u h : hubbardSpinConfig N) :
    (∑ j : Fin (2 * N + 2), ((hubbardBlockMergeConfig N u h j).val : ℂ))
      = (∑ x : Fin (N + 1), ((u x).val : ℂ)) + ∑ x : Fin (N + 1), ((h x).val : ℂ) := by
  rw [← Equiv.sum_comp (hubbardBlockIndexEquiv N)
    (fun o => ((hubbardBlockMergeConfig N u h o).val : ℂ)), Fintype.sum_prod_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fin.sum_univ_two]
  simp only [hubbardBlockIndexEquiv_apply, hubbardBlockMergeConfig_blockIndex_zero,
    hubbardBlockMergeConfig_blockIndex_one]

/-- **The `blockWCoeff` sector support.** For a state `ψ` in the `Ne`-electron sector,
`blockWCoeff ψ u h = 0` whenever `|u| + |h| ≠ Ne`. -/
theorem blockWCoeff_apply_eq_zero_of_count_ne (Ne : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hψ : (fermionTotalNumber (2 * N + 1)).mulVec ψ = (Ne : ℂ) • ψ)
    (u h : hubbardSpinConfig N)
    (hcount : (∑ x : Fin (N + 1), ((u x).val : ℂ))
      + ∑ x : Fin (N + 1), ((h x).val : ℂ) ≠ (Ne : ℂ)) :
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
    refine mulVec_apply_eq_zero_of_number_ne N ψ (Ne : ℂ) hψ _ ?_
    rw [show (∑ j : Fin (2 * N + 2),
          (((hubbardBlockMergeConfig N u h) ∘ (hubbardBlockToSpinfulOrbitalEquiv N).symm) j).val
            : ℂ)
        = ∑ j : Fin (2 * N + 2), ((hubbardBlockMergeConfig N u h j).val : ℂ) from
        Equiv.sum_comp (hubbardBlockToSpinfulOrbitalEquiv N).symm
          (fun j => ((hubbardBlockMergeConfig N u h j).val : ℂ)),
      hubbardBlockMergeConfig_count]
    exact hcount
  rw [hzero, mul_zero]

end LatticeSystem.Fermion
