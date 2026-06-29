import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffBridge

/-!
# The interaction intertwiner `blockWCoeff (Ĥ_int ψ) = Σ_x (−U_x)·D_x·W·D_x` (Tasaki §10.2.4)

Layer PR36b of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet`. Companion to the kinetic intertwiner
(PR36a): how the **attractive interaction** `Ĥ_int = attractiveHubbardInteraction`
acts in the `W`-coordinate `W := blockWCoeff ψ`.

The interaction is diagonal in configuration space, so its action on the block
coefficient is the entrywise weight multiplication of the SRP-action, transported
through the Jordan–Wigner ε-bridge (`ε² = 1`, so ε cancels — the interaction is
diagonal, no Hermiticity obstruction). Writing the entrywise weight as a
diagonal sandwich and collapsing the `·P` reindex (`E_x·P = P·D_x`) gives

  `blockWCoeff (Ĥ_int ψ) = Σ_x (−U_x)·D_x·W·D_x`,

`D_x = hubbardUpOccupationDiag x` Hermitian. This is manifestly equivariant under
`W ↦ Wᴴ` (`(D_x·W·D_x)ᴴ = D_x·Wᴴ·D_x`), the interaction half of the `Ĥ`–`Θ` commutation.

## Main results

* `blockCoeff_conj_hubbardOnSiteInteractionSite` — the ε-bridge transport of the
  diagonal action to `hubbardBlockCoeff (Uᴴ·)`.
* `reflectionCoeffAction_eq_sum_diag` — the entrywise weight action as a
  diagonal-sandwich sum `Σ_x V_x·D_x·C·E_x`.
* `blockWCoeff_attractiveHubbardInteraction_mulVec` — the interaction intertwiner.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **The diagonal interaction action on the block coefficient** (ε-bridge transport).
Since the interaction is diagonal, the Jordan–Wigner sign `ε` (with `ε² = 1`) cancels
and the SRP entrywise action transports verbatim to `hubbardBlockCoeff (Uᴴ·)`. -/
theorem blockCoeff_conj_hubbardOnSiteInteractionSite (V : Fin (N + 1) → ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N
        ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec
          ((hubbardOnSiteInteractionSite N V).mulVec ψ))
      = hubbardOnSiteInteractionSiteReflectionCoeffAction N V
          (hubbardBlockCoeff N
            ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)) := by
  -- ε-bridge in the form `spinReflectionCoeff X = ε ⊙ hubbardBlockCoeff (Uᴴ X)`.
  have key : ∀ X : (Fin (2 * N + 2) → Fin 2) → ℂ,
      spinReflectionCoeff N X
        = fun u h => translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N)
              (hubbardBlockMergeConfig N u (particleHoleConfig N h))
            * hubbardBlockCoeff N
                ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec X) u h := by
    intro X
    have h := spinReflectionCoeff_hubbardBlockToSpinfulPermutationOperator_mulVec N
      ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec X)
    rwa [Matrix.mulVec_mulVec, hubbardBlockToSpinfulPermutationOperator_mul_conjTranspose,
      Matrix.one_mulVec] at h
  funext u h
  simp only [hubbardOnSiteInteractionSiteReflectionCoeffAction]
  set ε := translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N)
    (hubbardBlockMergeConfig N u (particleHoleConfig N h)) with hε
  set bcH := hubbardBlockCoeff N
    ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec
      ((hubbardOnSiteInteractionSite N V).mulVec ψ)) u h with hbcH
  set bc := hubbardBlockCoeff N
    ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) u h with hbc
  set w := hubbardOnSiteInteractionSiteReflectionCoeffWeight N V u h with hw
  have e1 : spinReflectionCoeff N ((hubbardOnSiteInteractionSite N V).mulVec ψ) u h = ε * bcH :=
    congrFun (congrFun (key _) u) h
  have e2 : spinReflectionCoeff N ψ u h = ε * bc := congrFun (congrFun (key ψ) u) h
  have e3 : spinReflectionCoeff N ((hubbardOnSiteInteractionSite N V).mulVec ψ) u h
      = w * spinReflectionCoeff N ψ u h := by
    have h0 := congrFun (congrFun (spinReflectionCoeff_hubbardOnSiteInteractionSite N V ψ) u) h
    simpa only [hubbardOnSiteInteractionSiteReflectionCoeffAction] using h0
  have hεsq : ε * ε = 1 := translationJwSign_sq _ _
  have combined : ε * bcH = w * (ε * bc) := by rw [← e1, e3, e2]
  calc bcH = (ε * ε) * bcH := by rw [hεsq, one_mul]
    _ = ε * (ε * bcH) := by ring
    _ = ε * (w * (ε * bc)) := by rw [combined]
    _ = (ε * ε) * (w * bc) := by ring
    _ = w * bc := by rw [hεsq, one_mul]

/-- **The entrywise weight action as a diagonal sandwich sum.**
`action C = Σ_x V_x·(D_x·C·E_x)` with `D_x`/`E_x` the up/hole occupation diagonals. -/
theorem reflectionCoeffAction_eq_sum_diag (V : Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    hubbardOnSiteInteractionSiteReflectionCoeffAction N V C
      = ∑ x : Fin (N + 1), V x •
          (hubbardUpOccupationDiag N x * C * hubbardHoleOccupationDiag N x) := by
  funext u h
  simp only [hubbardOnSiteInteractionSiteReflectionCoeffAction,
    hubbardOnSiteInteractionSiteReflectionCoeffWeight, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hubbardUpOccupationDiag, hubbardHoleOccupationDiag, Matrix.mul_diagonal,
    Matrix.diagonal_mul, particleHoleConfig, flipOccupation_val_complex]
  ring

/-- The hole occupation diagonal absorbs the particle-hole permutation:
`E_x·P = P·D_x`. -/
theorem hubbardHoleOccupationDiag_mul_permMatrix (x : Fin (N + 1)) :
    hubbardHoleOccupationDiag N x * particleHoleConfigPermMatrix N
      = particleHoleConfigPermMatrix N * hubbardUpOccupationDiag N x := by
  rw [hubbardHoleOccupationDiag_eq_permConj, Matrix.mul_assoc,
    particleHoleConfigPermMatrix_mul_self, Matrix.mul_one]

/-- **The interaction intertwiner.** The reconciliation coefficient of `Ĥ_int ψ` is
`Σ_x (−U_x)·D_x·W·D_x` with `W := blockWCoeff ψ`. -/
theorem blockWCoeff_attractiveHubbardInteraction_mulVec (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N ((attractiveHubbardInteraction N U).mulVec ψ)
      = ∑ x : Fin (N + 1), (-(U x : ℂ)) •
          (hubbardUpOccupationDiag N x * blockWCoeff N ψ
            * hubbardUpOccupationDiag N x) := by
  rw [blockWCoeff, attractiveHubbardInteraction, blockCoeff_conj_hubbardOnSiteInteractionSite,
    reflectionCoeffAction_eq_sum_diag, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.smul_mul]
  congr 1
  rw [blockWCoeff]
  simp only [Matrix.mul_assoc]
  rw [hubbardHoleOccupationDiag_mul_permMatrix]

end LatticeSystem.Fermion
