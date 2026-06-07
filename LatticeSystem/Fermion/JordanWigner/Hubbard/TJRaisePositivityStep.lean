import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingCoeffSum

/-!
# Tasaki 11.5: the coefficient-sum recursion step (Prop 11.24 E3b PR5b-3b)

For a hard-core `N̂ = Ne` vector `ψ` that is an `N̂_↓`-eigenvector at `d`, the raising operator
scales its coefficient sum by `d`: `coeffSum (Ŝ⁺_tot ψ) = d · coeffSum ψ`.

Both `Ŝ⁺_tot ψ` and `N̂_↓ ψ` have the same coefficient sum `Σ_s coeff_s · #↓(s)` (the former since
each basis state raises `#↓(s)` ways with `+1` signs, the latter because `N̂_↓` is diagonal); and
`coeffSum (N̂_↓ ψ) = d · coeffSum ψ` since `ψ` is an eigenvector.  The multiplicative step driving
`coeffSum ((Ŝ⁺)^k Φ₀)` to `((Ne−1)/2)! · Σ v_q > 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **`N̂_↓` is diagonal on a filling expansion**, scaling each basis state by its down-count. -/
theorem fermionTotalDownNumber_mulVec_tJFillingExpansion (Ne : ℕ) (Φ : TJFillingSector N Ne → ℂ) :
    (fermionTotalDownNumber N).mulVec (tJFillingExpansion N Ne Φ) =
      tJFillingExpansion N Ne
        (fun s => Φ s * ((Finset.univ.filter (fun k => s.val k = 2)).card : ℂ)) := by
  unfold tJFillingExpansion
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.mulVec_smul, fermionTotalDownNumber_mulVec_tJConfigOf, smul_smul]

/-- **The coefficient-sum recursion step.**  A hard-core `N̂ = Ne` vector `ψ` with `N̂_↓ ψ = d ψ`
satisfies `coeffSum (Ŝ⁺_tot ψ) = d · coeffSum ψ`. -/
theorem coeffSum_fermionTotalSpinPlus_eq_of_downEigen (Ne : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hhc : ψ ∈ hubbardHardcoreSubspace N)
    (hNum : (fermionTotalNumber (2 * N + 1)).mulVec ψ = (Ne : ℂ) • ψ) (d : ℂ)
    (hd : (fermionTotalDownNumber N).mulVec ψ = d • ψ) :
    ∑ c, (fermionTotalSpinPlus N).mulVec ψ c = d * ∑ c, ψ c := by
  set coeff := tJFillingExpansionCoeff N Ne ψ with hcoeff
  have hexp : ψ = tJFillingExpansion N Ne coeff := tJ_filling_completeness Ne ψ hhc hNum
  -- coeffSum (Ŝ⁺ ψ) = Σ_s coeff_s · #↓(s)
  have hLHS : ∑ c, (fermionTotalSpinPlus N).mulVec ψ c =
      ∑ s, coeff s * ((Finset.univ.filter (fun x => s.val x = 2)).card : ℂ) := by
    conv_lhs => rw [hexp]
    exact coeffSum_fermionTotalSpinPlus_tJFillingExpansion N Ne coeff
  -- coeffSum (N̂_↓ ψ) = Σ_s coeff_s · #↓(s), and also = d · coeffSum ψ
  have hND : ∑ c, (fermionTotalDownNumber N).mulVec ψ c =
      ∑ s, coeff s * ((Finset.univ.filter (fun x => s.val x = 2)).card : ℂ) := by
    conv_lhs => rw [hexp, fermionTotalDownNumber_mulVec_tJFillingExpansion]
    exact coeffSum_tJFillingExpansion N Ne _
  have hND2 : ∑ c, (fermionTotalDownNumber N).mulVec ψ c = d * ∑ c, ψ c := by
    rw [hd]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [hLHS, ← hND, hND2]

end LatticeSystem.Fermion
