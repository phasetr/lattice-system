import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAddComplement
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# `max(...) + min(...) = −|A|·|¬A|·N² − |Λ|·N`

`max x y + min x y = x + y` is a standard identity for any two reals.
Combined with PR #3035-ish sum identity at the complex level:

  `(predicted_min A) + (predicted_min ¬A) = −|A|·|¬A|·N² − |Λ|·N`,

taking real parts gives:

  `max((predicted_min A).re, (predicted_min ¬A).re)
    + min((predicted_min A).re, (predicted_min ¬A).re)
   = −|A|·|¬A|·N² − |Λ|·N`

unconditionally. Companion of PR #3012 (max − min spread) and
PR #3001 (max = predictedSymm) / PR #3011 (min formula).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max + min` of orientation-specific predicted min energies**:
`= −|A|·|¬A|·N² − |Λ|·N` unconditionally. Direct from the
sum identity (PR #3035-ish) + `max + min = sum`. -/
theorem bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            ((N : ℝ) * (N : ℝ))) -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  -- `max x y + min x y = x + y` for any reals.
  have hmax_add_min : max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    max_add_min _ _
  rw [hmax_add_min]
  have hsum := bipartiteToyMinEnergyPredicted_add_complement (Λ := Λ) A N
  have hre_sum : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N) +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N)).re := by
    rw [Complex.add_re]
  rw [hre_sum, hsum]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, sub_zero, zero_add]

end LatticeSystem.Quantum
