import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Explicit difference (complement) `(predictedSymm A).re − (predicted_min ¬A).re = (|A| − min(|A|, |¬A|))·N`

Mirror of PR #3019. By the same algebra applied to the complement
orientation:

  `(predictedSymm A).re − (predicted_min ¬A).re
   = (|A| − min(|A|, |¬A|))·N`

unconditionally.

At complement orientation (`|A| ≤ |¬A|`, hence `min = |A|`), the
difference vanishes (recovering PR #3010). At proper orientation
(`|¬A| ≤ |A|`, hence `min = |¬A|`), the difference is `(|A| − |¬A|)·N ≥ 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Explicit difference formula (complement)**: `(predictedSymm A).re −
(predicted_min ¬A).re = (|A| − min(|A|, |¬A|))·N` unconditionally.
Mirror of PR #3019. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_complement_predicted_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
              (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  unfold bipartiteToyMinEnergyPredictedSymm
  -- Replace card {¬¬A} with card {A}.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  ring

end LatticeSystem.Quantum
