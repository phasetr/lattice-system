import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Explicit difference `(predictedSymm A).re − (predicted_min A).re = (|¬A| − min(|A|, |¬A|))·N`

The signed-difference formula gives:
- `(predictedSymm A).re = −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`.
- `(predicted_min A).re = −|A|·|¬A|·N²/2 − |¬A|·N`.

Their difference is:

  `(predictedSymm A).re − (predicted_min A).re
   = (|¬A| − min(|A|, |¬A|))·N`

unconditionally.

This is the **explicit difference formula** — at proper orientation
(`|¬A| ≤ |A|`, hence `min = |¬A|`), the difference vanishes (recovering
PR #3009's equality at proper orientation). At complement orientation
(`|A| ≤ |¬A|`, hence `min = |A|`), the difference is `(|¬A| − |A|)·N ≥ 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Explicit difference formula**: `(predictedSymm A).re − (predicted_min A).re
= (|¬A| − min(|A|, |¬A|))·N` unconditionally. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_predicted_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
          (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
              (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  ring

end LatticeSystem.Quantum
