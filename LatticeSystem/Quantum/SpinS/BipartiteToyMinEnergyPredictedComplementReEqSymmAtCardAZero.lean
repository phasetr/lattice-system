import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# At complement-saturated `|A| = 0`: `(predicted_min ¬A).re = (predictedSymm A).re = 0`

Mirror of PR #3005.

At `|A| = 0`:
- `(predicted_min ¬A).re = −|¬A|·0·N²/2 − 0·N = 0` (since `|¬¬A| = |A| = 0`).
- `(predictedSymm A).re = −0·|¬A|·N²/2 − min(0, |¬A|)·N = 0`.

Hence

  `(predicted_min ¬A).re = (predictedSymm A).re = 0`   at `|A| = 0`.

The complement-orientation predicted min energy uses `predicted_min ¬A`
at complement-saturated; both formulas vanish.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **At complement-saturated `|A| = 0`**: `(predicted_min ¬A).re =
(predictedSymm A).re`. Both vanish. Mirror of PR #3005. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_predictedSymm_re_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
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
  rw [h]
  have hmin_eq : Nat.min 0
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 :=
    Nat.min_eq_left (Nat.zero_le _)
  rw [hmin_eq]
  ring

end LatticeSystem.Quantum
