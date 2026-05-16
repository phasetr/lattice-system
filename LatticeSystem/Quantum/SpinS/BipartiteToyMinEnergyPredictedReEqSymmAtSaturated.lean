import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# At canonical-saturated `|¬A| = 0`: `(predicted_min A).re = (predictedSymm A).re`

Both predicted min energy formulas vanish at canonical-saturated:
- `(predicted_min A).re = −|A|·0·N²/2 − 0·N = 0`.
- `(predictedSymm A).re = −|A|·0·N²/2 − min(|A|, 0)·N = 0`.

Hence

  `(predicted_min A).re = (predictedSymm A).re = 0`
  at `|¬A| = 0`.

The fully-polarised ferromagnetic ground state (saturated edge) has
predicted energy `0` in both formulations.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **At canonical-saturated `|¬A| = 0`**: `(predicted_min A).re =
(predictedSymm A).re`. Both vanish. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_predictedSymm_re_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  -- At |¬A| = 0: min(|A|, 0) = 0 = |¬A|.
  rw [h]
  -- Need to simplify min(|A|, 0) = 0.
  have hmin_eq : Nat.min
      (Finset.univ.filter (fun x : Λ => A x = true)).card 0 = 0 :=
    Nat.min_eq_right (Nat.zero_le _)
  rw [hmin_eq]

end LatticeSystem.Quantum
