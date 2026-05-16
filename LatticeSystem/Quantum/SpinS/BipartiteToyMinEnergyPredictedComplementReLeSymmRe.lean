import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# `(predicted_min (¬A)).re ≤ (predictedSymm A).re`

Mirror of PR #2999.

Both quantities have real part:
- `(predicted_min (¬A)).re = −|¬A|·|A|·N²/2 − |A|·N`.
- `(predictedSymm A).re = −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`.

The difference:
`(predictedSymm).re − (predicted_min ¬A).re = (|A| − min(|A|, |¬A|))·N ≥ 0`.

Hence

  `(predicted_min ¬A).re ≤ (predictedSymm A).re`   unconditionally.

The complement-orientation predicted min energy is bounded above by
the symmetric form. Equality at `|A| ≤ |¬A|` (where `min = |A|`);
strict at `|¬A| < |A|` and `N ≥ 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(predicted_min ¬A).re ≤ (predictedSymm A).re`** unconditionally.
Mirror of PR #2999. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_le_predictedSymm_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  -- Replace card {¬¬A} with card {A}.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  -- Goal: -|¬A|·|A|·N²/2 - |A|·N ≤ -|A|·|¬A|·N²/2 - min(|A|,|¬A|)·N.
  -- Equivalent: min(|A|,|¬A|)·N ≤ |A|·N, i.e., min ≤ |A|.
  have hmin_le : (((Nat.min
      (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) : ℝ)) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    exact_mod_cast Nat.min_le_left _ _
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  nlinarith [hmin_le, hN_nn]

end LatticeSystem.Quantum
