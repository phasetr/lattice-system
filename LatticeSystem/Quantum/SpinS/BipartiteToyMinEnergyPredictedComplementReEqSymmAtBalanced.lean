import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# At balanced: `(predicted_min ¬A).re = (predictedSymm A).re`

Mirror of PR #3003.

At balanced `|A| = |¬A|`:
- `(predicted_min ¬A).re = −|¬A|·|A|·N²/2 − |A|·N`
- `(predictedSymm A).re = −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N
                        = −|A|·|¬A|·N²/2 − |¬A|·N` (since |A| = |¬A|)
                        = `(predicted_min ¬A).re`.

Combined with PR #3003 (canonical version): at balanced, both
orientations coincide and equal the symmetric form.

  `(predicted_min ¬A).re = (predictedSymm A).re`   at `|A| = |¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **At balanced**: `(predicted_min ¬A).re = (predictedSymm A).re`.
Mirror of PR #3003. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_predictedSymm_re_of_balanced
    (A : Λ → Bool) (N : ℕ)
    (hbal : (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
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
  set cA : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set cB : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  have hbal_real : cA = cB := by
    simp only [cA, cB]
    exact_mod_cast hbal
  have hmin_eq : (((Nat.min
      (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) : ℝ)) = cA := by
    rw [show (Nat.min
        (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) =
        (Finset.univ.filter (fun x : Λ => A x = true)).card from
      Nat.min_eq_left (le_of_eq hbal)]
  rw [hmin_eq, ← hbal_real]

end LatticeSystem.Quantum
