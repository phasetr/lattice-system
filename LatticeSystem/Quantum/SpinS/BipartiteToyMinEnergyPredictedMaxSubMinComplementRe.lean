import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `max - min` of orientation-specific predicted min energies = `||A| − |¬A||·N`

Companion of PR #3001 (max = predictedSymm) and PR #3011 (min formula).

The two predicted min energies have the form:
- `(predicted_min A).re = −|A|·|¬A|·N²/2 − |¬A|·N`.
- `(predicted_min ¬A).re = −|A|·|¬A|·N²/2 − |A|·N`.

Their **difference** is `(|A| − |¬A|)·N`, so their **max − min** is
`||A| − |¬A||·N`. This measures the orientation spread of the
predicted min energy:

  `max((predicted_min A).re, (predicted_min ¬A).re)
     − min((predicted_min A).re, (predicted_min ¬A).re)
   = ||A| − |¬A||·N`

unconditionally.

Combined with PR #3001 (max = predictedSymm) and PR #3011 (min
formula), this characterizes the full spread of the orientation
ambiguity in the predicted min energy: the symmetric prediction sits
at the top, and the "wrong-orientation" prediction sits exactly
`||A| − |¬A||·N` below.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Max − min spread of orientation-specific predicted min energies**:
`= ||A| − |¬A||·N` unconditionally. Companion of PR #3001 (max =
predictedSymm) and PR #3011 (min formula). -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N,
      bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
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
  set cN : ℝ := (N : ℝ)
  have hNnn : (0 : ℝ) ≤ cN := by simp [cN]
  rcases le_total cA cB with hAB | hBA
  · -- cA ≤ cB. (predicted_min A) - (predicted_min ¬A) = (cA - cB)·cN ≤ 0,
    -- so max = (predicted_min ¬A), min = (predicted_min A).
    rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith),
        abs_of_nonpos (by linarith : cA - cB ≤ 0)]
    ring
  · -- cB ≤ cA. (predicted_min A) - (predicted_min ¬A) = (cA - cB)·cN ≥ 0,
    -- so max = (predicted_min A), min = (predicted_min ¬A).
    rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith),
        abs_of_nonneg (by linarith : 0 ≤ cA - cB)]
    ring

end LatticeSystem.Quantum
