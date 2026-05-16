import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `min((predicted_min A).re, (predicted_min ¬A).re) = −|A|·|¬A|·N²/2 − max(|A|, |¬A|)·N`

Companion of PR #3001 (`max = predictedSymm = −|A|·|¬A|·N²/2 − min·N`).

The two predicted min energies have the form:
- `(predicted_min A).re = −|A|·|¬A|·N²/2 − |¬A|·N`.
- `(predicted_min ¬A).re = −|A|·|¬A|·N²/2 − |A|·N`.

Their **min** is `−|A|·|¬A|·N²/2 − max(|A|, |¬A|)·N`. This is the
"unphysical" lower predicted min energy — strictly below the
symmetric Tasaki §2.5 Theorem 2.3 prediction at unbalanced.

  `min((predicted_min A).re, (predicted_min ¬A).re)
     = −|A|·|¬A|·N²/2 − max(|A|, |¬A|)·N`
  unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Min of orientation-specific predicted min energies**:
`= −|A|·|¬A|·N²/2 − max(|A|, |¬A|)·N` unconditionally. Companion of
PR #3001 (max = predictedSymm). -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            ((N : ℝ) * (N : ℝ)) / 2) -
        max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
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
  rcases le_total cA cB with hAB | hBA
  · -- cA ≤ cB: max = cB. min(-cA·cB·cN²/2 - cB·cN, -cB·cA·cN²/2 - cA·cN) = -cA·cB·cN²/2 - cB·cN.
    rw [max_eq_right hAB, min_eq_left (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
    ring
  · -- cB ≤ cA: max = cA. min(...) = -cB·cA·cN²/2 - cA·cN.
    rw [max_eq_left hBA, min_eq_right (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
    ring

end LatticeSystem.Quantum
