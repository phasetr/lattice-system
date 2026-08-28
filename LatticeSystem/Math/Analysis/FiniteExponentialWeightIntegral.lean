import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Orthogonality of integer characters against a finite weighted sum

A source-independent Fourier identity: integrating a finite sum of vectors modulated by the
characters `φ ↦ e^{i(w j - w i)φ}` over one full period `[0, 2π]` annihilates every term whose
integer weight `w j` differs from the reference weight `w i`, and multiplies the surviving term by
`2π`.  The weights are integer-valued, which is what makes each non-matching character integrate to
zero over the period.

The statement is generic in the target space: any complete normed space that is a module over both
`ℝ` (needed to split the integral over the finite sum) and `ℂ` (needed to pull the scalar character
out of each term).  No spin, lattice, or measure-theoretic input beyond the interval integral is
used, so the lemma applies to any finite family indexed by injective integer weights.
-/

namespace LatticeSystem.Math

/-- **Character orthogonality against a finite weighted sum.**  If the integer weight `w` separates
the index `i` from every other index, then
`∫₀^{2π} Σ_j e^{i(w j - w i)φ} • v j dφ = 2π • v i`.

Each term is a constant vector scaled by a scalar character, so the integral splits over the finite
sum and reduces to the scalar integral `∫₀^{2π} e^{i(m - n)φ} dφ`, which is `2π` when `m = n` and
vanishes otherwise by periodicity of the complex exponential.  Only the term `j = i` survives, since
`w j = w i` forces `j = i`. -/
theorem integral_exp_int_weight_smul_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] (w : ι → ℤ) (v : ι → E) (i : ι)
    (hw : ∀ j, w j = w i → j = i) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j, Complex.exp (((w j : ℂ) - (w i : ℂ)) * Complex.I * (φ : ℂ)) • v j)
      = ((2 * Real.pi : ℝ) : ℂ) • v i := by
  classical
  have hcont : ∀ m n : ℤ,
      Continuous fun φ : ℝ => Complex.exp (((m : ℂ) - (n : ℂ)) * Complex.I * (φ : ℂ)) := fun _ _ =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hchar : ∀ m n : ℤ,
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (((m : ℂ) - (n : ℂ)) * Complex.I * (φ : ℂ)))
        = if m = n then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    intro m n
    have hcast : ((m : ℂ) - (n : ℂ)) = (((m - n : ℤ) : ℂ)) := by push_cast; ring
    rw [hcast]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl]
      simp only [sub_self, Int.cast_zero, zero_mul, Complex.exp_zero]
      exact (intervalIntegral.integral_const (1 : ℂ)).trans
        (by rw [sub_zero]; exact Complex.real_smul.trans (mul_one _))
    · rw [if_neg hmn]
      have hne : (m - n : ℤ) ≠ 0 := sub_ne_zero.mpr hmn
      have hc : (((m - n : ℤ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hne) Complex.I_ne_zero
      rw [integral_exp_mul_complex hc]
      have h2pi : ((m - n : ℤ) : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)
          = ((m - n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h2pi, Complex.exp_int_mul_two_pi_mul_I]
      simp
  have hterm : ∀ j : ι,
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (((w j : ℂ) - (w i : ℂ)) * Complex.I * (φ : ℂ)) • v j)
        = (if w j = w i then ((2 * Real.pi : ℝ) : ℂ) else 0) • v j := by
    intro j
    refine (intervalIntegral.integral_smul_const _ _).trans ?_
    exact congrArg (fun z : ℂ => z • v j) (hchar (w j) (w i))
  calc (∫ φ in (0 : ℝ)..(2 * Real.pi),
          ∑ j, Complex.exp (((w j : ℂ) - (w i : ℂ)) * Complex.I * (φ : ℂ)) • v j)
      = ∑ j, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (((w j : ℂ) - (w i : ℂ)) * Complex.I * (φ : ℂ)) • v j :=
        intervalIntegral.integral_finset_sum (fun j _ =>
          ((hcont (w j) (w i)).smul continuous_const).intervalIntegrable _ _)
    _ = ∑ j, (if w j = w i then ((2 * Real.pi : ℝ) : ℂ) else 0) • v j :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = ((2 * Real.pi : ℝ) : ℂ) • v i := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro j _ hji
          rw [if_neg (fun h => hji (hw j h)), zero_smul]
        · intro h
          exact absurd (Finset.mem_univ i) h

end LatticeSystem.Math
