import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A sublinear real power dominates a linear one near zero

A source-independent real-analysis threshold: for positive `a, b` and an exponent `p < 1`, the
sublinear curve `ρ ↦ a·ρ^p` strictly dominates the line `ρ ↦ b·ρ` on an interval `(0, r]`, with an
explicit `r > 0` depending only on `a, b, p`.

The point of the statement is the *order of the quantifiers*: the threshold is produced before any
particular `ρ` is chosen, which is what lets a downstream argument fix a uniform density cutoff in
advance of the system it is applied to.
-/

namespace LatticeSystem.Math

/-- **A sublinear power beats a linear one below an explicit threshold.**  For `a, b > 0` and
`p < 1` there is `r > 0` with `b·ρ < a·ρ^p` for every `ρ ∈ (0, r]`.

The witness is `r = R/2` with `R = (a/b)^{1/(1−p)}`, the abscissa where the two curves cross:
`ρ < R` gives `ρ^{1−p} < a/b`, i.e. `b·ρ^{1−p} < a`, and multiplying by `ρ^p > 0` recombines
`ρ^{1−p}·ρ^p = ρ`.  Sublinearity `p < 1` is load-bearing — at `p = 1` the conclusion is false for
every `b ≥ a`. -/
theorem exists_pos_forall_mul_lt_rpow {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp1 : p < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → b * ρ < a * ρ ^ p := by
  have hq : 0 < 1 - p := by linarith
  have hab : 0 < a / b := div_pos ha hb
  set R : ℝ := (a / b) ^ (1 / (1 - p)) with hR
  have hRpos : 0 < R := Real.rpow_pos_of_pos hab _
  refine ⟨R / 2, by linarith, fun ρ hρ hρr => ?_⟩
  have hlt : ρ < R := by linarith
  have h1 : ρ ^ (1 - p) < R ^ (1 - p) := Real.rpow_lt_rpow (le_of_lt hρ) hlt hq
  have h2 : R ^ (1 - p) = a / b := by
    rw [hR, ← Real.rpow_mul (le_of_lt hab), one_div, inv_mul_cancel₀ (ne_of_gt hq),
      Real.rpow_one]
  rw [h2] at h1
  have h3 : b * ρ ^ (1 - p) < a := by
    rw [lt_div_iff₀ hb] at h1
    linarith [h1]
  have hρp : (0 : ℝ) < ρ ^ p := Real.rpow_pos_of_pos hρ p
  have h4 : b * ρ ^ (1 - p) * ρ ^ p < a * ρ ^ p := mul_lt_mul_of_pos_right h3 hρp
  have h5 : ρ ^ (1 - p) * ρ ^ p = ρ := by rw [← Real.rpow_add hρ]; simp
  calc b * ρ = b * (ρ ^ (1 - p) * ρ ^ p) := by rw [h5]
    _ = b * ρ ^ (1 - p) * ρ ^ p := by ring
    _ < a * ρ ^ p := h4

end LatticeSystem.Math
