import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Magnetization eigenvalue bounds (`|M_z| ≤ s_max`)

Scaffold for the total-spin Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `Ŝ_tot^(3)` eigenvalue on a basis state `|σ⟩` is
`magEigenvalueS σ = |Λ|·N/2 − magSumS σ`, a real number.  Since
`0 ≤ magSumS σ ≤ |Λ|·N`, this lies in `[−s_max, s_max]` with
`s_max = |Λ|·N/2 = |Λ|·S` the maximal total spin.  This is the elementary
magnetization bound underlying the highest-weight argument
`s ≤ s_max ⟹ s(s+1) ≤ s_max(s_max+1)` for the total Casimir.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

omit [DecidableEq Λ] in
/-- **Upper magnetization bound**: `M_z ≤ s_max = |Λ|·N/2`. -/
theorem magEigenvalueS_re_le_sMax (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [magEigenvalueS_re]
  have : (0 : ℝ) ≤ (magSumS σ : ℝ) := by positivity
  linarith

omit [DecidableEq Λ] in
/-- **Lower magnetization bound**: `−s_max ≤ M_z`. -/
theorem neg_sMax_le_magEigenvalueS_re (σ : Λ → Fin (N + 1)) :
    -((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ≤ (magEigenvalueS σ).re := by
  rw [magEigenvalueS_re]
  have hle : (magSumS σ : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) := by
    have := magSumS_le σ
    calc (magSumS σ : ℝ) ≤ ((Fintype.card Λ * N : ℕ) : ℝ) := by exact_mod_cast this
      _ = (Fintype.card Λ : ℝ) * (N : ℝ) := by push_cast; ring
  linarith

omit [DecidableEq Λ] in
/-- **Squared magnetization bound**: `M_z² ≤ s_max²`.  Combines the two-sided
bound `|M_z| ≤ s_max`; this is the diagonal `(Ŝ_tot^(3))²` bound feeding the
total-Casimir spectral max bound. -/
theorem magEigenvalueS_re_sq_le_sMax_sq (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re ^ 2 ≤ ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have hub := magEigenvalueS_re_le_sMax σ
  have hlb := neg_sMax_le_magEigenvalueS_re σ
  have hsmax_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  nlinarith [hub, hlb, hsmax_nn]

end LatticeSystem.Quantum
