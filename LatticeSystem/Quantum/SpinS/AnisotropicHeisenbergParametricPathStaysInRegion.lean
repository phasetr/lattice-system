import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import Mathlib.Tactic.Positivity

/-!
# The parametric path stays in the obligation (1) strict region for `t ∈ (0, 1]`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For target `(λ', D')` in the strict region (i) `(-1 < λ' < 1, D' > 0)`, the
linear parametric path `γ(t) = ((1 - t) + t λ', t D')` from `(1, 0)` to
`(λ', D')` satisfies the obligation (1) strict hypotheses for every
`t ∈ (0, 1]`:
- `-1 < γ(t).1`
- `γ(t).1 < 1`
- `0 < γ(t).2`

(At `t = 0` the path is at the SU(2) point `(1, 0)` itself, which violates the
strict obligation (1) hypotheses — this is expected since obligation (1) is the
*punctured* region.)

This is the analytic ingredient that lets PR #3970 (spin-1/2 `finrank ≤ 2`
at `hermitianMinEigenvalue Ĥ` for fixed `(λ, D)`) be applied at the parametric
crossing point `γ(t*)` in the obligation (2) chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

/-- `γ(t).1 < 1` for `t ∈ (0, 1]` and `λ' < 1`. -/
theorem anisotropicHeisenbergParametricPath_fst_lt_one
    {lam' D' : ℝ} (hlam' : lam' < 1) {t : ℝ} (ht_pos : 0 < t) (_ht_le : t ≤ 1) :
    (anisotropicHeisenbergParametricPath lam' D' t).1 < 1 := by
  unfold anisotropicHeisenbergParametricPath
  change (1 - t) + t * lam' < 1
  nlinarith

/-- `-1 < γ(t).1` for `t ∈ [0, 1]` and `-1 < λ'`. -/
theorem anisotropicHeisenbergParametricPath_neg_one_lt_fst
    {lam' D' : ℝ} (hlam' : -1 < lam') {t : ℝ} (ht_nn : 0 ≤ t) (ht_le : t ≤ 1) :
    -1 < (anisotropicHeisenbergParametricPath lam' D' t).1 := by
  unfold anisotropicHeisenbergParametricPath
  change -1 < (1 - t) + t * lam'
  -- 1 - t + t * lam' = 1 + t * (lam' - 1). For lam' > -1, t ∈ [0, 1]:
  -- t * (lam' - 1) ≥ -2 since either lam' ≥ 1 (so ≥ 0) or t * (lam' - 1) ≥ 1 * (lam' - 1) > -2.
  have h1 : 1 - t + t * lam' = 1 + t * (lam' - 1) := by ring
  rw [h1]
  rcases le_or_gt 1 lam' with h | h
  · -- lam' ≥ 1
    have : 0 ≤ t * (lam' - 1) := mul_nonneg ht_nn (by linarith)
    linarith
  · -- lam' < 1
    have : t * (lam' - 1) ≥ 1 * (lam' - 1) := by
      have hneg : lam' - 1 < 0 := by linarith
      nlinarith
    linarith

/-- `0 < γ(t).2` for `t ∈ (0, 1]` and `D' > 0`. -/
theorem anisotropicHeisenbergParametricPath_snd_pos
    {lam' D' : ℝ} (hD' : 0 < D') {t : ℝ} (ht_pos : 0 < t) :
    0 < (anisotropicHeisenbergParametricPath lam' D' t).2 := by
  unfold anisotropicHeisenbergParametricPath
  change 0 < t * D'
  positivity

/-- **Combined**: for target `(λ', D')` in strict region (i) and `t ∈ (0, 1]`,
the path satisfies the strict obligation (1) hypotheses. -/
theorem anisotropicHeisenbergParametricPath_in_strict_region
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    -1 < (anisotropicHeisenbergParametricPath lam' D' t).1 ∧
    (anisotropicHeisenbergParametricPath lam' D' t).1 < 1 ∧
    0 < (anisotropicHeisenbergParametricPath lam' D' t).2 :=
  ⟨anisotropicHeisenbergParametricPath_neg_one_lt_fst hlam'_lb (le_of_lt ht_pos) ht_le,
   anisotropicHeisenbergParametricPath_fst_lt_one hlam'_ub ht_pos ht_le,
   anisotropicHeisenbergParametricPath_snd_pos hD' ht_pos⟩

end LatticeSystem.Quantum
