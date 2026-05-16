import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxAddMinComplementRe

/-!
# `(pmA).re + (pm¬A).re < 0` at `|Λ| ≥ 1, N ≥ 1`

PR #3031: `max + min = (pmA).re + (pm¬A).re = -|A|·|¬A|·N² - |Λ|·N`.

This is strictly negative whenever `|Λ| ≥ 1` and `N ≥ 1`, since the
`-|Λ|·N` term is strictly negative (the `-|A|·|¬A|·N²` term is
non-positive). Even at saturated edges (one sublattice empty), the
`|Λ|·N` term is positive when `|Λ| ≥ 1, N ≥ 1`.

  `0 < |Λ|, 0 < N → (predicted_min A).re + (predicted_min ¬A).re < 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Sum strictly negative at `|Λ| ≥ 1, N ≥ 1`**: a `predictedSymm`-
independent fact ensured by the `-|Λ|·N` term. -/
theorem bipartiteToyMinEnergyPredicted_sum_complement_re_neg_of_card_pos
    (A : Λ → Bool) (N : ℕ)
    (hΛ : 0 < Fintype.card Λ)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 := by
  have hsum_max_min := bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq
    (Λ := Λ) A N
  have hmax_add_min_eq_sum : max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    max_add_min _ _
  -- Goal: pmA + pm¬A = -|A||¬A|N² - |Λ|N (from hsum_max_min + hmax_add_min_eq_sum).
  have hsum_eq : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            ((N : ℝ) * (N : ℝ))) -
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
    linarith [hsum_max_min, hmax_add_min_eq_sum]
  rw [hsum_eq]
  have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    positivity
  have hcB_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    positivity
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hΛ_re : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      ((N : ℝ) * (N : ℝ)) := by positivity
  have hlin_pos : (0 : ℝ) < (Fintype.card Λ : ℝ) * (N : ℝ) := mul_pos hΛ_re hN_re
  linarith

end LatticeSystem.Quantum
