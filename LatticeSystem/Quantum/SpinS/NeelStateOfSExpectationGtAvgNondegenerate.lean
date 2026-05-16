import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# Néel expectation strictly above avg at `|Λ| ≥ 1` ∧ `N ≥ 1`

PR #3051: `⟨Néel⟩.re − avg = |Λ|·N/2`. Strict when `|Λ| ≥ 1` and `N ≥ 1`:

  `0 < |Λ|, 0 < N
    → avg < ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel > avg at `|Λ| ≥ 1` and `N ≥ 1`**. Strict version of PR #3051. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_avg_complement_re
    (A : Λ → Bool) (N : ℕ)
    (hΛ : 0 < Fintype.card Λ)
    (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have hΛ_re : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  linarith

end LatticeSystem.Quantum
