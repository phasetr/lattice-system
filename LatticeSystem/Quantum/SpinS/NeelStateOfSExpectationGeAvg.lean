import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# Unconditional `avg ≤ ⟨Néel⟩.re`

PR #3051: `⟨Néel⟩.re − avg = |Λ|·N/2 ≥ 0`.

Hence unconditionally:

  `((pmA).re + (pm¬A).re) / 2 ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Weak unconditional version of PR #3058 (strict inequality at
`|Λ| ≥ 1 ∧ N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `avg ≤ ⟨Néel⟩.re`**: weak version of PR #3058. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_avg_complement_re
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  have hΛ_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := by positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hgap_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  linarith

end LatticeSystem.Quantum
