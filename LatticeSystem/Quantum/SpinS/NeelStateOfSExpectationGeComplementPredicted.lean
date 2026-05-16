import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubComplementPredicted

/-!
# Unconditional `(pm¬A).re ≤ ⟨Néel⟩.re`

PR #3054: `⟨Néel⟩.re − (pm¬A).re = |A|·N ≥ 0`.

Hence unconditionally:

  `(predicted_min ¬A).re ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Mirror of PR #3097. Weak unconditional version of PR #3057.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `(pm¬A).re ≤ ⟨Néel⟩.re`**: mirror of PR #3097. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_complement_predicted_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq
    (Λ := Λ) A N
  have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hgap_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) :=
    mul_nonneg hcA_nn hN_nn
  linarith

end LatticeSystem.Quantum
