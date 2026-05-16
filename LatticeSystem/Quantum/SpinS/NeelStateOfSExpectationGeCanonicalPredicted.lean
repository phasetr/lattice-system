import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalPredicted

/-!
# Unconditional `(pmA).re ≤ ⟨Néel⟩.re`

PR #3053: `⟨Néel⟩.re − (pmA).re = |¬A|·N ≥ 0`.

Hence unconditionally:

  `(predicted_min A).re ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Weak unconditional version of PR #3056 (strict at `|¬A| ≥ 1 ∧ N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `(pmA).re ≤ ⟨Néel⟩.re`**: weak version of PR #3056. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_canonical_predicted_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq
    (Λ := Λ) A N
  have hcAc_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hgap_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) :=
    mul_nonneg hcAc_nn hN_nn
  linarith

end LatticeSystem.Quantum
