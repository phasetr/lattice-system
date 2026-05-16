import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement

/-!
# Unconditional `min(...) ≤ ⟨Néel⟩.re`

PR #3052: `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N ≥ 0`.

Hence unconditionally:

  `min((pmA).re, (pm¬A).re) ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Weak unconditional version of PR #3059 (strict at `|Λ| ≥ 1 ∧ N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `min(...) ≤ ⟨Néel⟩.re`**: weak version of PR #3059. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_min_complement_re
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq
    (Λ := Λ) A N
  have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    positivity
  have hcAc_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by positivity
  have hmax_nn : (0 : ℝ) ≤ max
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    le_max_of_le_left hcA_nn
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hgap_nn : (0 : ℝ) ≤ max
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) :=
    mul_nonneg hmax_nn hN_nn
  linarith

end LatticeSystem.Quantum
