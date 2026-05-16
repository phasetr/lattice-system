import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalPredicted

/-!
# Néel expectation strictly above canonical predicted min at `|¬A| ≥ 1` ∧ `N ≥ 1`

PR #3053: `⟨Néel⟩.re − (pmA).re = |¬A|·N`. This is positive exactly
when both `|¬A| ≥ 1` and `N ≥ 1`:

  `0 < |¬A|, 0 < N → (pmA).re < ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`

unconditionally otherwise.

Physical reading: the Néel state strictly fails to attain the
canonical-orientation predicted min energy whenever the minor
sublattice is non-empty and the spin is positive.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel > pmA at `|¬A| ≥ 1` and `N ≥ 1`**. Strict version of
PR #3053's gap identity. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_canonical_predicted_re
    (A : Λ → Bool) (N : ℕ)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq
    (Λ := Λ) A N
  have hAc_re : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hAc
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) :=
    mul_pos hAc_re hN_re
  linarith

end LatticeSystem.Quantum
