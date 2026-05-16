import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubComplementPredicted

/-!
# Néel expectation strictly above complement predicted min at `|A| ≥ 1` ∧ `N ≥ 1`

Mirror of PR #3056. PR #3054: `⟨Néel⟩.re − (pm¬A).re = |A|·N`. Strict
when `|A| ≥ 1` and `N ≥ 1`:

  `0 < |A|, 0 < N → (pm¬A).re < ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel > pm¬A at `|A| ≥ 1` and `N ≥ 1`**. Mirror of PR #3056. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_complement_predicted_re
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq
    (Λ := Λ) A N
  have hA_re : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by exact_mod_cast hA
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) :=
    mul_pos hA_re hN_re
  linarith

end LatticeSystem.Quantum
