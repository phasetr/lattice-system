import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubComplementPredicted

/-!
# Néel expectation = complement predicted min iff `|A| = 0` at `N ≥ 1`

Mirror of PR #3060. PR #3054: `⟨Néel⟩.re − (pm¬A).re = |A|·N`. At `N ≥ 1`:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re = (predicted_min ¬A).re ↔ |A| = 0`.

The Néel state attains the complement predicted min energy exactly at
complement-saturated edge (`|A| = 0`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel = pm(¬A) iff `|A| = 0` at `N ≥ 1`**. Mirror of PR #3060. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_complement_predicted_re_iff_cardA_zero
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq
    (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : ((N : ℝ)) ≠ 0 := ne_of_gt hN_re
  constructor
  · intro heq
    have hgap_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        (N : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp hgap_zero with h | h
    · exact_mod_cast h
    · exact absurd h hN_ne
  · intro hcard
    have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
      exact_mod_cast hcard
    have hgap_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        (N : ℝ) = 0 := by rw [hcard_re]; ring
    linarith

end LatticeSystem.Quantum
