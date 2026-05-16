import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtMaxNondeg
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationEqMaxIffUncond
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGeMax

/-!
# `max(...) < ⟨Néel⟩.re ↔ non-degenerate`

PR #3102: forward direction.
PR #3104: equality iff degenerate.

Since max ≤ ⟨Néel⟩.re always (PR #3101), max < ⟨Néel⟩.re ↔ ¬ (max = ⟨Néel⟩.re):

  `max((pmA).re, (pm¬A).re) < ⟨Néel⟩.re
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **max(...) < ⟨Néel⟩.re iff non-degenerate** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_max_complement_re_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
        0 < N := by
  have hge := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_max_complement_re
    (Λ := Λ) A N
  have heq_iff := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_max_complement_re_iff_uncond
    (Λ := Λ) A N
  constructor
  · intro hlt
    by_contra hne
    push Not at hne
    -- hne: ¬ (0 < |A| ∧ 0 < |¬A| ∧ 0 < N)
    -- We need: |A| = 0 ∨ |¬A| = 0 ∨ N = 0 (degenerate).
    have hor : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
        N = 0 := by
      by_cases hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card
      · by_cases hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card
        · -- 0 < |A| and 0 < |¬A|, so by hne, N ≤ 0.
          have hN_le : N ≤ 0 := hne hA hAc
          right; right
          exact Nat.le_zero.mp hN_le
        · -- |¬A| = 0.
          right; left
          exact Nat.le_zero.mp (Nat.not_lt.mp hAc)
      · -- |A| = 0.
        left
        exact Nat.le_zero.mp (Nat.not_lt.mp hA)
    -- At degenerate, ⟨Néel⟩.re = max.
    have heq := heq_iff.mpr hor
    linarith
  · intro ⟨hA, hAc, hN⟩
    exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_max_complement_re
      (Λ := Λ) A N hA hAc hN

end LatticeSystem.Quantum
