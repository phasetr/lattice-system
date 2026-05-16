import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGeMin
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtMinNondegenerate
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationEqMinIffUncond

/-!
# `min(...) < ⟨Néel⟩.re ↔ |Λ| ≥ 1 ∧ N ≥ 1`

PR #3096: `min ≤ ⟨Néel⟩.re` unconditional.
PR #3059: strict at non-trivial `|Λ|, N`.
PR #3109: equality iff `|Λ| = 0 ∨ N = 0`.

Combining:

  `min((pmA).re, (pm¬A).re) < ⟨Néel⟩.re ↔ 0 < |Λ| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **min(...) < ⟨Néel⟩.re iff `|Λ| ≥ 1 ∧ N ≥ 1`** (full strict iff). -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_min_complement_re_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < Fintype.card Λ ∧ 0 < N := by
  have hge := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_min_complement_re
    (Λ := Λ) A N
  have heq_iff := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_min_complement_re_iff_uncond
    (Λ := Λ) A N
  constructor
  · intro hlt
    by_contra hne
    push Not at hne
    have hor : Fintype.card Λ = 0 ∨ N = 0 := by
      by_cases hΛ : 0 < Fintype.card Λ
      · have : N ≤ 0 := hne hΛ
        right; exact Nat.le_zero.mp this
      · left; exact Nat.le_zero.mp (Nat.not_lt.mp hΛ)
    have heq := heq_iff.mpr hor
    linarith
  · intro ⟨hΛ, hN⟩
    exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_min_complement_re
      (Λ := Λ) A N hΛ hN

end LatticeSystem.Quantum
