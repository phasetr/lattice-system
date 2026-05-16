import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReNegIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNonpos

/-!
# `(predictedSymm A).re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

PR #3082: `predictedSymm.re < 0 ↔ |A| ≥ 1 ∧ |¬A| ≥ 1 ∧ N ≥ 1`.
PR #2844: `predictedSymm.re ≤ 0` unconditionally.

Combining (contrapositive of #3082 + non-positivity):

  `(predictedSymm A).re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Unconditional version of PR #2864 (`predictedSymm.re = 0 ↔ saturated`
at `N ≥ 1`) extended to include the `N = 0` edge case.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **predictedSymm.re = 0 iff degeneracy** (unconditional in `N`).
Extends PR #2864 by including `N = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq_zero_iff_degenerate
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
        N = 0 := by
  have hnonpos := bipartiteToyMinEnergyPredictedSymm_re_nonpos (Λ := Λ) A N
  have hlt_iff :=
    bipartiteToyMinEnergyPredictedSymm_re_neg_iff_nondegenerate (Λ := Λ) A N
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨hA_ne, hAc_ne, hN_ne⟩ := hne
    have hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
      Nat.pos_of_ne_zero hA_ne
    have hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      Nat.pos_of_ne_zero hAc_ne
    have hN : 0 < N := Nat.pos_of_ne_zero hN_ne
    have hlt := hlt_iff.mpr ⟨hA, hAc, hN⟩
    linarith
  · intro hor
    -- Equivalent to: ¬(|A|≥1 ∧ |¬A|≥1 ∧ N≥1) → predictedSymm.re ≥ 0; combined with hnonpos, = 0.
    have hnotlt : ¬ (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re < 0 := by
      intro hlt
      obtain ⟨hA, hAc, hN⟩ := hlt_iff.mp hlt
      rcases hor with h | h | h
      · exact (Nat.pos_iff_ne_zero.mp hA) h
      · exact (Nat.pos_iff_ne_zero.mp hAc) h
      · exact (Nat.pos_iff_ne_zero.mp hN) h
    linarith

end LatticeSystem.Quantum
