import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap

/-!
# Iff: `0 < ⟨Néel⟩ − predictedSymm ↔ non-degenerate`

PR existing (`NeelStateOfSPredictedSymmGapPosNondegenerate.lean`) gives the
forward direction: if non-degenerate then the gap is positive. This PR
adds the iff form via the explicit gap formula:

  `(⟨Néel⟩ − predictedSymm).re = min(|A|, |¬A|) · N`

which is `> 0` iff `min(|A|, |¬A|) > 0 ∧ N > 0` iff non-degenerate
(`0 < |A| ∧ 0 < |¬A| ∧ 0 < N`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **0 < ⟨Néel⟩ − predictedSymm iff non-degenerate**. iff form of the
existing one-directional theorem. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_pos_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N)) -
          bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  -- Use the explicit gap formula.
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) A N
  -- Take .re and convert ℂ min to ℝ min.
  have hgap_re : (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N)) -
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) := by
    rw [hgap]
    simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Nat.cast_min]
  rw [hgap_re]
  constructor
  · intro hpos
    -- min·N > 0 → both factors positive.
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hmin_nn : (0 : ℝ) ≤ (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
    · -- N > 0 and min·N > 0 → min > 0.
      have hmin_pos : (0 : ℝ) < (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        by_contra h
        push Not at h
        have : (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
          le_antisymm h hmin_nn
        rw [this] at hpos
        simp at hpos
      have hmin_nat : 0 < Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
        exact_mod_cast hmin_pos
      refine ⟨?_, ?_, ?_⟩
      · exact Nat.lt_of_lt_of_le hmin_nat (Nat.min_le_left _ _)
      · exact Nat.lt_of_lt_of_le hmin_nat (Nat.min_le_right _ _)
      · exact_mod_cast hN_pos
    · -- N = 0 → min·N = 0, contradicts hpos.
      have : (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
        rw [← hN_zero]; ring
      linarith
  · intro ⟨hA, hAc, hN⟩
    have hmin : 0 < Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
      exact Nat.lt_min.mpr ⟨hA, hAc⟩
    have hmin_re : (0 : ℝ) < (Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hmin
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact mul_pos hmin_re hN_re

end LatticeSystem.Quantum
