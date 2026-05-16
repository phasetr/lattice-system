import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmStrictNeg
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNonpos
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# `(predictedSymm A).re < 0 ↔ |A| ≥ 1 ∧ |¬A| ≥ 1 ∧ N ≥ 1`

PR #2845: forward direction (`non-degenerate → predictedSymm.re < 0`).
PR #2844 + explicit formula: at saturated or `N = 0`, `predictedSymm.re = 0`.

  `(predictedSymm A).re < 0
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **predictedSymm.re < 0 iff non-degenerate**: full iff form of PR #2845. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_neg_iff_nondegenerate
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re < 0 ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
        0 < N := by
  constructor
  · intro hlt
    -- Use explicit formula `predictedSymm.re = −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`.
    rw [bipartiteToyMinEnergyPredictedSymm_re_eq] at hlt
    -- Goal: hlt: -|A||¬A|N²/2 - min·N < 0, derive 0 < |A|, |¬A|, N.
    have hcA_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      positivity
    have hcAc_nn : (0 : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by positivity
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hmin_nn : (0 : ℝ) ≤ min
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
      le_min hcA_nn hcAc_nn
    -- hlt is already in ℝ-min form via bipartiteToyMinEnergyPredictedSymm_re_eq.
    -- Now: -|A||¬A|N²/2 - min·N < 0. So either |A||¬A|N² > 0 or min·N > 0 (at least one).
    -- We need ALL three positive: |A|, |¬A|, N.
    have hq_nn : (0 : ℝ) ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by positivity
    have hmin_lin_nn : (0 : ℝ) ≤ min
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) :=
      mul_nonneg hmin_nn hNnn
    -- hlt: -X - Y < 0 where X ≥ 0, Y ≥ 0. So X + Y > 0.
    have hsum_pos : 0 < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) / 2 +
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) := by
      linarith
    -- Since |A|·|¬A|·N²/2 + min·N > 0 with both summands ≥ 0, we need to conclude:
    -- if |A| = 0 ∨ |¬A| = 0 ∨ N = 0 then both summands = 0, contradicting hsum_pos.
    refine ⟨?_, ?_, ?_⟩
    · by_contra hA_zero
      push Not at hA_zero
      have hcA_z : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 :=
        Nat.le_zero.mp hA_zero
      have hcA_re_z : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hcA_z
      have hmin_z : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hcA_re_z]
        exact min_eq_left hcAc_nn
      rw [hmin_z, hcA_re_z] at hsum_pos
      linarith
    · by_contra hAc_zero
      push Not at hAc_zero
      have hcAc_z : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 :=
        Nat.le_zero.mp hAc_zero
      have hcAc_re_z : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hcAc_z
      have hmin_z : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hcAc_re_z]
        exact min_eq_right hcA_nn
      rw [hmin_z, hcAc_re_z] at hsum_pos
      linarith
    · by_contra hN_zero
      push Not at hN_zero
      have hN_z : N = 0 := Nat.le_zero.mp hN_zero
      have hN_re_z : (N : ℝ) = 0 := by exact_mod_cast hN_z
      rw [hN_re_z] at hsum_pos
      simp at hsum_pos
  · intro ⟨hA, hAc, hN⟩
    exact bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate
      (Λ := Λ) (A := A) (N := N) hA hAc hN

end LatticeSystem.Quantum
