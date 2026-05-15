import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# Néel-vs-predicted-min energy gap = 0 ↔ saturated edge at `N ≥ 1`

PR #2884 established the gap complex equality
`<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N
   = min(|A|, |¬A|) · N`.

At `N ≥ 1`, the gap real part vanishes iff `min · N = 0`, iff
`min = 0`, iff `|A| = 0 ∨ |¬A| = 0` (saturated edge).

  `(gap).re = 0 ↔ |A| = 0 ∨ |¬A| = 0`   at `N ≥ 1`.

Energy parallel of PR #2933 (`(Ŝ_tot)² gap = 0 iff saturated`):
both gaps vanish simultaneously at saturated edges, where the
Néel state exactly matches the predicted GS.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Energy gap iff characterisation**: at `N ≥ 1`,
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel> − bipartiteToyMinEnergyPredictedSymm A N).re = 0
   ↔ |A| = 0 ∨ |¬A| = 0`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm_re_eq_zero_iff_saturated
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N)) -
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm]
  -- Goal: ((min · N : ℂ)).re = 0 ↔ |A|=0 ∨ |¬A|=0
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Nat.cast_min]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro h
    -- h: min·N - 0·0 = 0, simplifies to min·N = 0.
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
    -- Note `Complex.natCast_im = 0` so the imaginary contribution vanishes.
    -- After simp, h is `min ((|A|:ℝ)) ((|¬A|:ℝ)) * N - 0 = 0`.
    have hmin_N : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) = 0 := by linarith
    have hmin_eq_zero :
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
      (mul_eq_zero.mp hmin_N).resolve_right hN_ne
    rcases le_total
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) with hab | hba
    · left
      rw [min_eq_left hab] at hmin_eq_zero
      exact_mod_cast hmin_eq_zero
    · right
      rw [min_eq_right hba] at hmin_eq_zero
      exact_mod_cast hmin_eq_zero
  · intro h
    rcases h with hA_zero | hAc_zero
    · have hA_real :
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hA_zero
      have hAc_nn : 0 ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
        Nat.cast_nonneg _
      have hmin_zero :
          min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hA_real]; exact min_eq_left hAc_nn
      rw [hmin_zero]; ring
    · have hAc_real :
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hAc_zero
      have hA_nn : 0 ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
        Nat.cast_nonneg _
      have hmin_zero :
          min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hAc_real]; exact min_eq_right hA_nn
      rw [hmin_zero]; ring

end LatticeSystem.Quantum
