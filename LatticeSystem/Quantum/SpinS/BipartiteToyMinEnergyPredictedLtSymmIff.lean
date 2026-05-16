import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Iff: `(predicted_min A).re < (predictedSymm A).re ↔ |A| < |¬A|` at `N ≥ 1`

PR #2999 gave `(predicted_min A).re ≤ (predictedSymm A).re` with
difference `(|¬A| − min(|A|, |¬A|))·N ≥ 0`.

The strict inequality holds iff this difference is strictly positive,
iff `|¬A| > min(|A|, |¬A|)` AND `N ≥ 1`. Since `min(|A|, |¬A|) ≤ |¬A|`
always, `|¬A| > min ↔ |A| < |¬A|` (the only way `min < |¬A|` is when
`min = |A| < |¬A|`).

Hence

  `(predicted_min A).re < (predictedSymm A).re ↔ |A| < |¬A|`   at `N ≥ 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff strict**: `(predicted_min A).re < (predictedSymm A).re ↔
|A| < |¬A|` at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_lt_predictedSymm_re_iff_cardA_lt_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  set cA : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set cB : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  have hmin_eq : (((Nat.min
      (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) : ℝ)) =
      min cA cB := by
    push_cast [Nat.cast_min]; rfl
  rw [hmin_eq]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- Goal: -|A|·|¬A|·N²/2 - |¬A|·N < -|A|·|¬A|·N²/2 - min(cA, cB)·N ↔ |A| < |¬A|.
  -- Equivalent: min(cA, cB) < cB ↔ cA < cB (since min ≤ cB always).
  rcases lt_or_ge cA cB with hAB | hBA
  · -- cA < cB: min = cA. Need: -cB·N < -cA·N ↔ cA < cB. Both true.
    rw [min_eq_left (le_of_lt hAB)]
    constructor
    · intro _
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)) <
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) := hAB
      exact_mod_cast this
    · intro _
      nlinarith [hAB, hN_pos]
  · -- cB ≤ cA: min = cB. Need: -cB·N < -cB·N ↔ cA < cB. LHS false. RHS false.
    rw [min_eq_right hBA]
    constructor
    · intro hlt; linarith
    · intro h
      have hA_real : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)) =
          cA := rfl
      have hB_real : (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) =
          cB := rfl
      have hAB_real : cA < cB := by
        rw [← hA_real, ← hB_real]; exact_mod_cast h
      linarith

end LatticeSystem.Quantum
