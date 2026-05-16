import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Iff: `(predicted_min ¬A).re < (predictedSymm A).re ↔ |¬A| < |A|` at `N ≥ 1`

Mirror of PR #3007.

PR #3000 gave `(predicted_min ¬A).re ≤ (predictedSymm A).re` with
difference `(|A| − min(|A|, |¬A|))·N ≥ 0`. The strict inequality
holds iff `|A| > min(|A|, |¬A|)`, iff `|¬A| < |A|` AND `N ≥ 1`.

Hence

  `(predicted_min ¬A).re < (predictedSymm A).re ↔ |¬A| < |A|`
  at `N ≥ 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff strict (complement)**: `(predicted_min ¬A).re < (predictedSymm A).re ↔
|¬A| < |A|` at `N ≥ 1`. Mirror of PR #3007. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_lt_predictedSymm_re_iff_cardNotA_lt_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  unfold bipartiteToyMinEnergyPredictedSymm
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
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
  rcases lt_or_ge cB cA with hBA | hAB
  · -- cB < cA: min = cB. LHS: -cA·N < -cB·N ↔ cB < cA. Both true.
    rw [min_eq_right (le_of_lt hBA)]
    constructor
    · intro _
      have : (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) <
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)) := hBA
      exact_mod_cast this
    · intro _
      nlinarith [hBA, hN_pos]
  · -- cA ≤ cB: min = cA. LHS: -cA·N < -cA·N ↔ cB < cA. LHS false. RHS false.
    rw [min_eq_left hAB]
    constructor
    · intro hlt; linarith
    · intro h
      have hBA_real : (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) <
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)) := by
        exact_mod_cast h
      linarith

end LatticeSystem.Quantum
