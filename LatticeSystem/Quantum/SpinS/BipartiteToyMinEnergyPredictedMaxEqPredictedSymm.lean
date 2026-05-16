import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# `max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`

PR #2999/#3000 gave the upper-bound inequalities:
- `(predicted_min A).re ≤ (predictedSymm A).re`
- `(predicted_min ¬A).re ≤ (predictedSymm A).re`

Equality is achieved by one of the two orientations:
- At `|¬A| ≤ |A|`: `predicted_min A = predictedSymm` (since `min = |¬A|`).
- At `|A| ≤ |¬A|`: `predicted_min ¬A = predictedSymm` (since `min = |A|`).

In either case, `max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`.

  `max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`
  unconditionally.

This identifies `bipartiteToyMinEnergyPredictedSymm` as the **max** of
the two orientation-specific predicted min energies — i.e., the
"physical" predicted GS energy (Tasaki §2.5 Theorem 2.3 prediction):
the highest of the two orientations is the lowest physical energy
upper bound.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`**
unconditionally. The symmetric form is the max over orientations. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N,
      bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  unfold bipartiteToyMinEnergyPredictedSymm
  -- Replace card {¬¬A} with card {A}.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero, zero_add]
  -- Goal: max(-|A|·|¬A|·N²/2 - |¬A|·N, -|¬A|·|A|·N²/2 - |A|·N)
  --     = -|A|·|¬A|·N²/2 - min(|A|, |¬A|)·N
  set cA : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set cB : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  set cN : ℝ := (N : ℝ)
  have hmin_eq : (((Nat.min
      (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) : ℝ)) =
      min cA cB := by
    push_cast [Nat.cast_min]; rfl
  rw [hmin_eq]
  -- max(-|A|·|¬A|·N²/2 - |¬A|·N, -|A|·|¬A|·N²/2 - |A|·N) factors as
  -- (-|A|·|¬A|·N²/2) + max(-|¬A|·N, -|A|·N).
  rcases le_total cA cB with hAB | hBA
  · -- cA ≤ cB: min = cA, max(-cB·N, -cA·N) = -cA·N.
    rw [min_eq_left hAB, max_eq_right (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
    ring
  · -- cB ≤ cA: min = cB, max(-cB·N, -cA·N) = -cB·N.
    rw [min_eq_right hBA, max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]

end LatticeSystem.Quantum
