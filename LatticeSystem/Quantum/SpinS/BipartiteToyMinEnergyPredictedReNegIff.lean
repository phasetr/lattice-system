import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `(pmA).re < 0 ↔ non-degenerate`

The canonical predicted-min energy `(pmA).re = −|A|·|¬A|·N²/2 − |¬A|·N`
is strictly negative exactly when the orientation pair is non-degenerate
(`0 < |A| ∧ 0 < |¬A| ∧ 0 < N` or, equivalently, `0 < |¬A| ∧ 0 < N`).

Actually `(pmA).re = −|A|·|¬A|·N²/2 − |¬A|·N`. This is strictly
negative iff `|¬A|·(|A|·N²/2 + N) > 0`, which holds iff `|¬A| > 0`
and `N > 0` (the `|A|·N²/2 + N` factor is positive iff `N > 0`).

So `(pmA).re < 0 ↔ |¬A| > 0 ∧ N > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re < 0 iff `|¬A| > 0 ∧ N > 0`**.

The canonical predicted-min energy is strictly negative exactly when
the complement sublattice is non-empty and `N` is positive. -/
theorem bipartiteToyMinEnergyPredicted_re_neg_iff_complement_nondeg
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re < 0 ↔
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧ 0 < N := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  -- Goal involves (−|A|·|¬A|·N²/2 − |¬A|·N) < 0.
  constructor
  · intro hlt
    -- Need to show |¬A| > 0 ∧ N > 0.
    by_contra h
    push Not at h
    by_cases hNotA : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card
    · -- 0 < |¬A| then N ≤ 0 → N = 0.
      have hN : N = 0 := Nat.le_zero.mp (h hNotA)
      rw [hN] at hlt
      simp at hlt
    · -- |¬A| = 0.
      have hNotA_zero : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hNotA)
      rw [hNotA_zero] at hlt
      simp at hlt
  · intro ⟨hNotApos, hNpos⟩
    have hNotA_re : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hNotApos
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hA_nn : (0 : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    nlinarith [sq_nonneg ((N : ℝ)), mul_nonneg hA_nn hNotA_re.le,
      mul_pos hNotA_re hN_re]

end LatticeSystem.Quantum
