import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# Non-positivity of `bipartiteToyMinEnergyPredictedSymm` real part

The symmetric predicted toy-Hamiltonian minimum energy is the sum
of two non-positive real terms:

  `-|A|·|¬A|·N²/2`   (non-positive, product of three non-negatives)
  `-min(|A|, |¬A|)·N` (non-positive)

Hence `Re(bipartiteToyMinEnergyPredictedSymm A N) ≤ 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Non-positivity of the predicted symmetric min energy**:
`(bipartiteToyMinEnergyPredictedSymm A N).re ≤ 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_nonpos :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ≤ 0 := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq]
  have hA : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have hAc : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmin : (0 : ℝ) ≤
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    le_min hA hAc
  nlinarith [mul_nonneg (mul_nonneg hA hAc) (mul_nonneg hN hN),
    mul_nonneg hmin hN]

end LatticeSystem.Quantum
