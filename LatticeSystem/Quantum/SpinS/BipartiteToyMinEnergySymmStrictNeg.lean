import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# Strict negativity of `bipartiteToyMinEnergyPredictedSymm`
in the non-degenerate case

PR #2844 proved
`(bipartiteToyMinEnergyPredictedSymm A N).re ≤ 0`.

In the non-degenerate case (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`), the
real part is **strictly negative**:

  `(bipartiteToyMinEnergyPredictedSymm A N).re < 0`.

Symmetric-form mirror of PR #2817 (asymmetric strict negativity).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict negativity of the predicted symmetric min energy**
(non-degenerate case): `(bipartiteToyMinEnergyPredictedSymm A N).re < 0`
when both sublattices are non-empty and `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re < 0 := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq]
  have hA_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have hAc_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmin_pos : (0 : ℝ) <
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    lt_min hA_pos hAc_pos
  nlinarith [mul_pos (mul_pos hA_pos hAc_pos) (mul_pos hN_pos hN_pos),
    mul_pos hmin_pos hN_pos]

end LatticeSystem.Quantum
