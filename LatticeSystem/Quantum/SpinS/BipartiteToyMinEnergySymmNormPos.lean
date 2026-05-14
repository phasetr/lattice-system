import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmStrictNeg

/-!
# Strict positivity of the symm-energy norm (non-degenerate case)

In the non-degenerate case (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`), the
norm of `bipartiteToyMinEnergyPredictedSymm` is strictly positive:

  `0 < ‖bipartiteToyMinEnergyPredictedSymm A N‖`.

Direct consequence of PR #2845 (`_re_neg_of_nondegenerate`):
since the real part is strictly negative, the complex number is
non-zero, so its norm is strictly positive.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict positivity of the symm-energy norm** (non-degenerate
case): `0 < ‖bipartiteToyMinEnergyPredictedSymm A N‖` when
`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_pos_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    0 < ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ := by
  rw [norm_pos_iff]
  intro hzero
  have h_re_zero : (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re = 0 := by
    rw [hzero]; simp
  have h_re_neg :=
    bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate A N hA hAc hN
  linarith

end LatticeSystem.Quantum
