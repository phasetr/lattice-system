import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# Cleaner `re` non-positivity API for `bipartiteToyMinEnergyPredictedSymm`

PR #2844 proved `(bipartiteToyMinEnergyPredictedSymm A N).re ≤ 0`.
This file provides a stronger ofReal-cast statement: the real part
is equal to the negative non-negative form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = -(|A|·|¬A|·N²/2 + min(|A|, |¬A|)·N)`.

Useful as a uniform sign-normalised form.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Negated-form of the symm-predicted min energy real part**:
`(bipartiteToyMinEnergyPredictedSymm A N).re
   = -(|A|·|¬A|·N²/2 + min(|A|, |¬A|)·N)`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq_neg_norm_form :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 +
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ)) := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq]
  ring

end LatticeSystem.Quantum
