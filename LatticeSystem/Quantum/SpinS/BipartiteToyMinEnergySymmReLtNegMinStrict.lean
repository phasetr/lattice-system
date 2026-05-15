import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal

/-!
# Strict refined upper bound at non-degenerate configurations

PR #2883 gave the upper bound

  `(bipartiteToyMinEnergyPredictedSymm A N).re ≤ −min(|A|, |¬A|)·N`.

In the **non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`) the
inequality is **strict**:

  `(bipartiteToyMinEnergyPredictedSymm A N).re < −min(|A|, |¬A|)·N`.

This is because `(symm).re = −|A|·|¬A|·N²/2 − min·N` (PR #2843) and
`|A|·|¬A|·N² > 0` strictly under the non-degeneracy hypothesis.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict refined upper bound** (non-degenerate case):
`(bipartiteToyMinEnergyPredictedSymm A N).re < −min(|A|, |¬A|)·N`
when both sublattices are non-empty and `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_lt_neg_min_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re <
      -(min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ)) := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq]
  have hA_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have hAc_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hprod_pos :
      0 < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 := by
    positivity
  linarith

end LatticeSystem.Quantum
