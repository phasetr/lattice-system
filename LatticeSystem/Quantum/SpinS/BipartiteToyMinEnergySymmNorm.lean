import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNonpos

/-!
# Norm of `bipartiteToyMinEnergyPredictedSymm`

Combining PR #2843 (`_re_eq` real-axis form + `_im_zero`) with
PR #2844 (`_re_nonpos`), the complex absolute value of
`bipartiteToyMinEnergyPredictedSymm A N` is the absolute value of
its (non-positive) real part:

  `‖bipartiteToyMinEnergyPredictedSymm A N‖
     = |A|·|¬A|·N²/2 + min(|A|, |¬A|)·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Norm of `bipartiteToyMinEnergyPredictedSymm`**: equals the
positive sum `|A|·|¬A|·N²/2 + min(|A|, |¬A|)·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 +
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) := by
  -- The energy is real and non-positive: norm = |re| = -re.
  have him := bipartiteToyMinEnergyPredictedSymm_im_zero (Λ := Λ) A N
  have hre_nonpos := bipartiteToyMinEnergyPredictedSymm_re_nonpos (Λ := Λ) A N
  -- Use Complex.norm_def: ‖z‖ = √((z.re)² + (z.im)²).
  have h_eq_neg_re :
      ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ =
        -(bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
    have hRewriteToReal :
        bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N =
          (((bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hRewriteToReal, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_re, abs_of_nonpos hre_nonpos]
  rw [h_eq_neg_re, bipartiteToyMinEnergyPredictedSymm_re_eq]
  ring

end LatticeSystem.Quantum
