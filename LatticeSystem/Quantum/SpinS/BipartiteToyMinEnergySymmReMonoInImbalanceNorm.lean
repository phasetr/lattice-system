import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormOnly

/-!
# Monotonicity of `symm.re` in the imbalance norm

PR #2888 gave the univariate form
`(symm).re = ‖biw‖²/2 + ‖biw‖ − |Λ|²·N²/8 − |Λ|·N/2`.

As a function of `‖biw‖` over `[0, ∞)`, the RHS is monotonic
**increasing** (derivative `‖biw‖ + 1 > 0`). Hence for two
bipartitions `A1, A2 : Λ → Bool` on the same lattice and `N`:

  `‖biw(A1, N)‖ ≤ ‖biw(A2, N)‖
     ⟹ (symm(A1, N)).re ≤ (symm(A2, N)).re`.

Equivalently: bipartitions with larger imbalance norm give
**larger** (i.e. less-negative) predicted symm-energy.

Together with PR #2882 (global lower bound saturated at balanced)
and the saturated-edge zero (`symm = 0` at `‖biw‖ = |Λ|·N/2`),
this characterises balanced as the predicted GS energy minimiser
and saturated as the maximiser.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Monotonicity of `symm.re` in the imbalance norm**:
if `‖biw(A₁, N)‖ ≤ ‖biw(A₂, N)‖` then
`(symm(A₁, N)).re ≤ (symm(A₂, N)).re`.

Direct from PR #2888 univariate form + monotonicity of
`x ↦ x²/2 + x` on `[0, ∞)`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_mono_in_imbalance_norm
    (A₁ A₂ : Λ → Bool) (N : ℕ)
    (h : ‖bipartiteImbalanceWeight (Λ := Λ) A₁ N‖ ≤
         ‖bipartiteImbalanceWeight (Λ := Λ) A₂ N‖) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A₁ N).re ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A₂ N).re := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only,
      bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only]
  have h1_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A₁ N‖ :=
    norm_nonneg _
  have h2_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A₂ N‖ :=
    norm_nonneg _
  nlinarith [h, h1_nn, h2_nn]

end LatticeSystem.Quantum
