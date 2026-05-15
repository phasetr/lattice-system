import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormOnly

/-!
# Strict monotonicity of `symm.re` in the imbalance norm

PR #2890 established the non-strict monotonicity:
`‖biw(A₁, N)‖ ≤ ‖biw(A₂, N)‖
   ⟹ (symm(A₁, N)).re ≤ (symm(A₂, N)).re`.

The strict version follows from the strict monotonicity of
`x ↦ x²/2 + x` on `[0, ∞)` (derivative `x + 1 > 0` strictly):

  `‖biw(A₁, N)‖ < ‖biw(A₂, N)‖
     ⟹ (symm(A₁, N)).re < (symm(A₂, N)).re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict monotonicity of `symm.re` in `‖biw‖`**:
if `‖biw(A₁, N)‖ < ‖biw(A₂, N)‖` then
`(symm(A₁, N)).re < (symm(A₂, N)).re`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_strict_mono_in_imbalance_norm
    (A₁ A₂ : Λ → Bool) (N : ℕ)
    (h : ‖bipartiteImbalanceWeight (Λ := Λ) A₁ N‖ <
         ‖bipartiteImbalanceWeight (Λ := Λ) A₂ N‖) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A₁ N).re <
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A₂ N).re := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only,
      bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only]
  have h1_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A₁ N‖ :=
    norm_nonneg _
  have h2_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A₂ N‖ :=
    norm_nonneg _
  nlinarith [h, h1_nn, h2_nn]

end LatticeSystem.Quantum
