import LatticeSystem.Quantum.SpinS.DressedAxisSwapSingleIonStrictPos
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBond
import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapBlockPow

/-!
# Ion-only parity-block positivity at `lambda = 1`, `D > 0`

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file packages the shifted Perron--Frobenius matrix positivity available at
the `lambda = 1`, `D > 0` boundary.  At this boundary the same-direction
parity-bond coefficient vanishes, so the positivity route deliberately uses
only transverse raise/lower moves and single-ion moves.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Ion-only parity-step strict positivity at `lambda = 1`, `D > 0`**.  For
an ion-only parity move on `bipartiteCompleteGraphOf A`, the shifted dressed
matrix entry is strictly positive. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_ionParityStepS_lambda_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)}
    (hstep : IonParityStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J 1 D N c τ σ := by
  rcases hstep with hRL | hSI
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
      A hJim hJnn hJpos hJself hJbip (by norm_num) (by norm_num) (by norm_num)
      hDim (le_of_lt hDpos) c hRL
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS
      A hJself hDim hDpos c hSI

/-- **Block matrix power positivity from ion-only parity reachability at
`lambda = 1`, `D > 0`**.  For any ion-only reachable pair of parity-block
configurations, some power of the shifted parity-block submatrix is strictly
positive at that pair. -/
theorem shiftedDressedReMatParity_pow_apply_pos_of_ionParityReach_lam1
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : IonParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p ^ k) σ' σ := by
  have hB_nn : ∀ ρ τ, 0 ≤ shiftedDressedAxisSwappedReMatrix A J 1 D N c ρ τ :=
    fun ρ τ => shiftedDressedAxisSwappedReMatrix_nonneg A hJim hJnn hJself hJbip
      (by norm_num) (by norm_num) (by norm_num) hDim (le_of_lt hDpos) hc ρ τ
  have hB_step : ∀ {ρ τ : Λ → Fin (N + 1)},
      IonParityStepS (bipartiteCompleteGraphOf A) ρ τ →
        0 < shiftedDressedAxisSwappedReMatrix A J 1 D N c τ ρ :=
    fun {ρ τ} hstep =>
      shiftedDressedAxisSwappedReMatrix_apply_pos_of_ionParityStepS_lambda_one
        A hJim hJnn hJpos hJself hJbip hDim hDpos c hstep
  obtain ⟨k, hpow_pos⟩ := exists_matrixPow_apply_pos_of_ionParityReachableS
    (G := bipartiteCompleteGraphOf A) (N := N)
    (B := shiftedDressedAxisSwappedReMatrix A J 1 D N c) hB_nn hB_step hreach
  refine ⟨k, ?_⟩
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply A hJself]
  exact hpow_pos

end LatticeSystem.Quantum
