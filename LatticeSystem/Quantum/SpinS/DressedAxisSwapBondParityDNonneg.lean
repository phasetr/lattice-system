import LatticeSystem.Quantum.SpinS.DressedAxisSwapParityBondStrictPos
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIon
import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapBlockPow

/-!
# Bond-only parity-block positivity at the `D >= 0` boundary

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file packages the shifted Perron--Frobenius matrix positivity available
without using single-ion moves.  It is intended for the general spin-`S`
`D = 0` boundary: transverse raise/lower moves and bond-parity moves remain
strictly positive when `D.re >= 0`, whereas the single-ion branch requires
`D.re > 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bond-only parity-step strict positivity with `D >= 0`**.  For a
bond-only parity move on `bipartiteCompleteGraphOf A`, the shifted dressed
matrix entry is strictly positive under the strict `-1 < lambda < 1` condition
and only the non-strict `D.re >= 0` condition. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_bondParityStepS_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)}
    (hstep : BondParityStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ := by
  rcases hstep with hRL | hPB
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb (le_of_lt hub) hDim hDnn c hRL
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn c hPB

/-- **Block matrix power positivity from bond-only parity reachability with
`D >= 0`**.  For any bond-only reachable pair of parity-block configurations,
some power of the shifted parity-block submatrix is strictly positive at that
pair. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_bondParityReachable
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : BondParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k) σ' σ := by
  have hB_nn : ∀ ρ τ, 0 ≤ shiftedDressedAxisSwappedReMatrix A J lam D N c ρ τ :=
    fun ρ τ => shiftedDressedAxisSwappedReMatrix_nonneg A hJim hJnn hJself hJbip hlam
      (le_of_lt hlb) (le_of_lt hub) hDim hDnn hc ρ τ
  have hB_step : ∀ {ρ τ : Λ → Fin (N + 1)},
      BondParityStepS (bipartiteCompleteGraphOf A) ρ τ →
        0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ ρ :=
    fun {ρ τ} hstep =>
      shiftedDressedAxisSwappedReMatrix_apply_pos_of_bondParityStepS_bipartite
        A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn c hstep
  obtain ⟨k, hpow_pos⟩ := exists_matrixPow_apply_pos_of_bondParityReachableS
    (G := bipartiteCompleteGraphOf A) (N := N)
    (B := shiftedDressedAxisSwappedReMatrix A J lam D N c) hB_nn hB_step hreach
  refine ⟨k, ?_⟩
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply A hJself]
  exact hpow_pos

end LatticeSystem.Quantum
