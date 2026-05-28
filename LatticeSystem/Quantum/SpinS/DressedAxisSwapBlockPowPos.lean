import LatticeSystem.Quantum.SpinS.DressedAxisSwapParityStepStrictPos
import LatticeSystem.Quantum.SpinS.ParityReachableMatrixPow
import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapBlockPow

/-!
# Block matrix power positivity from parity reachability

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For the shifted dressed `Ĥ'` real-part matrix restricted to the parity-block subtype, every
pair of parity-reachable configurations has some power of the block matrix taking a strict
positive value at that pair:

`∃ k, (parityBlockMatrix ^ k) σ' σ > 0` whenever `ParityReachableS σ.1 σ'.1`.

This combines

* the unified `ParityStepS` strict positivity of the shifted full matrix (#3795);
* the parity-block reachability matrix-power lift on the full matrix (#3787);
* the block-power-from-full identity (#3789);
* and the nonneg-everywhere bound (#3782).

The result is the per-pair pow positivity input of `Matrix.isIrreducible_iff_exists_pow_pos` —
modulo reachability totality (`∀ σ' σ, ParityReachableS σ.1 σ'.1`, the remaining combinatorial
piece (d) of PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Block matrix power positivity from parity reachability** (case (i.2) strict, `D > 0`).
For any `ParityReachableS σ.1 σ'.1` between two parity-block configurations, some power of the
parity-block submatrix takes a strict positive value at `(σ', σ)`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : ParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k) σ' σ := by
  have hB_nn : ∀ ρ τ, 0 ≤ shiftedDressedAxisSwappedReMatrix A J lam D N c ρ τ :=
    fun ρ τ => shiftedDressedAxisSwappedReMatrix_nonneg A hJim hJnn hJself hJbip hlam
      (le_of_lt hlb) (le_of_lt hub) hDim (le_of_lt hDpos) hc ρ τ
  have hB_step : ∀ {ρ τ : Λ → Fin (N + 1)},
      ParityStepS (bipartiteCompleteGraphOf A) ρ τ →
        0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ ρ :=
    fun {ρ τ} hstep =>
      shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_bipartite
        A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos c hstep
  obtain ⟨k, hpow_pos⟩ := exists_matrixPow_apply_pos_of_parityReachableS
    (G := bipartiteCompleteGraphOf A) (N := N)
    (B := shiftedDressedAxisSwappedReMatrix A J lam D N c) hB_nn hB_step hreach
  refine ⟨k, ?_⟩
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply A hJself]
  exact hpow_pos

end LatticeSystem.Quantum
