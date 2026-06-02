import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityLambdaOne
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBondTotal
import LatticeSystem.Math.PerronFrobeniusMain

/-!
# Ion-only parity-block irreducibility at `lambda = 1`, `D > 0`

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file gives the shifted axis-swapped parity-block irreducibility result for
the `lambda = 1`, `D > 0` boundary.  The proof uses only transverse
raise/lower moves and single-ion moves, avoiding the parity-bond branch whose
coefficient vanishes at `lambda = 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Ion-only shifted parity-block irreducibility under reachability totality**.
If every two distinct configurations in a parity block are connected by
ion-only parity moves, then the shifted parity-block matrix is irreducible at
`lambda = 1`, `D > 0`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_ionParityReachable_total_lambda_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      IonParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p).IsIrreducible := by
  have hc_le : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ ≤ c := fun σ =>
    le_of_lt (hc_strict σ)
  have h_nn : ∀ σ' σ : parityConfigS Λ N p,
      0 ≤ shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p σ' σ :=
    fun σ' σ => shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg A hJim hJnn hJself hJbip
      (by norm_num) (by norm_num) (by norm_num) hDim (le_of_lt hDpos) hc_le p σ' σ
  rw [Matrix.isIrreducible_iff_exists_pow_pos h_nn]
  intro σ' σ
  by_cases hsig : σ' = σ
  · subst hsig
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos A J 1 D N p (hc_strict σ'.1)
  · have hreach := hreach_total σ' σ hsig
    obtain ⟨k, hk⟩ :=
      shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_ionParityReachable_lambda_one
        A hJim hJnn hJpos hJself hJbip hDim hDpos hc_le p hreach
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · subst hk0
        rw [pow_zero, Matrix.one_apply_ne hsig] at hk
        exact absurd hk (lt_irrefl 0)
      · exact hkp
    exact ⟨k, hk_pos, hk⟩

set_option linter.style.longLine false in
/-- **Ion-only shifted parity-block irreducibility at `lambda = 1`, `D > 0`**.
The ion-only reachability totality theorem discharges the conditional totality
hypothesis on the bipartite complete graph. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_lambda_one_D_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_ionParityReachable_total_lambda_one
    A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict p ?_
  intro σ' σ _hne
  refine ionParityReachableS_total A hA_ne hB_ne hN ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

end LatticeSystem.Quantum
