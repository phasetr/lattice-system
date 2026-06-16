import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducible
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural

/-!
# Structural shifted parity-block irreducibility (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

(#3887.4): Structural variant of
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_legacy` that uses
`parityReachableS_total` (#3887.3) instead of `parityReachableS_total_legacy`.

Drops `h_intermediate`; requires `hA_ne + hB_ne + 1 ≤ N` instead. The result is
identical in conclusion — irreducibility of the shifted parity-block matrix —
but the hypotheses are now satisfiable at any `N ≥ 1` (where the original was
vacuous due to `h_intermediate`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **(#3887.4) Structural shifted parity-block irreducibility (no `h_intermediate`)**. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total A hA_ne hB_ne hN ?_
  -- magSumS σ.1 % 2 = p = magSumS σ'.1 % 2 from parityConfigS membership.
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

end LatticeSystem.Quantum
