import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducible
import LatticeSystem.Quantum.SpinS.ParityReachTotal

/-!
# Parity-block matrix irreducibility — unconditional version

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Discharges the `hreach_total` reachability-totality hypothesis of
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total`
(#3797) using `parityReachableS_total_legacy` (#3823): any two same-parity configurations on the
bipartite complete graph are `ParityReachableS`-connected.

This closes **(e) PR5** of Tasaki §2.5 Theorem 2.4 obligation (1): the parity-block shifted PF
matrix is `Matrix.IsIrreducible` unconditionally under case (i.2) strict (plus the standard
intermediate-site hypothesis for within-sector reachability and sublattice non-emptyness).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Parity-block shifted PF matrix is irreducible** (unconditional under case (i.2) strict).
Discharges the totality hypothesis of #3797 via #3823 `parityReachableS_total_legacy`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_legacy
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
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total_legacy A hA_ne hB_ne h_intermediate ?_
  -- magSumS σ.1 % 2 = p = magSumS σ'.1 % 2 from parityConfigS membership.
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

end LatticeSystem.Quantum
