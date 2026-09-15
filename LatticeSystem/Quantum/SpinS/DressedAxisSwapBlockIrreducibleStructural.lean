import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducible
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.ParityReachConnectedTotal

/-!
# Structural shifted parity-block irreducibility (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

(#3887.4): Structural (`h_intermediate`-free) parity-block irreducibility, using
`parityReachableS_total` (#3887.3).

Drops `h_intermediate`; requires `hA_ne + hB_ne + 1 ≤ N` instead. The result is
identical in conclusion — irreducibility of the shifted parity-block matrix —
but the hypotheses are now satisfiable at any `N ≥ 1` (where the original was
vacuous due to `h_intermediate`).

Both unconditional engines here discharge the same conditional engine
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total`
(`DressedAxisSwapBlockIrreducible.lean`), differing only in the totality layer used:
`parityReachableS_total` on `bipartiteCompleteGraphOf A` from `hA_ne + hB_ne`, and
`parityReachableS_total_of_connected` (`ParityReachConnectedTotal.lean`) on a connected `G`
from `hGconn`, each under `1 ≤ N`.

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
    A hJim hJnn (fun _ _ hadj => bipartiteCompleteGraphOf_adj_sublattice_ne hadj)
    hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total A hA_ne hB_ne hN ?_
  -- magSumS σ.1 % 2 = p = magSumS σ'.1 % 2 from parityConfigS membership.
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

/-- **Connected-graph shifted parity-block irreducibility (interior case)**.  The analogue of
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible` for an arbitrary connected graph
`G` whose edges join opposite sublattices (`hGbip`) and on whose edges the coupling is strictly
positive (`hJ_pos_G`), replacing the complete-bipartite `hA_ne`/`hB_ne` by `hGconn`.

Only the discharge of the totality hypothesis changes: `parityReachableS_total_of_connected`
(`ParityReachConnectedTotal.lean`) supplies it for `G` under `1 ≤ N` alone, since the full
parity-block relation carries the single-ion move and therefore needs no second vertex. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_connected
    (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total
    A hJim hJnn hGbip hJ_pos_G hJself hJbip hlam hlb hub hDim hDpos hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total_of_connected hGconn hN ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

end LatticeSystem.Quantum
