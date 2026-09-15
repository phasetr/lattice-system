import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityDNonneg
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIonTotal
import LatticeSystem.Quantum.SpinS.ParityReachConnectedTotal
import LatticeSystem.Math.PerronFrobeniusMain

/-!
# Bond-only parity-block irreducibility at the `D >= 0` boundary

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file gives the conditional irreducibility capstone for the shifted
axis-swapped parity-block matrix using only bond-generated parity reachability.
The hypothesis is deliberately stated as a bond-only totality assumption over a
graph `G` whose edges join opposite sublattices, so that it can be discharged by
whichever totality layer fits the graph at hand — each under its own side
conditions, which the wrappers below therefore carry: `bondParityReachableS_total`
(`ParityReachableNoSingleIonTotal.lean`) on `bipartiteCompleteGraphOf A` under
`hA_ne`, `hB_ne` and `1 <= N`, used by the first wrapper below, or
`bondParityReachableS_total_of_connected` (`ParityReachConnectedTotal.lean`) on a
connected graph under `Nontrivial V` and `1 <= N`, used by the second.  The
`Nontrivial V` of the connected layer is not bookkeeping carried over from the
complete-bipartite side: both step kinds of the bond-only relation require an
edge, so on a one-vertex graph the relation has no move at all.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bond-only shifted parity-block irreducibility under reachability
totality**.  If every two distinct configurations in a parity block are
connected by bond-only parity moves along a graph `G` whose edges join opposite
sublattices, then the shifted parity-block matrix is irreducible under
`-1 < lambda < 1` and `D.re >= 0`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total
    (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      BondParityReachableS G σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  have hc_le : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c := fun σ =>
    le_of_lt (hc_strict σ)
  have h_nn : ∀ σ' σ : parityConfigS Λ N p,
      0 ≤ shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ' σ :=
    fun σ' σ => shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg A hJim hJnn hJself hJbip
      hlam (le_of_lt hlb) (le_of_lt hub) hDim hDnn hc_le p σ' σ
  rw [Matrix.isIrreducible_iff_exists_pow_pos h_nn]
  intro σ' σ
  by_cases hsig : σ' = σ
  · subst hsig
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos A J lam D N p (hc_strict σ'.1)
  · have hreach := hreach_total σ' σ hsig
    obtain ⟨k, hk⟩ :=
      shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_bondParityReachable
        A hJim hJnn hGbip hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc_le p hreach
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · subst hk0
        rw [pow_zero, Matrix.one_apply_ne hsig] at hk
        exact absurd hk (lt_irrefl 0)
      · exact hkp
    exact ⟨k, hk_pos, hk⟩

/-- **Bond-only shifted parity-block irreducibility with `D >= 0`**.  The
bond-only reachability totality theorem discharges the conditional totality
hypothesis in
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total
    A hJim hJnn (fun _ _ hadj => bipartiteCompleteGraphOf_adj_sublattice_ne hadj)
    hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict p ?_
  intro σ' σ _hne
  refine bondParityReachableS_total A hA_ne hB_ne hN ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

/-- **Connected-graph bond-only shifted parity-block irreducibility with `D >= 0`**.  The
analogue of `shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_D_nonneg` for an
arbitrary connected graph `G` whose edges join opposite sublattices (`hGbip`) and on whose
edges the coupling is strictly positive (`hJ_pos_G`), replacing `hA_ne`/`hB_ne` by `hGconn`.

Unlike the connected interior and `lambda = 1` engines
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_connected`,
`..._isIrreducible_lambda_one_D_pos_of_connected`), this one also takes
`hΛnt : Nontrivial Λ`.  It is required by the bond-only totality layer
`bondParityReachableS_total_of_connected` (`ParityReachConnectedTotal.lean`), and for the
same reason: the moves available here are the transverse and bond-parity steps, both of which
require an edge, so on a one-vertex graph the relation is empty while `G.Connected` still
holds. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_D_nonneg_of_connected
    (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hΛnt : Nontrivial Λ)
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total
    A hJim hJnn hGbip hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc_strict p ?_
  intro σ' σ _hne
  refine bondParityReachableS_total_of_connected hΛnt hGconn hN ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

end LatticeSystem.Quantum
