import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockPowPos
import LatticeSystem.Math.PerronFrobeniusMain

/-!
# Parity-block matrix is irreducible (conditional on reachability totality)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Given **reachability totality** within a parity block (every two distinct same-parity configs are
`ParityReachableS`-connected via `bipartiteCompleteGraphOf A`-moves), the parity-block shifted PF
matrix is `Matrix.IsIrreducible` under case (i.2) strict.

This is the irreducibility step (e) of PR5 / Tasaki §2.5 Theorem 2.4, modulo the remaining
combinatorial piece (d) `hreach_total` — the canonical-representative reachability proof.

Combines:
* the conditional block matrix pow positivity (#3796, on parity-reachable pairs);
* the parity-block diagonal strict positivity (#3783);
* `Matrix.isIrreducible_iff_exists_pow_pos`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Parity-block shifted PF matrix is irreducible** under reachability totality (case (i.2)
strict). -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      ParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  have hc_le : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c := fun σ =>
    le_of_lt (hc_strict σ)
  have h_nn : ∀ σ' σ : parityConfigS Λ N p,
      0 ≤ shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ' σ :=
    fun σ' σ => shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg A hJim hJnn hJself hJbip hlam
      (le_of_lt hlb) (le_of_lt hub) hDim (le_of_lt hDpos) hc_le p σ' σ
  rw [Matrix.isIrreducible_iff_exists_pow_pos h_nn]
  intro σ' σ
  by_cases hsig : σ' = σ
  · subst hsig
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos A J lam D N p (hc_strict σ'.1)
  · -- σ' ≠ σ: use reachability + path-positivity.
    have hreach := hreach_total σ' σ hsig
    obtain ⟨k, hk⟩ :=
      shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable
        A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_le p hreach
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · subst hk0
        rw [pow_zero, Matrix.one_apply_ne hsig] at hk
        exact absurd hk (lt_irrefl 0)
      · exact hkp
    exact ⟨k, hk_pos, hk⟩

end LatticeSystem.Quantum
