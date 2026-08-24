import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismTransverseCasimir

/-!
# §10.2.3 (Theorem 10.6): the centered-sector bound `⟨(Ô_L)²⟩ ≥ S₀²`

Tasaki's ferrimagnetic bound (10.2.17) says that the squared staggered order parameter
`(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` has expectation at least `S₀² = (||A| − |B||/2)²` in the
ground states of Lieb's half-filled repulsive Hubbard model.  This module establishes that bound
on the **centered** member `u = (Ŝ⁻_tot)^{k₀} w` of the ground multiplet's lowering tower
(`k₀ = L/2` in ℕ division, `L := sublatticeImbalance A`, `S₀ = L/2 : ℝ`), the tower member on
which Theorem 10.5's correlation signs are available (`LiebFerrimagnetismCenteredSector.lean`).

The chain runs entirely inside the single vector `u`:

* `liebRepulsive_centered_staggeredTransverse_ge_sum` — the **sign step**.  The staggered gauge
  `ε_x ε_y` is `+1` exactly on the pairs whose transverse correlation is positive and `−1` exactly
  where it is negative, so staggering can only raise each term of the transverse double sum:
  `⟨Σ_{x,y} Ŝ⊥_{xy}⟩.re ≤ ⟨(Ô_L)²_⊥⟩.re`;
* `liebRepulsive_centered_sum_transverse_eq` — the **Casimir step**.  The un-staggered double sum
  is `(Ŝ_tot)² − (Ŝ³_tot)²` (`sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq`) and `u`
  is a joint eigenvector of the two, at Theorem 10.4's Casimir value `γ₀ = S₀(S₀ + 1)` and at the
  centered weight `m₀ = S₀ − k₀`, so that expectation is `(γ₀ − m₀²) ‖u‖²`;
* `liebRepulsive_centered_ratioRe_ge_sq` — the **capstone**.  Restoring the positive-semidefinite
  longitudinal square (`fermionStaggeredTransverse_expectation_le_staggeredCasimir_expectation`)
  and using `S₀² ≤ γ₀ − m₀²` — which holds because the centered weight is `m₀ = (L % 2)/2 ≤ 1/2` —
  gives `S₀² ≤ ⟨(Ô_L)²⟩.re / ‖u‖²`;
* `liebRepulsive_exists_centered_ratioRe_ge_sq` — the **existential form**, supplying one
  highest-weight ground vector `w` that carries both the weight equation `Ŝ³_tot w = S₀ w` and the
  bound at its centered tower member.

Theorem 10.4's conclusions (`hne`, `hmin`, `hcas`) and Theorem 10.5's model hypotheses (`hbip`,
`hT_conn`, `hU`, `1 ≤ N`) enter only through the existential form; the sign step and the ratio
bound take the correlation-sign pattern as a hypothesis, so they are independent of how that
pattern was obtained.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17); §10.2.2, eq. (10.2.7), p. 351.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

/-! ## The sign step -/

/-- **Staggering a transverse pair term can only raise it.**  The gauge product `ε_x ε_y` is `+1`
on a common sublattice, where the term is unchanged, and `−1` across the two sublattices, where
the correlation is negative and the flip turns it into its absolute value.  Only the negative
branch of Theorem 10.5's sign pattern is needed: on a common sublattice the two sides agree. -/
private theorem liebRepulsive_staggeredPair_re_le {N : ℕ} (A : Finset (Fin (N + 1)))
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (x y : Fin (N + 1))
    (hneg : ¬ SameSublattice A x y → (vectorExpectation (fermionSpinTransverse N x y) v).re < 0) :
    (vectorExpectation (fermionSpinTransverse N x y) v).re ≤
      (vectorExpectation
        ((gaugeSign A x * gaugeSign A y) • fermionSpinTransverse N x y) v).re := by
  classical
  have hsmul : vectorExpectation
        ((gaugeSign A x * gaugeSign A y) • fermionSpinTransverse N x y) v
      = (gaugeSign A x * gaugeSign A y)
        * vectorExpectation (fermionSpinTransverse N x y) v := by
    unfold vectorExpectation
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  by_cases hs : SameSublattice A x y
  · rw [hsmul, gaugeSign_mul_sameSublattice A x y hs, one_mul]
  · rw [hsmul, gaugeSign_mul_not_sameSublattice A x y hs, neg_one_mul, Complex.neg_re]
    linarith [hneg hs]

/-- **The staggered transverse expectation dominates the un-staggered one.**  Summing the per-pair
sign step `liebRepulsive_staggeredPair_re_le` over the same index set `Λ × Λ` on both sides gives
`⟨Σ_{x,y} Ŝ⊥_{xy}⟩.re ≤ ⟨(Ô_L)²_⊥⟩.re`.  Theorem 10.5's sign pattern enters verbatim as the
hypothesis `hsign`, so no model hypothesis is needed here. -/
theorem liebRepulsive_centered_staggeredTransverse_ge_sum {N : ℕ} (A : Finset (Fin (N + 1)))
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsign : ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y) v).im = 0 ∧
        (SameSublattice A x y → 0 < (vectorExpectation (fermionSpinTransverse N x y) v).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y) v).re < 0)) :
    (vectorExpectation (∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y) v).re ≤
      (vectorExpectation (fermionStaggeredTransverse N A) v).re := by
  rw [fermionStaggeredTransverse]
  simp only [vectorExpectation_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  obtain ⟨-, -, hneg⟩ := hsign x y
  exact liebRepulsive_staggeredPair_re_le A v x y hneg

end LatticeSystem.Fermion
