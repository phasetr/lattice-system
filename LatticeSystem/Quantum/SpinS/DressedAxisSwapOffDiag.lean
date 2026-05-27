import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondSign
import LatticeSystem.Quantum.SpinS.DressedSingleIonSign

/-!
# Full off-diagonal non-positivity of the Marshall-dressed axis-swapped Hamiltonian (case (i))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a bipartite antiferromagnetic coupling (`J ≥ 0` real, supported on cross-sublattice bonds,
no self-bonds) and case-(i) anisotropy (`−1 ≤ λ ≤ 1`, `D ≥ 0`), **every off-diagonal entry of the
Marshall-dressed axis-swapped Hamiltonian `Ĥ'_dressed` has non-positive real part**.

This is the Perron–Frobenius input (Tasaki §2.5 Property (ii) for Theorem 2.4): `−Ĥ'_dressed` is
entrywise real with non-negative off-diagonal part, so on each parity block it is an irreducible
non-negative matrix.  It assembles the per-bond sign (#3765) and the single-ion sign (#3769) over
the bond sum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The axis-swapped bond vanishes off-diagonal when `σ'` does not agree with `σ` off `{x, y}`
(every bond term is a cross-site product). -/
theorem spinSDotXXZSwap_apply_eq_zero_of_not_agree
    {x y : Λ} (hxy : x ≠ y) (lam : ℂ) {σ' σ : Λ → Fin (N + 1)}
    (hng : ¬ (∀ k, k ≠ x → k ≠ y → σ' k = σ k)) :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  rw [spinSDotXXZSwap_def, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
    onSiteS_mul_onSiteS_apply_eq hxy, if_neg hng, if_neg hng, if_neg hng]
  simp

/-- **Full off-diagonal non-positivity of the dressed axis-swapped Hamiltonian** (case (i)). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_offdiag_re_nonpos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re ≤ 0 := by
  -- Per-bond dressed contribution is non-positive.
  have hbond : ∀ x y, (marshallSignS A σ * marshallSignS A σ' *
      (J x y * spinSDotXXZSwap x y lam N σ' σ)).re ≤ 0 := by
    intro x y
    by_cases hJ : J x y = 0
    · rw [hJ, zero_mul, mul_zero, Complex.zero_re]
    · have hAxy := hJbip x y hJ
      have hxy : x ≠ y := fun h => hJ (by rw [h]; exact hJself y)
      by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
      · have hz : (marshallSignS A σ * marshallSignS A σ' *
            spinSDotXXZSwap x y lam N σ' σ).re ≤ 0 := by
          rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
          · have hAy : A y = false := by
              rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
              · exact absurd (hAx.trans hAy.symm) hAxy
              · exact hAy
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_x A hxy hAx hAy hlam hlb hub hne
              hagree
          · have hAy : A y = true := by
              rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
              · exact hAy
              · exact absurd (hAx.trans hAy.symm) hAxy
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_y A hxy hAx hAy hlam hlb hub hne
              hagree
        rw [show marshallSignS A σ * marshallSignS A σ' *
              (J x y * spinSDotXXZSwap x y lam N σ' σ) =
            J x y * (marshallSignS A σ * marshallSignS A σ' *
              spinSDotXXZSwap x y lam N σ' σ) from by ring,
          Complex.mul_re, hJim, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hJnn x y) hz
      · rw [spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree, mul_zero, mul_zero,
          Complex.zero_re]
  -- The bond-sum off-diagonal entry, pushed through the double sum.
  have hsum : (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N) σ' σ =
      ∑ x : Λ, ∑ y : Λ, J x y * spinSDotXXZSwap x y lam N σ' σ := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hsum, mul_add, Complex.add_re]
  refine add_nonpos ?_ (dressed_singleIonAnisotropyS2_re_nonpos A hDim hDnn hne)
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_nonpos (fun x _ => ?_)
  rw [Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_nonpos (fun y _ => hbond x y)

end LatticeSystem.Quantum
