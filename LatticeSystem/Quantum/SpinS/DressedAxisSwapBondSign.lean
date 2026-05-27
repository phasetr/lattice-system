import LatticeSystem.Quantum.SpinS.AxisSwapBondReNonneg
import LatticeSystem.Quantum.SpinS.AxisSwapBondVanish
import LatticeSystem.Quantum.SpinS.DressedBipartiteSign

/-!
# Marshall-dressed axis-swapped bond off-diagonal sign (case (i))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a bipartite bond `x ≠ y` (`A`-site on `x`, resp. `y`) and case-(i) anisotropy
(`−1 ≤ λ ≤ 1` real), the Marshall-dressed off-diagonal entry of `spinSDotXXZSwap x y λ` has
**non-positive real part**.  The case split on the shift at the `A`-site:

* `A`-site unchanged or shifted by `≥ 2`: the bond entry vanishes (#3764);
* `A`-site shifted by `±1`: the shift is odd, so the bipartite Marshall sign is `−1` (#3760),
  flipping the real non-negative bond entry (#3762, #3763) to non-positive.

This is the per-bond ingredient of the full dressed-`Ĥ'` off-diagonal non-positivity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Companion of `spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1` for the `y`-site: if `y` is neither
raised nor lowered by a single step the off-diagonal bond entry vanishes. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1
    {x y : Λ} (hxy : x ≠ y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hyr : (σ y).val + 1 ≠ (σ' y).val) (hyl : (σ' y).val + 1 ≠ (σ y).val) :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hP : (spinSOpPlus N) (σ' y) (σ y) = 0 := spinSOpPlus_apply_other N hyl
  have hM : (spinSOpMinus N) (σ' y) (σ y) = 0 := spinSOpMinus_apply_other N hyr
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero]
  rw [Matrix.add_apply, Matrix.add_apply,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy, hP, hM]
  simp

/-- Dressed bond off-diagonal sign on a bipartite bond with the `A`-site at `x`. -/
theorem dressedAxisSwapped_bond_re_nonpos_bipartite_x
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re ≤ 0 := by
  by_cases hr : (σ x).val + 1 = (σ' x).val
  · exact dressed_entry_re_nonpos_bipartite_x A hxy hAx hAy h ⟨(σ x).val, by omega⟩
      (spinSDotXXZSwap_apply_re_nonneg hxy hlam hlb hub hne)
  · by_cases hl : (σ' x).val + 1 = (σ x).val
    · exact dressed_entry_re_nonpos_bipartite_x A hxy hAx hAy h ⟨(σ' x).val, by omega⟩
        (spinSDotXXZSwap_apply_re_nonneg hxy hlam hlb hub hne)
    · rw [spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hxy lam hne hr hl]
      simp

/-- Dressed bond off-diagonal sign on a bipartite bond with the `A`-site at `y`. -/
theorem dressedAxisSwapped_bond_re_nonpos_bipartite_y
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 ≤ lam.re) (hub : lam.re ≤ 1)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re ≤ 0 := by
  by_cases hr : (σ y).val + 1 = (σ' y).val
  · exact dressed_entry_re_nonpos_bipartite_y A hxy hAx hAy h ⟨(σ y).val, by omega⟩
      (spinSDotXXZSwap_apply_re_nonneg hxy hlam hlb hub hne)
  · by_cases hl : (σ' y).val + 1 = (σ y).val
    · exact dressed_entry_re_nonpos_bipartite_y A hxy hAx hAy h ⟨(σ' y).val, by omega⟩
        (spinSDotXXZSwap_apply_re_nonneg hxy hlam hlb hub hne)
    · rw [spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hr hl]
      simp

end LatticeSystem.Quantum
