import LatticeSystem.Quantum.SpinS.DressedAxisSwapSingleIonStrictPosCore

/-!
# Strict positivity of the shifted PF matrix on a single-ion step (case (i.2), `D.re > 0`)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a `SingleIonStepS` witness (same-site `±2`-move at some `x`) under case (i.2) (real `λ` in
`(−1, 1]`, real `D > 0` strict, `N ≥ 2` implicit since the move requires a `±2` index spread), the
shifted PF matrix entry `shiftedDressedAxisSwappedReMatrix τ σ > 0`.

The key facts:

* Every cross-site bond entry of `spinSDotXXZSwap a b` vanishes for a same-site `±2` move at `x`:
  either the configurations disagree at `x ∉ {a, b}` (#3770), or the ladder factor at `x ∈ {a, b}`
  vanishes since no single ladder operator (`Ŝ⁺`, `Ŝ⁻`, `Ŝ³`) connects `±2`-shifted Fin indices.
* The single-ion term contributes only at `y = x`; for `y ≠ x` the `δ`-product at `x` vanishes.
* `(Ŝ²)² (i, j).re < 0` strict for `|i.val − j.val| = 2`, since
  `(Ŝ²)² = −(1/4)(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)` and one of the two parity-square ladder products is strict
  positive (the other vanishes).
* Marshall sign at a same-site even shift is `+1` (no flip), so the dressed entry inherits the
  strict negative real part.
* Shifted off-diag `= −Re(dressed) > 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Full Ĥ' strict negativity + shifted strict positivity. -/

/-- **Strict negativity of the dressed `Ĥ'` off-diagonal on a `SingleIonStepS` witness**
(case (i.2): real `λ`, real `D > 0` strict). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_singleIonStepS_witness
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {x : Λ}
    {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re < 0 := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsx with h | h <;> · rw [he] at h; omega
  -- Bond sum vanishes.
  have hbonds_zero :
      (marshallSignS A σ * marshallSignS A σ' *
        (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ).re = 0 := by
    rw [Matrix.sum_apply]
    have h_inner : ∀ a, (∑ b : Λ, J a b • spinSDotXXZSwap a b lam N) σ' σ = 0 := by
      intro a
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab; rw [hJself a, zero_mul]
      · rw [spinSDotXXZSwap_apply_eq_zero_of_singleIonStep hab lam hsx hagree, mul_zero]
    rw [Finset.sum_eq_zero (fun a _ => h_inner a), mul_zero, Complex.zero_re]
  -- Single-ion sum: only the x term survives, strict negative.
  have hsingle_re :
      (marshallSignS A σ * marshallSignS A σ' * singleIonAnisotropyS2 D N σ' σ).re < 0 := by
    rw [singleIonAnisotropyS2,
      show (∑ y : Λ, onSiteS y (spinSOp2 N) * onSiteS y (spinSOp2 N) : ManyBodyOpS Λ N) =
        ∑ y : Λ, onSiteS y (spinSOp2 N * spinSOp2 N) from
        Finset.sum_congr rfl (fun y _ => onSiteS_mul_onSiteS_same y _ _),
      Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    have hsum_eq : ∑ y : Λ, (onSiteS y (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ =
        (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
      have hrest : ∑ y ∈ Finset.univ.erase x, (onSiteS y (spinSOp2 N * spinSOp2 N) :
          ManyBodyOpS Λ N) σ' σ = 0 := by
        refine Finset.sum_eq_zero (fun y hy => ?_)
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        have hsx_ne : σ' x ≠ σ x := by
          intro h
          rcases hsx with hh | hh <;> · rw [h] at hh; omega
        exact onSiteS_spinSOp2_sq_apply_eq_zero_of_singleIon_off_site hsx_ne hyx
      rw [hrest, add_zero]
    rw [hsum_eq]
    rw [show marshallSignS A σ * marshallSignS A σ' * (D *
          (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ) =
        D * (marshallSignS A σ * marshallSignS A σ' *
          (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ) from by ring,
      Complex.mul_re, hDim, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg hDpos
      (dressed_onSiteS_spinSOp2_sq_re_neg_of_singleIon_witness A hsx hagree)
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, mul_add, Complex.add_re]
  linarith [hbonds_zero, hsingle_re]

/-- **Shifted PF strict positive on a `SingleIonStepS` witness** (case (i.2), `D.re > 0`). -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS_witness
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {x : Λ}
    {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsx with h | h <;> · rw [he] at h; omega
  unfold shiftedDressedAxisSwappedReMatrix
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, zero_sub]
  have hneg :=
    dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_singleIonStepS_witness
      (lam := lam) A hJself hDim hDpos hsx hagree
  change 0 < -((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N) σ' σ).re
  linarith

/-- **Shifted PF strict positive on a `SingleIonStepS`** (case (i.2), `D.re > 0`). -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : SingleIonStepS σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ := by
  obtain ⟨x, hsx, hagree⟩ := hstep
  exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS_witness
    A hJself hDim hDpos c hsx hagree

end LatticeSystem.Quantum
