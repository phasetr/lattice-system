import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Operators

/-!
# Config-basis entries of the axis-swapped ladder bond terms are real and sign-definite

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The cross-site products `onSiteS x Ŝ^a * onSiteS y Ŝ^b` (`a, b ∈ {+, −}`, `x ≠ y`) appearing in
the ladder form (2.5.16) of `Ĥ'` have **real, non-negative** matrix entries in the configuration
basis: each is a product of two single-site raising/lowering entries, which are real and
non-negative.  This is the bare-sign input to the Marshall-dressed off-diagonal sign analysis
(in the dressed basis these positive entries are flipped to `≤ 0`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- A cross-site product `onSiteS x A * onSiteS y B` of operators with real entries has real
entries in the configuration basis. -/
theorem onSiteS_mul_onSiteS_apply_im_zero_of_real
    {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : ∀ i j, (A i j).im = 0) (hB : ∀ i j, (B i j).im = 0)
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x A * onSiteS y B) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  split_ifs
  · rw [Complex.mul_im, hA, hB]; ring
  · exact Complex.zero_im

/-- A cross-site product of operators with real, non-negative entries has non-negative real part. -/
theorem onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg
    {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : ∀ i j, (A i j).im = 0) (hAnn : ∀ i j, 0 ≤ (A i j).re)
    (hB : ∀ i j, (B i j).im = 0) (hBnn : ∀ i j, 0 ≤ (B i j).re)
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x A * onSiteS y B) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  split_ifs
  · rw [Complex.mul_re, hA, hB]
    simp only [mul_zero, sub_zero]
    exact mul_nonneg (hAnn _ _) (hBnn _ _)
  · exact le_of_eq Complex.zero_re.symm

/-- The two-site parity raising term `Ŝ⁺_x Ŝ⁺_y` has real, non-negative config-basis entries. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N)) σ' σ).im = 0 ∧
      0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N)) σ' σ).re :=
  ⟨onSiteS_mul_onSiteS_apply_im_zero_of_real (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_im_zero N) hxy σ' σ,
    onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_re_nonneg N) (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_re_nonneg N) hxy σ' σ⟩

/-- The two-site parity lowering term `Ŝ⁻_x Ŝ⁻_y` has real, non-negative config-basis entries. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)) σ' σ).im = 0 ∧
      0 ≤ ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)) σ' σ).re :=
  ⟨onSiteS_mul_onSiteS_apply_im_zero_of_real (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_im_zero N) hxy σ' σ,
    onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_re_nonneg N) (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_re_nonneg N) hxy σ' σ⟩

/-- The transverse hopping term `Ŝ⁺_x Ŝ⁻_y` has real, non-negative config-basis entries. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) σ' σ).im = 0 ∧
      0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) σ' σ).re :=
  ⟨onSiteS_mul_onSiteS_apply_im_zero_of_real (spinSOpPlus_apply_im_zero N)
      (spinSOpMinus_apply_im_zero N) hxy σ' σ,
    onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_re_nonneg N) (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_re_nonneg N) hxy σ' σ⟩

/-- The transverse hopping term `Ŝ⁻_x Ŝ⁺_y` has real, non-negative config-basis entries. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) σ' σ).im = 0 ∧
      0 ≤ ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) σ' σ).re :=
  ⟨onSiteS_mul_onSiteS_apply_im_zero_of_real (spinSOpMinus_apply_im_zero N)
      (spinSOpPlus_apply_im_zero N) hxy σ' σ,
    onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_re_nonneg N) (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_re_nonneg N) hxy σ' σ⟩

end LatticeSystem.Quantum
