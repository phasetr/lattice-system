import LatticeSystem.Quantum.SpinS.DressedAxisSwapParityBondStrictPos
import LatticeSystem.Quantum.SpinS.SingleIonOffDiag
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondSign

/-!
# Dressed axis-swap single-ion strict positivity: per-term inputs (foundation)

Foundational layer extracted from `DressedAxisSwapSingleIonStrictPos.lean` for build speed.
This file proves the strict positivity of `(Ŝ⁺)²` / `(Ŝ⁻)²` at the matching `±2` entry, the
single-ion sum on a `±2` move (only the `x` term survives, strict negative), and the vanishing
of bonds for a single-ion `±2` move.

The full `Ĥ'` strict negativity and shifted strict positivity
(`shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS`) are kept in the capstone module
`DressedAxisSwapSingleIonStrictPos.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Strict positivity of `(Ŝ⁺)²` / `(Ŝ⁻)²` at the matching `±2` entry. -/

/-- `(Ŝ⁺)² (i, i+2)` is strict positive real. -/
theorem spinSOpPlus_mul_spinSOpPlus_apply_re_pos_of_diff_two (N : ℕ) {i j : Fin (N + 1)}
    (h : i.val + 2 = j.val) :
    0 < ((spinSOpPlus N * spinSOpPlus N) i j).re := by
  have hi1_lt : i.val + 1 < N + 1 := by have := j.isLt; omega
  set k : Fin (N + 1) := ⟨i.val + 1, hi1_lt⟩
  have hk_eq_sum_pick : (spinSOpPlus N * spinSOpPlus N) i j =
      spinSOpPlus N i k * spinSOpPlus N k j := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · intro b _ hbk
      by_cases hib : i.val + 1 = b.val
      · exact absurd (Fin.ext hib : k = b).symm hbk
      · rw [spinSOpPlus_apply_other N hib, zero_mul]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hk_eq_sum_pick, Complex.mul_re,
    spinSOpPlus_apply_im_zero, spinSOpPlus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpPlus_apply_re_pos_of_raise N rfl)
    (spinSOpPlus_apply_re_pos_of_raise N (by show k.val + 1 = j.val; omega))

/-- `(Ŝ⁻)² (i, j)` is strict positive real for `j+2 = i`. -/
theorem spinSOpMinus_mul_spinSOpMinus_apply_re_pos_of_diff_two (N : ℕ) {i j : Fin (N + 1)}
    (h : j.val + 2 = i.val) :
    0 < ((spinSOpMinus N * spinSOpMinus N) i j).re := by
  have hj1_lt : j.val + 1 < N + 1 := by have := i.isLt; omega
  set k : Fin (N + 1) := ⟨j.val + 1, hj1_lt⟩
  have hk_eq_sum_pick : (spinSOpMinus N * spinSOpMinus N) i j =
      spinSOpMinus N i k * spinSOpMinus N k j := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · intro b _ hbk
      by_cases hib : b.val + 1 = i.val
      · by_cases hjb : j.val + 1 = b.val
        · exact absurd (Fin.ext hjb : k = b).symm hbk
        · rw [spinSOpMinus_apply_other N hjb, mul_zero]
      · rw [spinSOpMinus_apply_other N hib, zero_mul]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hk_eq_sum_pick, Complex.mul_re,
    spinSOpMinus_apply_im_zero, spinSOpMinus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpMinus_apply_re_pos_of_lower N (by show k.val + 1 = i.val; omega))
    (spinSOpMinus_apply_re_pos_of_lower N rfl)

/-- The single-site `(Ŝ²)²` off-diagonal entry is strict negative real for `±2` Fin index. -/
theorem spinSOp2_mul_spinSOp2_apply_re_neg_of_diff_two (N : ℕ) {i j : Fin (N + 1)}
    (h : i.val + 2 = j.val ∨ j.val + 2 = i.val) :
    ((spinSOp2 N * spinSOp2 N) i j).re < 0 := by
  have hij : i ≠ j := by
    intro he; subst he
    rcases h with h | h <;> omega
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij, Complex.mul_re]
  have hcre : (-(1 / 4 : ℂ)).re = -(1 / 4) := by simp
  have hcim : (-(1 / 4 : ℂ)).im = 0 := by simp
  rw [hcre, hcim, zero_mul, sub_zero, Complex.add_re]
  have hpp_nn : 0 ≤ ((spinSOpPlus N * spinSOpPlus N) i j).re :=
    matrix_mul_self_apply_re_nonneg (spinSOpPlus_apply_im_zero N)
      (spinSOpPlus_apply_re_nonneg N) i j
  have hmm_nn : 0 ≤ ((spinSOpMinus N * spinSOpMinus N) i j).re :=
    matrix_mul_self_apply_re_nonneg (spinSOpMinus_apply_im_zero N)
      (spinSOpMinus_apply_re_nonneg N) i j
  rcases h with h | h
  · have hpp_pos := spinSOpPlus_mul_spinSOpPlus_apply_re_pos_of_diff_two N h
    nlinarith
  · have hmm_pos := spinSOpMinus_mul_spinSOpMinus_apply_re_pos_of_diff_two N h
    nlinarith

/-! ## Single-ion sum on a `±2` move: only the `x` term survives, strict negative. -/

/-- The single-ion term at `y ≠ x` vanishes on a same-site `±2` move at `x`. -/
theorem onSiteS_spinSOp2_sq_apply_eq_zero_of_singleIon_off_site
    {x : Λ} {σ' σ : Λ → Fin (N + 1)} (hsx_ne : σ' x ≠ σ x)
    {y : Λ} (hyx : y ≠ x) :
    (onSiteS y (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  apply onSiteS_apply_eq_zero_of_off_site_diff
  intro h
  exact hsx_ne (h x (Ne.symm hyx))

/-- The single-ion term at `x` is strict negative real on a same-site `±2` move at `x`. -/
theorem onSiteS_spinSOp2_sq_apply_re_neg_of_singleIon_witness
    {x : Λ} {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    ((onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ).re < 0 := by
  rw [onSiteS_apply, if_pos hagree]
  exact spinSOp2_mul_spinSOp2_apply_re_neg_of_diff_two N hsx.symm

/-- Dressed `onSiteS x (Ŝ²)²` off-diagonal Re is strict negative on a `±2` move at `x`. -/
theorem dressed_onSiteS_spinSOp2_sq_re_neg_of_singleIon_witness
    (A : Λ → Bool) {x : Λ} {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' *
      (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ).re < 0 := by
  have hpar : Even ((σ' x).val + (σ x).val) := by
    rcases hsx with h | h <;> · rw [Nat.even_iff]; omega
  have heven : marshallSignS A σ' * marshallSignS A σ = 1 := by
    rw [marshallSignS_mul_of_agree_off_site A x hagree]
    split_ifs with hAx
    · rw [Even.neg_one_pow hpar]
    · rfl
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'), heven, one_mul]
  exact onSiteS_spinSOp2_sq_apply_re_neg_of_singleIon_witness hsx hagree

/-! ## Bonds vanish for a single-ion `±2` move. -/

/-- On a same-site `±2` move at `x`, every cross-site bond `spinSDotXXZSwap a b` vanishes
(`a ≠ b`). -/
theorem spinSDotXXZSwap_apply_eq_zero_of_singleIonStep
    {x : Λ} {a b : Λ} (hab : a ≠ b) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    spinSDotXXZSwap a b lam N σ' σ = 0 := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsx with h | h <;> · rw [he] at h; omega
  by_cases ha_x : a = x
  · -- a = x: factor at x must vanish since no single-ladder connects ±2 shift.
    have hxr : (σ a).val + 1 ≠ (σ' a).val := by subst ha_x; rcases hsx with h | h <;> omega
    have hxl : (σ' a).val + 1 ≠ (σ a).val := by subst ha_x; rcases hsx with h | h <;> omega
    exact spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hab lam hne hxr hxl
  · by_cases hb_x : b = x
    · -- b = x: factor at x must vanish.
      have hyr : (σ b).val + 1 ≠ (σ' b).val := by subst hb_x; rcases hsx with h | h <;> omega
      have hyl : (σ' b).val + 1 ≠ (σ b).val := by subst hb_x; rcases hsx with h | h <;> omega
      exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hab lam hne hyr hyl
    · -- x ∉ {a, b}: configurations disagree at x, hence not agree-off-{a, b}.
      have hng : ¬ (∀ k, k ≠ a → k ≠ b → σ' k = σ k) := by
        intro h
        have hxa : x ≠ a := fun h => ha_x h.symm
        have hxb : x ≠ b := fun h => hb_x h.symm
        have := h x hxa hxb
        rcases hsx with h2 | h2 <;> · rw [this] at h2; omega
      exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hab lam hng

end LatticeSystem.Quantum
