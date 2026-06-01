import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement
import LatticeSystem.Quantum.SpinS.Problem25dLadderPositivity

/-!
# Tasaki Problem 2.5.d: signed ladder matrix entries

This module supplies the concrete matrix-entry sign input for the
`S_x^+ S_y^-` ladder positivity bridge in `Problem25dLadderPositivity`.
For a cross-sublattice pair `A x ≠ A y`, the bipartite gauge sign and the
Marshall sign product cancel on every non-zero `S_x^+ S_y^-` matrix entry,
leaving the bare non-negative real matrix entry.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution p. 498, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Signed `S_x^+ S_y^-` matrix entries -/

/-- On a cross-sublattice pair, the bipartite-gauge / Marshall-signed
`S_x^+ S_y^-` matrix entry has non-negative real part.  This is the concrete
matrix-entry sign input used in Tasaki's equation (S.23), p. 498. -/
theorem twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_bipartite_ne
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    (σ τ : V → Fin (N + 1)) :
    0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ *
      ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
      marshallSignS A τ).re := by
  classical
  let O : ℂ :=
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ)
  have hO_nonneg : 0 ≤ O.re :=
    onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg hxy σ τ
  have hO_im : O.im = 0 :=
    onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero hxy σ τ
  have hgauge : bipartiteGaugeSign A x * bipartiteGaugeSign A y = -1 :=
    bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy
  change 0 ≤ (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ * O * marshallSignS A τ).re)
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ k = τ k
  · by_cases hxraise : (σ x).val + 1 = (τ x).val
    · by_cases hylower : (τ y).val + 1 = (σ y).val
      · have hxodd : Odd ((σ x).val + (τ x).val) := by
          use (σ x).val
          omega
        have hyodd : Odd ((σ y).val + (τ y).val) := by
          use (τ y).val
          omega
        have hmarshall : marshallSignS A σ * marshallSignS A τ = -1 := by
          cases hAx : A x <;> cases hAy : A y
          · exact (hAxy (by rw [hAx, hAy])).elim
          · exact marshallSignS_mul_of_agree_off_two_site_bipartite_y
              A hxy hAx hAy hagree hyodd
          · exact marshallSignS_mul_of_agree_off_two_site_bipartite_x
              A hxy hAx hAy hagree hxodd
          · exact (hAxy (by rw [hAx, hAy])).elim
        calc
          ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
              marshallSignS A σ * O * marshallSignS A τ).re
              = (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
                  (marshallSignS A σ * marshallSignS A τ)) * O).re := by ring_nf
          _ = O.re := by rw [hgauge, hmarshall]; norm_num
          _ ≥ 0 := hO_nonneg
      · have hzero : O = 0 := by
          unfold O
          rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
            hxy hagree]
          rw [spinSOpMinus_apply_other N hylower]
          ring
        rw [hzero]
        simp
    · have hzero : O = 0 := by
        unfold O
        rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
          hxy hagree]
        rw [spinSOpPlus_apply_other N hxraise]
        ring
      rw [hzero]
      simp
  · have hzero : O = 0 :=
      by
        unfold O
        exact onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_off_two_site_diff
          hxy hagree
    rw [hzero]
    simp

/-- For `N ≥ 1`, a cross-sublattice pair has an explicit strictly positive
bipartite-gauge / Marshall-signed `S_x^+ S_y^-` matrix entry.  This supplies
the strict witness required by the finite-sum positivity bridge in Tasaki's
equation (S.23), p. 498. -/
theorem exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N) :
    ∃ σ τ : V → Fin (N + 1),
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        marshallSignS A τ).re := by
  classical
  let oneS : Fin (N + 1) := ⟨1, by omega⟩
  let zeroS : Fin (N + 1) := 0
  let σ : V → Fin (N + 1) := fun z => if z = x then zeroS else if z = y then oneS else zeroS
  let τ : V → Fin (N + 1) := fun z => if z = x then oneS else zeroS
  refine ⟨σ, τ, ?_⟩
  let O : ℂ :=
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ)
  have hgauge : bipartiteGaugeSign A x * bipartiteGaugeSign A y = -1 :=
    bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy
  have hagree : ∀ k, k ≠ x → k ≠ y → σ k = τ k := by
    intro k hkx hky
    simp [σ, τ, hkx, hky]
  have hxraise : (σ x).val + 1 = (τ x).val := by
    simp [σ, τ, oneS, zeroS]
  have hylower : (τ y).val + 1 = (σ y).val := by
    simp [σ, τ, oneS, zeroS, hxy.symm]
  have hxodd : Odd ((σ x).val + (τ x).val) := by
    use 0
    simp [σ, τ, oneS, zeroS]
  have hyodd : Odd ((σ y).val + (τ y).val) := by
    use 0
    simp [σ, τ, oneS, zeroS, hxy.symm]
  have hmarshall : marshallSignS A σ * marshallSignS A τ = -1 := by
    cases hAx : A x <;> cases hAy : A y
    · exact (hAxy (by rw [hAx, hAy])).elim
    · exact marshallSignS_mul_of_agree_off_two_site_bipartite_y
        A hxy hAx hAy hagree hyodd
    · exact marshallSignS_mul_of_agree_off_two_site_bipartite_x
        A hxy hAx hAy hagree hxodd
    · exact (hAxy (by rw [hAx, hAy])).elim
  have hO_pos : 0 < O.re := by
    unfold O
    rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
      hxy hagree]
    rw [Complex.mul_re, spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
    simp only [mul_zero, sub_zero]
    exact mul_pos (spinSOpPlus_apply_re_pos_of_raise N hxraise)
      (spinSOpMinus_apply_re_pos_of_lower N hylower)
  change 0 < (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ * O * marshallSignS A τ).re)
  calc
    (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ * O * marshallSignS A τ).re)
        = (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
            (marshallSignS A σ * marshallSignS A τ)) * O).re := by ring_nf
    _ = O.re := by rw [hgauge, hmarshall]; norm_num
    _ > 0 := hO_pos

/-! ## Correlation positivity from concrete signed entries -/

/-- Concrete Problem 2.5.d ladder positivity package: for `N ≥ 1` and a
cross-sublattice pair `A x ≠ A y`, strictly positive Marshall coefficients
imply a positive bipartite-gauge-signed `S_x^+ S_y^-` correlation. -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_coefficients_cross
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (c : (V → Fin (N + 1)) → ℝ) (hc_pos : ∀ σ, 0 < c σ) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  exact twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_coefficients
    A x y c hc_pos
    (twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_bipartite_ne A hxy hAxy)
    (exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne A hxy hAxy hN)

end LatticeSystem.Quantum
