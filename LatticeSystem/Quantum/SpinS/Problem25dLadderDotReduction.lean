import LatticeSystem.Quantum.SpinS.Problem25dLadderEntrySign

/-!
# Tasaki Problem 2.5.d: ladder-to-dot correlation reduction

This module packages the algebraic bridge from signed ladder correlation
positivity to signed two-spin dot-product correlation positivity.  The core
input is the standard decomposition

`S_x · S_y = 1/2 (S_x^+ S_y^- + S_x^- S_y^+) + S_x^3 S_y^3`.

The final SU(2)-ground-state argument will supply the component equalities
used by the sign-transfer wrapper below.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution p. 498, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Remaining two-site component correlations -/

/-- The transverse ladder correlation expectation
`⟨Φ, (Ŝ_x^- Ŝ_y^+) Φ⟩` for a spin-`S` many-body state. -/
noncomputable def twoSpinMinusPlusCorrelationS (x y : V)
    [Fintype V] [DecidableEq V]
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ)
    (((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) : ManyBodyOpS V N).mulVec Φ)

/-- The longitudinal two-site correlation expectation
`⟨Φ, (Ŝ_x^3 Ŝ_y^3) Φ⟩` for a spin-`S` many-body state. -/
noncomputable def twoSpinZZCorrelationS (x y : V)
    [Fintype V] [DecidableEq V]
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ)
    (((onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) : ManyBodyOpS V N).mulVec Φ)

/-! ## Correlation-level plus/minus decomposition -/

/-- Correlation-level form of
`Ŝ_x · Ŝ_y = 1/2 (Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^3 Ŝ_y^3`. -/
theorem twoSpinCorrelationS_eq_ladder_components
    [Fintype V] [DecidableEq V]
    (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) :
    twoSpinCorrelationS x y Φ =
      (1 / 2 : ℂ) *
        (twoSpinPlusMinusCorrelationS x y Φ + twoSpinMinusPlusCorrelationS x y Φ) +
      twoSpinZZCorrelationS x y Φ := by
  unfold twoSpinCorrelationS twoSpinPlusMinusCorrelationS twoSpinMinusPlusCorrelationS
    twoSpinZZCorrelationS
  rw [spinSDot_eq_plus_minus]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]

/-- Signed version of the correlation-level plus/minus decomposition. -/
theorem signed_twoSpinCorrelationS_eq_ladder_components
    [Fintype V] [DecidableEq V]
    (g : ℂ) (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) :
    g * twoSpinCorrelationS x y Φ =
      (1 / 2 : ℂ) *
        (g * twoSpinPlusMinusCorrelationS x y Φ +
          g * twoSpinMinusPlusCorrelationS x y Φ) +
      g * twoSpinZZCorrelationS x y Φ := by
  rw [twoSpinCorrelationS_eq_ladder_components]
  ring

/-! ## Positivity transfer under SU(2) component equalities -/

/-- If the signed `S_x^- S_y^+` and `S_x^3 S_y^3` components have the
SU(2)-symmetric real parts expected from the signed `S_x^+ S_y^-` component,
then positivity of the signed `S_x^+ S_y^-` correlation transfers to the
signed dot-product correlation. -/
theorem signed_twoSpinCorrelationS_re_pos_of_ladder_component_equalities
    [Fintype V] [DecidableEq V]
    (g : ℂ) (x y : V) (Φ : (V → Fin (N + 1)) → ℂ)
    (hpm_pos : 0 < (g * twoSpinPlusMinusCorrelationS x y Φ).re)
    (hmp_eq : (g * twoSpinMinusPlusCorrelationS x y Φ).re =
      (g * twoSpinPlusMinusCorrelationS x y Φ).re)
    (hzz_eq : (g * twoSpinZZCorrelationS x y Φ).re =
      (1 / 2 : ℝ) * (g * twoSpinPlusMinusCorrelationS x y Φ).re) :
    0 < (g * twoSpinCorrelationS x y Φ).re := by
  let p : ℝ := (g * twoSpinPlusMinusCorrelationS x y Φ).re
  have hdecomp :
      (g * twoSpinCorrelationS x y Φ).re =
        (1 / 2 : ℝ) *
            (p + (g * twoSpinMinusPlusCorrelationS x y Φ).re) +
          (g * twoSpinZZCorrelationS x y Φ).re := by
    rw [signed_twoSpinCorrelationS_eq_ladder_components]
    simp [p]
  rw [hdecomp, hmp_eq, hzz_eq]
  change 0 < (1 / 2 : ℝ) * (p + p) + (1 / 2 : ℝ) * p
  nlinarith [hpm_pos]

/-- Bipartite-gauge specialization of
`signed_twoSpinCorrelationS_re_pos_of_ladder_component_equalities`. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_ladder_component_equalities
    [Fintype V] [DecidableEq V]
    (A : V → Bool) (x y : V) (Φ : (V → Fin (N + 1)) → ℂ)
    (hpm_pos : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y Φ).re)
    (hmp_eq : ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinMinusPlusCorrelationS x y Φ).re =
        ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
          twoSpinPlusMinusCorrelationS x y Φ).re)
    (hzz_eq : ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinZZCorrelationS x y Φ).re =
        (1 / 2 : ℝ) * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
          twoSpinPlusMinusCorrelationS x y Φ).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φ).re :=
  signed_twoSpinCorrelationS_re_pos_of_ladder_component_equalities
    (bipartiteGaugeSign A x * bipartiteGaugeSign A y) x y Φ hpm_pos hmp_eq hzz_eq

/-- Conditional Problem 2.5.d package: for cross-sublattice pairs, strictly
positive Marshall coefficients and the SU(2) component equalities transfer the
PR #4071 signed ladder positivity to signed dot-product positivity. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_components
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (c : (V → Fin (N + 1)) → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hmp_eq :
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinMinusPlusCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re =
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re)
    (hzz_eq :
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinZZCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re =
      (1 / 2 : ℝ) * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y
          (fun σ => marshallSignS A σ * (c σ : ℂ))).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_ladder_component_equalities
    A x y (fun σ => marshallSignS A σ * (c σ : ℂ))
    (twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_coefficients_cross
      A hxy hAxy hN c hc_pos)
    hmp_eq hzz_eq

end LatticeSystem.Quantum
