import LatticeSystem.Quantum.SpinS.Problem25dLongitudinalComponentEqualityCore

/-!
# Tasaki Problem 2.5.d: longitudinal component equality

This module starts the remaining SU(2)-symmetry input for Problem 2.5.d.  The
first step is a two-site analogue of the phase-invariant expectation bridge
used in Problem 2.5.c: if a unitary conjugates one two-site spin product to
another and the state is invariant up to phase, their expectations agree.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution pp. 498--499.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Longitudinal equality -/

/-- For a cross-sublattice pair, axis-swap and z-axis rotation phase
invariance identify the signed longitudinal real part with half of the signed
`S_x^+ S_y^-` ladder real part. -/
theorem bipartite_signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_axis_phases
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    (Φ : (V → Fin (N + 1)) → ℂ) (cswap crot : ℂ)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = cswap • Φ)
    (hcswap : star cswap * cswap = 1)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec Φ =
        crot • Φ)
    (hcrot : star crot * crot = 1) :
    ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinZZCorrelationS x y Φ).re =
    (1 / 2 : ℝ) * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y Φ).re := by
  let g : ℂ := bipartiteGaugeSign A x * bipartiteGaugeSign A y
  let C1 : ℂ := twoSpinProductCorrelationS x y (spinSOp1 N) Φ
  let C2 : ℂ := twoSpinProductCorrelationS x y (spinSOp2 N) Φ
  let C3 : ℂ := twoSpinProductCorrelationS x y (spinSOp3 N) Φ
  let P : ℂ := twoSpinPlusMinusCorrelationS x y Φ
  let M : ℂ := twoSpinMinusPlusCorrelationS x y Φ
  have h32 : C3 = C2 := by
    simpa [C2, C3] using
      (twoSpinProductCorrelationS_axis3_eq_axis2_of_axisSwap_phase
        (x := x) (y := y) (Φ := Φ) (c := cswap) hΦswap hcswap)
  have h12 : C1 = C2 := by
    simpa [C1, C2] using
      (twoSpinProductCorrelationS_axis1_eq_axis2_of_zAxisRot_phase
        (x := x) (y := y) (Φ := Φ) (c := crot) hΦrot hcrot)
  have htrans : C1 + C2 = (1 / 2 : ℂ) * (P + M) := by
    simpa [C1, C2, P, M] using
      (twoSpinProductCorrelationS_axis1_add_axis2_eq_ladder
        (N := N) x y Φ)
  have hsum : C2 + C2 = (1 / 2 : ℂ) * (P + M) := by
    simpa [h12] using htrans
  have hsum_re :
      (2 : ℝ) * (g * C2).re =
        (1 / 2 : ℝ) * ((g * P).re + (g * M).re) := by
    have h := congrArg (fun z : ℂ => (g * z).re) hsum
    calc
      (2 : ℝ) * (g * C2).re = (g * (C2 + C2)).re := by
        simp [Complex.mul_re]
        ring
      _ = (g * ((1 / 2 : ℂ) * (P + M))).re := h
      _ = (1 / 2 : ℝ) * ((g * P).re + (g * M).re) := by
        simp [Complex.mul_re]
        ring
  have hmp : (g * M).re = (g * P).re := by
    simpa [g, M, P] using
      (bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus
        A hxy hAxy Φ)
  have htarget : (g * C2).re = (1 / 2 : ℝ) * (g * P).re := by
    nlinarith
  change (g * twoSpinZZCorrelationS x y Φ).re = (1 / 2 : ℝ) * (g * P).re
  rw [← twoSpinProductCorrelationS_spinSOp3_eq_twoSpinZZCorrelationS]
  change (g * C3).re = (1 / 2 : ℝ) * (g * P).re
  rw [h32]
  exact htarget

/-! ## Problem 2.5.d wrapper -/

/-- Conditional Problem 2.5.d package after the longitudinal component equality:
for cross-sublattice pairs, strictly positive Marshall coefficients plus
axis-swap and z-axis rotation phase invariance transfer the PR #4071 signed
ladder positivity to signed dot-product positivity. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_axis_phases
    [Fintype V] [DecidableEq V]
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (c : (V → Fin (N + 1)) → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (cswap crot : ℂ)
    (hΦswap :
      ((axisSwapUnitarySSpinS N).tensorInv V).mulVec
          (fun σ => marshallSignS A σ * (c σ : ℂ)) =
        cswap • (fun σ => marshallSignS A σ * (c σ : ℂ)))
    (hcswap : star cswap * cswap = 1)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec
          (fun σ => marshallSignS A σ * (c σ : ℂ)) =
        crot • (fun σ => marshallSignS A σ * (c σ : ℂ)))
    (hcrot : star crot * crot = 1) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_cross_ladderAdjoint
    A hxy hAxy hN c hc_pos
    (bipartite_signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_axis_phases
      A hxy hAxy (fun σ => marshallSignS A σ * (c σ : ℂ))
      cswap crot hΦswap hcswap hΦrot hcrot)

end LatticeSystem.Quantum
