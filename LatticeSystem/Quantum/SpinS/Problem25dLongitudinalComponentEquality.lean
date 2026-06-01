import LatticeSystem.Quantum.SpinS.Problem25dLadderAdjointEquality
import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapGroundStatePhase

/-!
# Tasaki Problem 2.5.d: longitudinal component equality

This module starts the remaining SU(2)-symmetry input for Problem 2.5.d.  The
first step is a two-site analogue of the phase-invariant expectation bridge
used in Problem 2.5.c: if a unitary conjugates one two-site spin product to
another and the state is invariant up to phase, their expectations agree.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 43, and solution pp. 498--499.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Two-site product expectations -/

/-- The two-site equal-axis product expectation
`⟨Φ, (Ŝ_x^A Ŝ_y^A) Φ⟩`, parametrized by the single-site matrix `A`. -/
noncomputable def twoSpinProductCorrelationS (x y : V)
    [Fintype V] [DecidableEq V]
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ)
    (((onSiteS x A * onSiteS y A) : ManyBodyOpS V N).mulVec Φ)

/-- The generic product correlation with `A = Ŝ^(3)` is the existing
longitudinal correlation. -/
theorem twoSpinProductCorrelationS_spinSOp3_eq_twoSpinZZCorrelationS
    [Fintype V] [DecidableEq V]
    (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) :
    twoSpinProductCorrelationS x y (spinSOp3 N) Φ =
      twoSpinZZCorrelationS x y Φ := by
  rfl

/-! ## Generic phase-invariant bridge -/

/-- If `T` conjugates one two-site product to another and `Φ` is fixed by
`T⁻¹ = T†` up to a unit-modulus phase, then the two product expectations in
`Φ` are equal. -/
theorem twoSpinProductCorrelationS_eq_of_conj_phaseInvariant
    [Fintype V] [DecidableEq V]
    (x y : V) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (T Tinv : ManyBodyOpS V N) (Φ : (V → Fin (N + 1)) → ℂ) (c : ℂ)
    (hTadj : T.conjTranspose = Tinv)
    (hΦ : Tinv.mulVec Φ = c • Φ)
    (hc : star c * c = 1)
    (hconj : T * (onSiteS x A * onSiteS y A) * Tinv =
      onSiteS x B * onSiteS y B) :
    twoSpinProductCorrelationS x y B Φ =
      twoSpinProductCorrelationS x y A Φ := by
  let OA : ManyBodyOpS V N := onSiteS x A * onSiteS y A
  let OB : ManyBodyOpS V N := onSiteS x B * onSiteS y B
  have hOB : OB = T * OA * Tinv := by
    simpa [OA, OB] using hconj.symm
  have hc' : c * star c = 1 := by
    rw [mul_comm, hc]
  unfold twoSpinProductCorrelationS
  calc
    dotProduct (star Φ) (OB.mulVec Φ) =
        dotProduct (star Φ) ((T * OA * Tinv).mulVec Φ) := by rw [hOB]
    _ = dotProduct (star Φ) (T.mulVec (OA.mulVec (Tinv.mulVec Φ))) := by
      rw [show (T * OA * Tinv).mulVec Φ =
          T.mulVec (OA.mulVec (Tinv.mulVec Φ)) from by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    _ = dotProduct (star Φ) (T.mulVec (OA.mulVec (c • Φ))) := by rw [hΦ]
    _ = c • dotProduct (star Φ) (T.mulVec (OA.mulVec Φ)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul]
    _ = c • dotProduct (star (T.conjTranspose.mulVec Φ)) (OA.mulVec Φ) := by
      rw [dotProduct_star_mulVec_eq_dotProduct_star_conjTranspose_mulVec]
    _ = c • dotProduct (star (c • Φ)) (OA.mulVec Φ) := by
      rw [hTadj, hΦ]
    _ = c • (star c • dotProduct (star Φ) (OA.mulVec Φ)) := by
      rw [star_smul, smul_dotProduct]
    _ = dotProduct (star Φ) (OA.mulVec Φ) := by
      rw [smul_smul, hc', one_smul]

/-- Conjugation distributes over a product if `Tinv` is a left inverse of `T`. -/
theorem conj_product_of_conj_factors
    [Fintype V] [DecidableEq V]
    (T Tinv P Q P' Q' : ManyBodyOpS V N)
    (hTinvT : Tinv * T = 1)
    (hP : T * P * Tinv = P')
    (hQ : T * Q * Tinv = Q') :
    T * (P * Q) * Tinv = P' * Q' := by
  rw [← hP, ← hQ]
  rw [show (T * P * Tinv) * (T * Q * Tinv) =
      T * (P * Q) * Tinv by
    rw [show (T * P * Tinv) * (T * Q * Tinv) =
        T * P * (Tinv * T) * Q * Tinv by simp only [mul_assoc]]
    rw [hTinvT]
    simp only [mul_one, mul_assoc]]

/-! ## Axis equalities from phase invariance -/

/-- Axis-swap phase invariance equates the axis-3 and axis-2 two-site product
expectations. -/
theorem twoSpinProductCorrelationS_axis3_eq_axis2_of_axisSwap_phase
    [Fintype V] [DecidableEq V]
    (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) (c : ℂ)
    (hΦ : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = c • Φ)
    (hc : star c * c = 1) :
    twoSpinProductCorrelationS x y (spinSOp3 N) Φ =
      twoSpinProductCorrelationS x y (spinSOp2 N) Φ := by
  refine twoSpinProductCorrelationS_eq_of_conj_phaseInvariant
    (x := x) (y := y) (A := spinSOp2 N) (B := spinSOp3 N)
    (T := (axisSwapUnitarySSpinS N).tensor V)
    (Tinv := (axisSwapUnitarySSpinS N).tensorInv V) (Φ := Φ) (c := c)
    ?hTadj hΦ hc ?hconj
  · exact axisSwapUnitarySSpinS_tensor_conjTranspose V N
  · refine conj_product_of_conj_factors
      ((axisSwapUnitarySSpinS N).tensor V)
      ((axisSwapUnitarySSpinS N).tensorInv V)
      (onSiteS x (spinSOp2 N)) (onSiteS y (spinSOp2 N))
      (onSiteS x (spinSOp3 N)) (onSiteS y (spinSOp3 N))
      ((axisSwapUnitarySSpinS N).tensorInv_mul_tensor (Λ := V)) ?hx ?hy
    · have hx :=
        (axisSwapUnitarySSpinS N).tensor_conj_onSiteS
          (Λ := V) x (spinSOp2 N)
      rw [(axisSwapUnitarySSpinS N).conj_spinSOp2] at hx
      exact hx
    · have hy :=
        (axisSwapUnitarySSpinS N).tensor_conj_onSiteS
          (Λ := V) y (spinSOp2 N)
      rw [(axisSwapUnitarySSpinS N).conj_spinSOp2] at hy
      exact hy

/-- Z-axis rotation phase invariance equates the axis-1 and axis-2 two-site
product expectations. -/
theorem twoSpinProductCorrelationS_axis1_eq_axis2_of_zAxisRot_phase
    [Fintype V] [DecidableEq V]
    (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) (c : ℂ)
    (hΦ :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec Φ =
        c • Φ)
    (hc : star c * c = 1) :
    twoSpinProductCorrelationS x y (spinSOp1 N) Φ =
      twoSpinProductCorrelationS x y (spinSOp2 N) Φ := by
  refine twoSpinProductCorrelationS_eq_of_conj_phaseInvariant
    (x := x) (y := y) (A := spinSOp2 N) (B := spinSOp1 N)
    (T := manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))))
    (Tinv := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
    (Φ := Φ) (c := c)
    ?hTadj hΦ hc ?hconj
  · exact manyBodySpinSRot3_neg_pi_half_conjTranspose V N
  · refine conj_product_of_conj_factors
      (manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))))
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
      (onSiteS x (spinSOp2 N)) (onSiteS y (spinSOp2 N))
      (onSiteS x (spinSOp1 N)) (onSiteS y (spinSOp1 N))
      ?hTinvT
      (manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2 (x := x))
      (manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2 (x := y))
    rw [manyBodyTensorS_mul]
    simpa [spinSRot3_mul_neg] using manyBodyTensorS_one (Λ := V) (N := N)

/-! ## Transverse ladder bridge -/

/-- The sum of the axis-1 and axis-2 product correlations equals the averaged
ladder-product correlation. -/
theorem twoSpinProductCorrelationS_axis1_add_axis2_eq_ladder
    [Fintype V] [DecidableEq V]
    (x y : V) (Φ : (V → Fin (N + 1)) → ℂ) :
    twoSpinProductCorrelationS x y (spinSOp1 N) Φ +
        twoSpinProductCorrelationS x y (spinSOp2 N) Φ =
      (1 / 2 : ℂ) *
        (twoSpinPlusMinusCorrelationS x y Φ +
          twoSpinMinusPlusCorrelationS x y Φ) := by
  have h := congrArg (fun M : ManyBodyOpS V N =>
      dotProduct (star Φ) (M.mulVec Φ))
    (onSiteS_spinSOp1_mul_add_onSiteS_spinSOp2_mul (N := N) x y)
  calc
    twoSpinProductCorrelationS x y (spinSOp1 N) Φ +
        twoSpinProductCorrelationS x y (spinSOp2 N) Φ =
      (1 / 2 : ℂ) * twoSpinPlusMinusCorrelationS x y Φ +
        (1 / 2 : ℂ) * twoSpinMinusPlusCorrelationS x y Φ := by
        simpa [twoSpinProductCorrelationS, twoSpinPlusMinusCorrelationS,
          twoSpinMinusPlusCorrelationS, Matrix.add_mulVec, Matrix.smul_mulVec,
          dotProduct_add, dotProduct_smul, smul_eq_mul] using h
    _ = (1 / 2 : ℂ) *
        (twoSpinPlusMinusCorrelationS x y Φ +
          twoSpinMinusPlusCorrelationS x y Φ) := by
      ring

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
