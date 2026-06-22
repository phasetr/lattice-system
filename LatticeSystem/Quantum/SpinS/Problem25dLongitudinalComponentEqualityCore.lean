import LatticeSystem.Quantum.SpinS.Problem25dLadderAdjointEquality
import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapGroundStatePhase

/-!
# Problem 2.5.d longitudinal equality: phase-invariant bridges (foundation)

Foundational layer extracted from `Problem25dLongitudinalComponentEquality.lean` for build speed.
This file collects the two-site product expectations, the generic phase-invariant bridge, the axis
equalities from phase invariance, and the transverse ladder bridge.

The longitudinal equality and the Problem 2.5.d wrapper are kept in the capstone module
`Problem25dLongitudinalComponentEquality.lean`.
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

end LatticeSystem.Quantum
