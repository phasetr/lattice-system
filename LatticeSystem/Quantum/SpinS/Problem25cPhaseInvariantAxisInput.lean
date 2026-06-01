import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationInput

/-!
# Tasaki Problem 2.5.c: phase-invariant unitary symmetry input

This module weakens the exact state-invariance hypothesis used in
`Problem25cUnitaryAxisInput.lean` and `Problem25cTwoSymmetryAxisInput.lean`.
For squared single-site expectations, it is enough for the inverse unitary to
fix the state up to a phase `c` with `star c * c = 1`.

This is the natural interface for the remaining SU(2)-symmetry step in Tasaki
Problem 2.5.c: a one-dimensional ground eigenspace is expected to be preserved
by a commuting rotation only up to scalar phase.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Generic phase-invariant bridge -/

/-- If `T` conjugates the single-site operator `A` to `B` and `Φ` is fixed by
`T⁻¹ = T†` up to a unit-modulus phase, then the squared single-site
expectations of `A` and `B` in `Φ` are equal. -/
theorem singleSiteSpinSquareExpectationS_eq_of_conj_phaseInvariant
    (x : V) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (T Tinv : ManyBodyOpS V N) (Φ : (V → Fin (N + 1)) → ℂ) (c : ℂ)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦ : Tinv.mulVec Φ = c • Φ)
    (hc : star c * c = 1)
    (hconj : T * onSiteS x A * Tinv = onSiteS x B) :
    singleSiteSpinSquareExpectationS x B Φ =
      singleSiteSpinSquareExpectationS x A Φ := by
  let OA : ManyBodyOpS V N := onSiteS x A
  let OB : ManyBodyOpS V N := onSiteS x B
  have hOB : OB = T * OA * Tinv := by
    simpa [OA, OB] using hconj.symm
  have hsq : OB * OB = T * (OA * OA) * Tinv := by
    calc
      OB * OB = (T * OA * Tinv) * (T * OA * Tinv) := by rw [hOB]
      _ = T * (OA * OA) * Tinv := by
        rw [show (T * OA * Tinv) * (T * OA * Tinv) =
            T * OA * (Tinv * T) * OA * Tinv by simp only [mul_assoc]]
        rw [hTinvT]
        simp only [mul_one, mul_assoc]
  have hc' : c * star c = 1 := by
    rw [mul_comm, hc]
  unfold singleSiteSpinSquareExpectationS
  calc
    dotProduct (star Φ) ((OB * OB).mulVec Φ) =
        dotProduct (star Φ) ((T * (OA * OA) * Tinv).mulVec Φ) := by rw [hsq]
    _ = dotProduct (star Φ) (T.mulVec ((OA * OA).mulVec (Tinv.mulVec Φ))) := by
      rw [show (T * (OA * OA) * Tinv).mulVec Φ =
          T.mulVec ((OA * OA).mulVec (Tinv.mulVec Φ)) from by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    _ = dotProduct (star Φ) (T.mulVec ((OA * OA).mulVec (c • Φ))) := by rw [hΦ]
    _ = c • dotProduct (star Φ) (T.mulVec ((OA * OA).mulVec Φ)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul]
    _ = c • dotProduct (star (T.conjTranspose.mulVec Φ)) ((OA * OA).mulVec Φ) := by
      rw [dotProduct_star_mulVec_eq_dotProduct_star_conjTranspose_mulVec]
    _ = c • dotProduct (star (c • Φ)) ((OA * OA).mulVec Φ) := by
      rw [hTadj, hΦ]
    _ = c • (star c • dotProduct (star Φ) ((OA * OA).mulVec Φ)) := by
      rw [star_smul, smul_dotProduct]
    _ = dotProduct (star Φ) ((OA * OA).mulVec Φ) := by
      rw [smul_smul, hc', one_smul]

/-! ## Problem 2.5.c axis wrappers -/

/-- Phase-invariant version of the remaining axis-1/axis-2 unitary input for
Problem 2.5.c. -/
theorem singleSiteSpinSquareExpectationS_axis1_eq_axis2_of_unitaryPhaseInvariant
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (T Tinv : ManyBodyOpS V N) (c : ℂ)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦ : Tinv.mulVec Φ = c • Φ)
    (hc : star c * c = 1)
    (hconj : T * onSiteS x (spinSOp2 N) * Tinv = onSiteS x (spinSOp1 N)) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
  singleSiteSpinSquareExpectationS_eq_of_conj_phaseInvariant
    (x := x) (A := spinSOp2 N) (B := spinSOp1 N)
    (T := T) (Tinv := Tinv) (Φ := Φ) (c := c)
    hTadj hTinvT hΦ hc hconj

/-- If a normalized state is fixed by the lifted axis-swap inverse and is fixed
up to a unit-modulus phase by a second unitary that maps axis 2 to axis 1, then
all three squared single-site spin expectations have value `N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_unitary_phase_axis12
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ)
    (T Tinv : ManyBodyOpS V N) (c : ℂ)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦunitary : Tinv.mulVec Φ = c • Φ)
    (hc : star c * c = 1)
    (hconj : T * onSiteS x (spinSOp2 N) * Tinv = onSiteS x (spinSOp1 N)) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  have h12 :
      singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
    singleSiteSpinSquareExpectationS_axis1_eq_axis2_of_unitaryPhaseInvariant
      (x := x) (T := T) (Tinv := Tinv) (c := c)
      hTadj hTinvT hΦunitary hc hconj
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_axis1_eq_axis2
    (x := x) hΦnorm hΦswap h12

/-! ## Concrete z-axis rotation phase wrapper -/

/-- Phase-invariant version of the concrete z-axis rotation input: if a
normalized state is fixed by the lifted axis-swap inverse and by the inverse
lifted z-axis rotation up to a unit-modulus phase, then all three squared
single-site spin expectations have value `N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_zAxisRot_phase
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ} (c : ℂ)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec Φ = c • Φ)
    (hc : star c * c = 1) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 :=
  singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_unitary_phase_axis12
    (x := x)
    hΦnorm hΦswap
    (T := manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))))
    (Tinv := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
    (c := c)
    (manyBodySpinSRot3_neg_pi_half_conjTranspose V N)
    (by
      rw [manyBodyTensorS_mul]
      simpa [spinSRot3_mul_neg] using manyBodyTensorS_one (Λ := V) (N := N))
    hΦrot hc
    (manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2 (x := x))

end LatticeSystem.Quantum
