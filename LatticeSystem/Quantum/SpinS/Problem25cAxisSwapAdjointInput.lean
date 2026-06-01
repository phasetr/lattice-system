import LatticeSystem.Quantum.SpinS.Problem25cUnitaryAxisInput
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS

/-!
# Tasaki Problem 2.5.c: lifted axis-swap adjoint input

This module instantiates the unitary-invariance bridge from
`Problem25cUnitaryAxisInput.lean` for the lifted axis-swap unitary already built
for Tasaki §2.5 Theorem 2.4.  The main auxiliary input is that the adjoint of a
many-body tensor is the tensor of the single-site adjoints.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Tensor adjoints -/

omit [DecidableEq V] in
/-- The adjoint of a many-body tensor is the many-body tensor of the single-site
adjoints. -/
theorem manyBodyTensorS_conjTranspose
    (W : V → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (manyBodyTensorS W).conjTranspose =
      manyBodyTensorS (fun x => (W x).conjTranspose) := by
  ext σ' σ
  simp [manyBodyTensorS_apply, Matrix.conjTranspose_apply]

namespace AxisSwapUnitaryS

variable (G : AxisSwapUnitaryS N)

/-- A single-site adjoint identity `U† = U⁻¹` lifts to the many-body tensor
axis-swap unitary. -/
theorem tensor_conjTranspose {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (hUadj : G.U.conjTranspose = G.Uinv) :
    (G.tensor Λ).conjTranspose = G.tensorInv Λ := by
  simpa [tensor, tensorInv, hUadj] using
    (manyBodyTensorS_conjTranspose (V := Λ) (N := N) (fun _ : Λ => G.U))

end AxisSwapUnitaryS

/-! ## The concrete spin-S axis swap -/

/-- The single-site adjoint identity for the concrete spin-S axis swap. -/
theorem axisSwapUnitarySSpinS_U_conjTranspose (N : ℕ) :
    (axisSwapUnitarySSpinS N).U.conjTranspose =
      (axisSwapUnitarySSpinS N).Uinv := by
  simpa [axisSwapUnitarySSpinS] using spinSRot1_adjoint N (Real.pi / 2)

/-- The lifted adjoint identity for the concrete spin-S axis swap. -/
theorem axisSwapUnitarySSpinS_tensor_conjTranspose
    (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) :
    ((axisSwapUnitarySSpinS N).tensor V).conjTranspose =
      (axisSwapUnitarySSpinS N).tensorInv V :=
  (axisSwapUnitarySSpinS N).tensor_conjTranspose
    (Λ := V) (axisSwapUnitarySSpinS_U_conjTranspose N)

/-! ## Axis-2 / axis-3 squared expectations -/

/-- If the state is fixed by the inverse lifted spin-S axis swap, then the
single-site squared expectations for axes 3 and 2 are equal. -/
theorem singleSiteSpinSquareExpectationS_axis3_eq_axis2_of_axisSwapInvariant
    (x : V) (Φ : (V → Fin (N + 1)) → ℂ)
    (hΦ : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ := by
  refine singleSiteSpinSquareExpectationS_eq_of_conj_invariant
    (x := x) (A := spinSOp2 N) (B := spinSOp3 N)
    (T := (axisSwapUnitarySSpinS N).tensor V)
    (Tinv := (axisSwapUnitarySSpinS N).tensorInv V) (Φ := Φ)
    ?hTadj ?hTinvT hΦ ?hconj
  · exact axisSwapUnitarySSpinS_tensor_conjTranspose V N
  · exact (axisSwapUnitarySSpinS N).tensorInv_mul_tensor (Λ := V)
  · have hconj :=
      (axisSwapUnitarySSpinS N).tensor_conj_onSiteS
        (Λ := V) x (spinSOp2 N)
    rw [(axisSwapUnitarySSpinS N).conj_spinSOp2] at hconj
    exact hconj

end LatticeSystem.Quantum
