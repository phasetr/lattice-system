import LatticeSystem.Quantum.SpinS.Problem25cZAxisGroundStatePhase
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

/-!
# Problem 2.5.c axis-swap ground-state phase: reduction and phase input (foundation)

Foundational layer extracted from `Problem25cAxisSwapGroundStatePhase.lean` for build speed.  This
file builds the SU(2)-point axis-swap reduction, the lifted axis-swap commutation and unitarity, and
the Heisenberg eigenspace phase input.

The Problem 2.5.c squared-expectation wrappers are kept in the capstone module
`Problem25cAxisSwapGroundStatePhase.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## SU(2)-point axis-swap reduction -/

/-- At `λ = 1`, the axis-swapped XXZ bond is the isotropic spin-`S` dot product. -/
theorem spinSDotXXZSwap_one (x y : V) (N : ℕ) :
    spinSDotXXZSwap x y 1 N = spinSDot x y N := by
  rw [spinSDotXXZSwap_def, spinSDot_def, one_smul]

/-- The axis-swapped single-ion term vanishes at `D = 0`. -/
theorem singleIonAnisotropyS2_zero (N : ℕ) :
    singleIonAnisotropyS2 (Λ := V) 0 N = 0 := by
  rw [singleIonAnisotropyS2, zero_smul]

/-- At `λ = 1, D = 0`, the axis-swapped anisotropic Hamiltonian is the isotropic
Heisenberg Hamiltonian. -/
theorem axisSwappedAnisotropicHeisenbergS_one_zero (J : V → V → ℂ) (N : ℕ) :
    axisSwappedAnisotropicHeisenbergS (Λ := V) J 1 0 N = heisenbergHamiltonianS J N := by
  rw [axisSwappedAnisotropicHeisenbergS_def, singleIonAnisotropyS2_zero, add_zero,
    heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [spinSDotXXZSwap_one]

/-! ## Lifted axis-swap commutation and unitarity -/

/-- The lifted concrete spin-`S` axis swap conjugates the Heisenberg Hamiltonian
to itself. -/
theorem axisSwapUnitarySSpinS_tensor_conj_heisenbergHamiltonianS
    (J : V → V → ℂ) :
    (axisSwapUnitarySSpinS N).tensor V * heisenbergHamiltonianS J N *
        (axisSwapUnitarySSpinS N).tensorInv V =
      heisenbergHamiltonianS J N := by
  have h :=
    (axisSwapUnitarySSpinS N).tensor_conj_anisotropicHeisenbergS
      (Λ := V) J 1 0
  rw [anisotropicHeisenbergS_one_zero, axisSwappedAnisotropicHeisenbergS_one_zero] at h
  exact h

/-- The Heisenberg Hamiltonian commutes with the inverse lifted concrete spin-`S`
axis swap. -/
theorem heisenbergHamiltonianS_commute_axisSwapUnitarySSpinS_tensorInv
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) ((axisSwapUnitarySSpinS N).tensorInv V) := by
  have hconj := axisSwapUnitarySSpinS_tensor_conj_heisenbergHamiltonianS
    (V := V) (N := N) J
  have h := congrArg (fun M : ManyBodyOpS V N =>
    (axisSwapUnitarySSpinS N).tensorInv V * M) hconj
  change (axisSwapUnitarySSpinS N).tensorInv V *
      ((axisSwapUnitarySSpinS N).tensor V * heisenbergHamiltonianS J N *
        (axisSwapUnitarySSpinS N).tensorInv V) =
    (axisSwapUnitarySSpinS N).tensorInv V * heisenbergHamiltonianS J N at h
  rw [show (axisSwapUnitarySSpinS N).tensorInv V *
        ((axisSwapUnitarySSpinS N).tensor V * heisenbergHamiltonianS J N *
          (axisSwapUnitarySSpinS N).tensorInv V) =
        ((axisSwapUnitarySSpinS N).tensorInv V * (axisSwapUnitarySSpinS N).tensor V) *
          heisenbergHamiltonianS J N * (axisSwapUnitarySSpinS N).tensorInv V by
      simp only [mul_assoc],
    (axisSwapUnitarySSpinS N).tensorInv_mul_tensor (Λ := V)] at h
  simpa only [one_mul] using h

/-- The adjoint of the inverse lifted concrete spin-`S` axis swap is the lifted
axis swap. -/
theorem axisSwapUnitarySSpinS_tensorInv_conjTranspose :
    ((axisSwapUnitarySSpinS N).tensorInv V).conjTranspose =
      (axisSwapUnitarySSpinS N).tensor V := by
  rw [AxisSwapUnitaryS.tensorInv, AxisSwapUnitaryS.tensor, manyBodyTensorS_conjTranspose]
  simp [axisSwapUnitarySSpinS, spinSRot1_adjoint]

/-- The inverse lifted concrete spin-`S` axis swap is unitary in the form
`Uᴴ * U = 1`. -/
theorem axisSwapUnitarySSpinS_tensorInv_conjTranspose_mul_self :
    ((axisSwapUnitarySSpinS N).tensorInv V).conjTranspose *
        (axisSwapUnitarySSpinS N).tensorInv V = 1 := by
  rw [axisSwapUnitarySSpinS_tensorInv_conjTranspose]
  exact (axisSwapUnitarySSpinS N).tensor_mul_tensorInv (Λ := V)

/-! ## Heisenberg eigenspace phase input -/

/-- A normalized non-zero vector in a one-dimensional Heisenberg eigenspace is
fixed up to a unit-modulus phase by the inverse lifted axis-swap unitary. -/
theorem exists_phase_unit_of_heisenbergHamiltonianS_axisSwapUnitarySSpinS_tensorInv
    (J : V → V → ℂ) (μ : ℂ) {Φ : (V → Fin (N + 1)) → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ) :
    ∃ c : ℂ,
      ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = c • Φ ∧
        star c * c = 1 :=
  exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute
    huniq hΦ_ne hΦnorm hΦ
    (heisenbergHamiltonianS_commute_axisSwapUnitarySSpinS_tensorInv
      (V := V) (N := N) J).eq
    (axisSwapUnitarySSpinS_tensorInv_conjTranspose_mul_self (V := V) (N := N))

end LatticeSystem.Quantum
