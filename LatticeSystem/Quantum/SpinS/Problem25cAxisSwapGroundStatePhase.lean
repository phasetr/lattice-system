import LatticeSystem.Quantum.SpinS.Problem25cZAxisGroundStatePhase
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

/-!
# Tasaki Problem 2.5.c: axis-swap ground-state phase input

This module removes the last exact axis-swap state-invariance hypothesis from
the Problem 2.5.c squared-expectation wrapper.  At the SU(2) point
`λ = 1, D = 0`, the axis-swapped anisotropic Hamiltonian also reduces to the
isotropic Heisenberg Hamiltonian.  Therefore the lifted spin-`S` axis-swap
unitary commutes with the Heisenberg Hamiltonian, and the one-dimensional
eigenspace phase bridge applies to its inverse.  The resulting unit-modulus
phase is enough for the axis-2/axis-3 squared-expectation equality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
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

/-! ## Problem 2.5.c squared-expectation wrappers -/

/-- Phase-invariant version of the lifted axis-swap input: if the inverse lifted
axis swap fixes the state up to a unit-modulus phase, then axes 3 and 2 have
equal squared single-site expectations. -/
theorem singleSiteSpinSquareExpectationS_axis3_eq_axis2_of_axisSwapPhaseInvariant
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ} (c : ℂ)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = c • Φ)
    (hc : star c * c = 1) :
    singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ := by
  refine singleSiteSpinSquareExpectationS_eq_of_conj_phaseInvariant
    (x := x) (A := spinSOp2 N) (B := spinSOp3 N)
    (T := (axisSwapUnitarySSpinS N).tensor V)
    (Tinv := (axisSwapUnitarySSpinS N).tensorInv V) (Φ := Φ) (c := c)
    ?hTadj ?hTinvT hΦswap hc ?hconj
  · exact axisSwapUnitarySSpinS_tensor_conjTranspose V N
  · exact (axisSwapUnitarySSpinS N).tensorInv_mul_tensor (Λ := V)
  · have hconj :=
      (axisSwapUnitarySSpinS N).tensor_conj_onSiteS
        (Λ := V) x (spinSOp2 N)
    rw [(axisSwapUnitarySSpinS N).conj_spinSOp2] at hconj
    exact hconj

/-- Problem 2.5.c ground-state phase wrapper: in a one-dimensional Heisenberg
eigenspace, the z-axis rotation phase gives the axis-1/axis-2 equality and the
axis-swap phase gives the axis-3/axis-2 equality.  The normalized state then has
all three squared single-site spin expectations equal to `N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_zAxisRot_axisSwap_eigenphase
    (J : V → V → ℂ) (μ : ℂ) (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  obtain ⟨cz, hphase_z, hcz⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_manyBodySpinSRot3
      (V := V) (N := N) J μ (Real.pi / 2) huniq hΦ_ne hΦnorm hΦ
  have h12 :
      singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
    singleSiteSpinSquareExpectationS_axis1_eq_axis2_of_unitaryPhaseInvariant
      (x := x)
      (T := manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))))
      (Tinv := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
      (c := cz)
      (manyBodySpinSRot3_neg_pi_half_conjTranspose V N)
      (by
        rw [manyBodyTensorS_mul]
        simpa [spinSRot3_mul_neg] using manyBodyTensorS_one (Λ := V) (N := N))
      hphase_z hcz
      (manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2 (x := x))
  obtain ⟨cswap, hphase_swap, hcswap⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_axisSwapUnitarySSpinS_tensorInv
      (V := V) (N := N) J μ huniq hΦ_ne hΦnorm hΦ
  have h32 :
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ :=
    singleSiteSpinSquareExpectationS_axis3_eq_axis2_of_axisSwapPhaseInvariant
      (x := x) (c := cswap) hphase_swap hcswap
  have h13 :
      singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ :=
    h12.trans h32.symm
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_axes_equal_normalized
    (x := x) hΦnorm h12 h13

end LatticeSystem.Quantum
