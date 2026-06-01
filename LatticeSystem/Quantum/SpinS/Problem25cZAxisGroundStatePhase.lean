import LatticeSystem.Quantum.SpinS.Problem25cEigenspacePhaseBridge
import LatticeSystem.Quantum.SpinS.Problem25cPhaseInvariantAxisInput
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation

/-!
# Tasaki Problem 2.5.c: z-axis ground-state phase input

This module combines the abstract one-dimensional eigenspace phase bridge with
the concrete lifted z-axis rotation commutation theorem.  A normalized non-zero
eigenvector in a `finrank ≤ 1` Heisenberg eigenspace is fixed up to a
unit-modulus phase by the lifted z-axis rotation.  This supplies the state-side
phase input for the Problem 2.5.c z-axis rotation wrapper.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Lifted z-axis rotation unitarity -/

omit [DecidableEq V] in
/-- The adjoint of the lifted z-axis rotation is the lifted inverse rotation. -/
theorem manyBodySpinSRot3_conjTranspose (θ : ℝ) :
    (manyBodyTensorS (fun _ : V => spinSRot3 N θ)).conjTranspose =
      manyBodyTensorS (fun _ : V => spinSRot3 N (-θ)) := by
  simpa [spinSRot3_adjoint] using
    (manyBodyTensorS_conjTranspose (V := V) (N := N)
      (fun _ : V => spinSRot3 N θ))

/-- The lifted z-axis rotation is unitary in the form `Uᴴ * U = 1`. -/
theorem manyBodySpinSRot3_conjTranspose_mul_self (θ : ℝ) :
    (manyBodyTensorS (fun _ : V => spinSRot3 N θ)).conjTranspose *
        manyBodyTensorS (fun _ : V => spinSRot3 N θ) = 1 := by
  rw [manyBodySpinSRot3_conjTranspose, manyBodyTensorS_mul]
  simpa [spinSRot3_neg_mul] using manyBodyTensorS_one (Λ := V) (N := N)

/-! ## Heisenberg eigenspace phase input -/

/-- A normalized non-zero vector in a one-dimensional Heisenberg eigenspace is
fixed up to a unit-modulus phase by the lifted z-axis rotation. -/
theorem exists_phase_unit_of_heisenbergHamiltonianS_manyBodySpinSRot3
    (J : V → V → ℂ) (μ : ℂ) (θ : ℝ) {Φ : (V → Fin (N + 1)) → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ) :
    ∃ c : ℂ,
      (manyBodyTensorS (fun _ : V => spinSRot3 N θ)).mulVec Φ = c • Φ ∧
        star c * c = 1 :=
  exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute
    huniq hΦ_ne hΦnorm hΦ
    (heisenbergHamiltonianS_commute_manyBodySpinSRot3 (N := N) J θ).eq
    (manyBodySpinSRot3_conjTranspose_mul_self (V := V) (N := N) θ)

/-- Problem 2.5.c z-axis ground-state phase wrapper: if the Heisenberg
eigenspace is one-dimensional and the state is fixed by the lifted axis-swap
inverse, then the lifted z-axis rotation phase input supplies the remaining
axis-1/axis-2 equality for the squared single-site spin expectations. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_zAxisRot_eigenphase
    (J : V → V → ℂ) (μ : ℂ) (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 := by
  obtain ⟨c, hphase, hc⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_manyBodySpinSRot3
      (N := N) J μ (Real.pi / 2) huniq hΦ_ne hΦnorm hΦ
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_zAxisRot_phase
    (x := x) (c := c) hΦnorm hΦswap hphase hc

end LatticeSystem.Quantum
