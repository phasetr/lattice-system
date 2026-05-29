import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness

/-!
# Tasaki §2.5 Theorem 2.4 SU(2) base case (`λ=1, D=0`)

(PR #3897, Issue #3739): at the SU(2) point `λ=1, D=0`, the anisotropic Hamiltonian
reduces to the isotropic Heisenberg Hamiltonian (`anisotropicHeisenbergS_one_zero`),
so every eigenspace coincides with that of the isotropic model. This is the entry
point for the deformation argument from the SU(2) point toward Theorem 2.4 obligation
(2) uniqueness.

The first lemma `anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS`
gives the direct eigenspace identification. The second specializes PR #3896 to the
SU(2) point: GS uniqueness at `(1, 0)` (which the deformation argument will provide
for the symmetric `|A|=|¬A|` case) implies `Ŝ³_tot|Φ⟩=0` for any non-zero GS of the
isotropic Heisenberg Hamiltonian (since at `(1, 0)` anisotropic = isotropic).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **At the SU(2) point `(λ=1, D=0)` the anisotropic and isotropic Heisenberg eigenspaces
coincide**. -/
theorem anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
    (J : Λ → Λ → ℂ) (μ : ℂ) :
    End.eigenspace (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J 1 0 N)) μ =
      End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) μ := by
  congr 2
  exact anisotropicHeisenbergS_one_zero J N

/-- **At the SU(2) point with GS uniqueness assumption, the GS has zero `Ŝ³_tot`
magnetization**. Specialization of PR #3896 to `(λ=1, D=0)` via the reduction
`anisotropicHeisenbergS J 1 0 N = heisenbergHamiltonianS J N`.

For the symmetric `|A|=|¬A|` case, the uniqueness hypothesis is what the deformation
argument from the SU(2) point establishes (the second obligation of Tasaki §2.5
Theorem 2.4; separate forthcoming work). With this specialisation, once uniqueness is
established for the SU(2) point of the isotropic Heisenberg Hamiltonian, the
`Ŝ³_tot|Φ⟩=0` conclusion is immediate.

Refers to the isotropic Heisenberg Hamiltonian directly so downstream uses don't
need to thread through the anisotropic ↦ isotropic reduction. -/
theorem heisenbergHamiltonianS_unique_groundState_has_zero_magnetization
    (J : Λ → Λ → ℂ) (μ : ℂ)
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  refine anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    J 1 0 μ ?_ hΦ_ne ?_
  · rw [anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS]
    exact huniq
  · rw [anisotropicHeisenbergS_one_zero]
    exact hΦ

end LatticeSystem.Quantum
