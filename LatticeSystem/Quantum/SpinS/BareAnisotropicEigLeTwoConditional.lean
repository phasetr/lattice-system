import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySpinHalf
import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.BareAxisSwapFullEigInterParityLeOne
import LatticeSystem.Quantum.SpinS.ParityDegeneracyBound

/-!
# Bare anisotropic Hamiltonian `Ĥ` eigenspace `finrank ℂ ≤ 2` (conditional)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(g.5): wraps the conditional `bare Ĥ' eig ≤ 2 from per-block ≤ 1` (via
`axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one`, #3776 family)
with the axis-swap unitary equivalence (`anisotropic_axisSwapped_eigenspace_finrank_eq`,
#3756) to give the same conditional bound for the bare anisotropic Hamiltonian `Ĥ`.

The conditional hypotheses (per-parity-block intersection finrank ≤ 1 at the same μ)
are not yet discharged unconditionally for general spin-S; they ARE discharged for
each parity sector's PF eigenvalue ν_p separately by (g.4) #3836, but the per-sector
ν_p may differ, so the unconditional ≤ 2 still awaits a ν-sector matching argument
(equality of the two PF ground-state energies, deferrable to subsequent work).

The spin-1/2 instance is established via `axisSwapUnitarySpinHalf`; for general S, the
caller must provide an `AxisSwapUnitaryS N` instance.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare anisotropic `Ĥ` eigenspace `finrank ℂ ≤ 2` (conditional, general N with an
`AxisSwapUnitaryS` instance)**: given per-parity-block bounds on the axis-swapped `Ĥ'` at
`μ`, the bare anisotropic `Ĥ` at `μ` also has eigenspace `finrank ℂ ≤ 2`.

Combines:
- `axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one`
  (#3776 family): bare `Ĥ'` eig ≤ 2 from per-block ≤ 1.
- `AxisSwapUnitaryS.anisotropic_axisSwapped_eigenspace_finrank_eq` (#3756): bare `Ĥ`
  and `Ĥ'` eigenspaces have equal finrank under the axis-swap unitary `G`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    (G : AxisSwapUnitaryS N)
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (heven : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) ≤ 1)
    (hodd : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2 := by
  rw [← G.anisotropic_axisSwapped_eigenspace_finrank_eq J lam D μ]
  exact axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    hJself lam D μ heven hodd

/-- **Spin-1/2 instance**: the conditional bare anisotropic `Ĥ` eigenspace `≤ 2` for `N = 1`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (heven : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D 1)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ 1)) 1) ≤ 1)
    (hodd : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D 1)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ 1)) (-1)) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D 1)) μ) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    axisSwapUnitarySpinHalf hJself lam D μ heven hodd

end LatticeSystem.Quantum
