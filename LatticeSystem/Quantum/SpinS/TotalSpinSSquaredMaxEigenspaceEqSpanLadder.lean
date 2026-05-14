import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Maximum-Casimir `(Ŝ_tot)²` eigenspace = span of ladder iterates

The `(Ŝ_tot)²`-eigenspace at the maximum eigenvalue
`saturatedFerromagnetCasimirEigenvalueS V N = m_max(m_max+1)` is
the linear span of the `(2 m_max + 1)` ladder iterates
`(Ŝ^-_tot)^k · |σ_⊤⟩`:

  `Module.End.eigenspace (Ŝ_tot)².mulVecLin
       (saturatedFerromagnetCasimirEigenvalueS V N)
     = Submodule.span ℂ (Set.range (ladderIterateUp V N))`.

This is the concrete basis identification of the maximum-Casimir
eigenspace at the operator level, independent of `A` and `J`.

Proof: PR #2801 (eigenspace = saturated FM joint at J=0) +
PR #2768 (saturated FM joint = span ladder for any J).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Max-Casimir `(Ŝ_tot)²` eigenspace = span(ladderIterateUp)**:
`Module.End.eigenspace (Ŝ_tot)².mulVecLin
(saturatedFerromagnetCasimirEigenvalueS V N) =
Submodule.span ℂ (Set.range (ladderIterateUp V N))`. -/
theorem totalSpinSSquaredEigenspace_max_eq_span_ladderIterateUp
    [Nonempty V] :
    Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) =
      Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  rw [← saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace
        (V := V) (N := N)]
  exact saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp 0

end LatticeSystem.Quantum
