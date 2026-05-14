import Mathlib.LinearAlgebra.Eigenspace.Basic
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# `(Ŝ_tot)²` eigenspace at ANY eigenvalue is `su(2)`-invariant

Generalises PR #2813 from the max-Casimir eigenvalue to any
eigenvalue α: for any α ∈ ℂ, the `(Ŝ_tot)²`-eigenspace at α is
closed under all `su(2)` generators (Cartesian + ladders),
because each commutes with `(Ŝ_tot)²`.

The general helper
`totalSpinSSquaredEigenspace_invariant_of_commute_at` is the
A-, J-, α-independent eigenspace-invariance lemma: any operator
commuting with `(Ŝ_tot)²` preserves every
`(Ŝ_tot)²`-eigenspace.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- General helper: any operator commuting with `(Ŝ_tot)²`
preserves every `(Ŝ_tot)²`-eigenspace, for any eigenvalue α. -/
theorem totalSpinSSquaredEigenspace_invariant_of_commute_at
    {T : Matrix _ _ ℂ}
    (hT : Commute (totalSpinSSquared V N) T) (α : ℂ) :
    Submodule.map T.mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α := by
  rintro w ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hv
  rw [Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [show (totalSpinSSquared V N).mulVec (T.mulVec v) =
        T.mulVec ((totalSpinSSquared V N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT.symm.eq]]
  rw [hv, Matrix.mulVec_smul]

set_option linter.style.longLine false in
/-- (Ŝ_tot)² eigenspace at any α closed under Ŝ^(1)_tot. -/
theorem totalSpinSSquaredEigenspace_totalSpinSOp1_invariant_at
    (α : ℂ) :
    Submodule.map (totalSpinSOp1 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α :=
  totalSpinSSquaredEigenspace_invariant_of_commute_at
    (totalSpinSSquared_commute_totalSpinSOp1 (V := V) (N := N)) α

set_option linter.style.longLine false in
/-- (Ŝ_tot)² eigenspace at any α closed under Ŝ^(2)_tot. -/
theorem totalSpinSSquaredEigenspace_totalSpinSOp2_invariant_at
    (α : ℂ) :
    Submodule.map (totalSpinSOp2 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α :=
  totalSpinSSquaredEigenspace_invariant_of_commute_at
    (totalSpinSSquared_commute_totalSpinSOp2 (V := V) (N := N)) α

set_option linter.style.longLine false in
/-- (Ŝ_tot)² eigenspace at any α closed under Ŝ^(3)_tot. -/
theorem totalSpinSSquaredEigenspace_totalSpinSOp3_invariant_at
    (α : ℂ) :
    Submodule.map (totalSpinSOp3 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α :=
  totalSpinSSquaredEigenspace_invariant_of_commute_at
    (totalSpinSSquared_commute_totalSpinSOp3 (Λ := V) (N := N)) α

set_option linter.style.longLine false in
/-- (Ŝ_tot)² eigenspace at any α closed under Ŝ^+_tot. -/
theorem totalSpinSSquaredEigenspace_totalSpinSOpPlus_invariant_at
    (α : ℂ) :
    Submodule.map (totalSpinSOpPlus V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α :=
  totalSpinSSquaredEigenspace_invariant_of_commute_at
    (totalSpinSSquared_commute_totalSpinSOpPlus (V := V) (N := N)) α

set_option linter.style.longLine false in
/-- (Ŝ_tot)² eigenspace at any α closed under Ŝ^-_tot. -/
theorem totalSpinSSquaredEigenspace_totalSpinSOpMinus_invariant_at
    (α : ℂ) :
    Submodule.map (totalSpinSOpMinus V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin α :=
  totalSpinSSquaredEigenspace_invariant_of_commute_at
    (totalSpinSSquared_commute_totalSpinSOpMinus (V := V) (N := N)) α

end LatticeSystem.Quantum
