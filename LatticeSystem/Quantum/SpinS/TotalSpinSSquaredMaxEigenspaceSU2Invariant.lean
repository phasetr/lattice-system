import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Maximum-Casimir `(Ŝ_tot)²` eigenspace is `su(2)`-invariant

The `(Ŝ_tot)²`-eigenspace at the maximum Casimir eigenvalue is
closed under all three Cartesian total-spin generators
`Ŝ^(1)_tot`, `Ŝ^(2)_tot`, `Ŝ^(3)_tot` and the two ladder
operators `Ŝ^+_tot`, `Ŝ^-_tot`. Each follows from the commutation
of the corresponding operator with `(Ŝ_tot)²`.

This is the A-independent, J-independent version of the predicted
GS subspace `su(2)`-invariances (PRs #2798-#2800), specialised to
the maximum-Casimir eigenspace itself.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- General lemma: for any operator `T` commuting with
`totalSpinSSquared V N`, the `(Ŝ_tot)²`-eigenspace at any
eigenvalue is `T`-invariant. -/
private theorem totalSpinSSquaredEigenspace_invariant_of_commute
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
/-- Max-Casimir `(Ŝ_tot)²` eigenspace closed under `Ŝ^(1)_tot`. -/
theorem totalSpinSSquaredEigenspace_max_totalSpinSOp1_invariant
    [Nonempty V] :
    Submodule.map (totalSpinSOp1 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
  totalSpinSSquaredEigenspace_invariant_of_commute
    (totalSpinSSquared_commute_totalSpinSOp1 (V := V) (N := N)) _

set_option linter.style.longLine false in
/-- Max-Casimir `(Ŝ_tot)²` eigenspace closed under `Ŝ^(2)_tot`. -/
theorem totalSpinSSquaredEigenspace_max_totalSpinSOp2_invariant
    [Nonempty V] :
    Submodule.map (totalSpinSOp2 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
  totalSpinSSquaredEigenspace_invariant_of_commute
    (totalSpinSSquared_commute_totalSpinSOp2 (V := V) (N := N)) _

set_option linter.style.longLine false in
/-- Max-Casimir `(Ŝ_tot)²` eigenspace closed under `Ŝ^(3)_tot`. -/
theorem totalSpinSSquaredEigenspace_max_totalSpinSOp3_invariant
    [Nonempty V] :
    Submodule.map (totalSpinSOp3 V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
  totalSpinSSquaredEigenspace_invariant_of_commute
    (totalSpinSSquared_commute_totalSpinSOp3 (Λ := V) (N := N)) _

set_option linter.style.longLine false in
/-- Max-Casimir `(Ŝ_tot)²` eigenspace closed under `Ŝ^+_tot`. -/
theorem totalSpinSSquaredEigenspace_max_totalSpinSOpPlus_invariant
    [Nonempty V] :
    Submodule.map (totalSpinSOpPlus V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
  totalSpinSSquaredEigenspace_invariant_of_commute
    (totalSpinSSquared_commute_totalSpinSOpPlus (V := V) (N := N)) _

set_option linter.style.longLine false in
/-- Max-Casimir `(Ŝ_tot)²` eigenspace closed under `Ŝ^-_tot`. -/
theorem totalSpinSSquaredEigenspace_max_totalSpinSOpMinus_invariant
    [Nonempty V] :
    Submodule.map (totalSpinSOpMinus V N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
  totalSpinSSquaredEigenspace_invariant_of_commute
    (totalSpinSSquared_commute_totalSpinSOpMinus (V := V) (N := N)) _

end LatticeSystem.Quantum
