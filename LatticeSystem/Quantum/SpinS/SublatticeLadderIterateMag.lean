import LatticeSystem.Quantum.SpinS.SublatticeLadderIterate
import LatticeSystem.Quantum.SpinS.SublatticeMagShift
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Sublattice magnetization of the sublattice ladder iterates

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `k`-th sublattice ladder iterate `(Ŝ_A^-)^k · |σ_⊤⟩` lies in the sublattice
magnetization subspace at `s_A − k`: the all-up state has `Ŝ_A^(3)`-eigenvalue
`s_A`, and each `Ŝ_A^-` lowers the sublattice magnetization by one
(`SublatticeMagShift`).  Since distinct `k` give distinct sublattice
magnetizations, the iterates are linearly independent (once non-vanishing is
established) — the dimension-counting input for the A-symmetric subspace.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

omit [DecidableEq Λ] in
/-- The all-up state has sublattice `Ŝ_A^(3)`-eigenvalue `s_A = |A|·N/2`. -/
theorem sublatticeMagEigenvalueS_allUp (A : Λ → Bool) :
    sublatticeMagEigenvalueS A (allAlignedConfigS Λ N (0 : Fin (N + 1))) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 := by
  rw [sublatticeMagEigenvalueS_def]
  have h : ∀ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
      ((N : ℂ) / 2 - ((allAlignedConfigS Λ N (0 : Fin (N + 1)) x).val : ℂ)) = (N : ℂ) / 2 := by
    intro x _
    simp [allAlignedConfigS]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Sublattice magnetization of the `k`-th ladder iterate**:
`(Ŝ_A^-)^k · |σ_⊤⟩ ∈ sublatticeMagSubspaceS A (s_A − k)`. -/
theorem sublatticeLadderIterateDownS_mem_sublatticeMagSubspaceS (A : Λ → Bool) (k : ℕ) :
    sublatticeLadderIterateDownS A N k ∈
      sublatticeMagSubspaceS A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (k : ℂ)) := by
  induction k with
  | zero =>
    simp only [sublatticeLadderIterateDownS, pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero]
    have h := basisVecS_mem_sublatticeMagSubspaceS A (allAlignedConfigS Λ N (0 : Fin (N + 1)))
    rw [sublatticeMagEigenvalueS_allUp A] at h
    simpa [allAlignedStateS] using h
  | succ k ih =>
    have hstep := sublatticeSpinSOpMinus_mulVec_mem_sublatticeMagSubspaceS_of_mem A ih
    have hval : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2
          - (k : ℂ)) - 1 =
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2
          - ((k + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [hval] at hstep
    have hiter : sublatticeLadderIterateDownS A N (k + 1) =
        (sublatticeSpinSOpMinus N A).mulVec (sublatticeLadderIterateDownS A N k) := by
      simp only [sublatticeLadderIterateDownS, pow_succ']
      rw [Matrix.mulVec_mulVec]
    rw [hiter]
    exact hstep

end LatticeSystem.Quantum
