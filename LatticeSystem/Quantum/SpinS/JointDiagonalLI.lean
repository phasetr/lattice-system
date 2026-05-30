import LatticeSystem.Quantum.SpinS.JointLadderIterateNonvanishing
import LatticeSystem.Quantum.SpinS.JointLadderIterateSublatticeMag

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Linear independence of the diagonal joint-ladder family

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

At the extremal total magnetization `s_A − s_B` (WLOG `|¬A| ≤ |A|`), the diagonal
family `k_A ↦ jointLadderIterateDownS A N k_A (|¬A|·N − k_A)`, `k_A = 0, …, |¬A|·N`,
is linearly independent: each member is a non-zero `Ŝ_A^(3)`-eigenvector (#3703,
#3700) at the distinct eigenvalue `s_A − k_A`, and eigenvectors at distinct
eigenvalues are linearly independent.  This `(|¬A|·N + 1)`-element family in
`W ∩ mag-(s_A−s_B)` is the source of the rank–nullity argument: `Ŝ⁺_tot` maps it
into the smaller `|¬A|·N`-element lower-index family, forcing a kernel.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The diagonal family at extremal total magnetization:
`k_A ↦ (Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{|¬A|·N − k_A} |σ_⊤⟩`. -/
noncomputable def jointDiagonalIterate (A : Λ → Bool) (N : ℕ)
    (kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1)) :
    (Λ → Fin (N + 1)) → ℂ :=
  jointLadderIterateDownS A N kA.val
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - kA.val)

/-- Each diagonal member is a non-zero `Ŝ_A^(3)`-eigenvector at `s_A − k_A`,
assuming `|¬A| ≤ |A|`. -/
theorem jointDiagonalIterate_hasEigenvector (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1)) :
    Module.End.HasEigenvector ((sublatticeSpinSOp3 N A).mulVecLin)
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (kA.val : ℂ))
      (jointDiagonalIterate A N kA) := by
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    have hmem := jointLadderIterateDownS_mem_sublatticeMagSubspaceS (N := N) A kA.val
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - kA.val)
    rw [mem_sublatticeMagSubspaceS_iff] at hmem
    exact hmem
  · -- non-vanishing: kA ≤ |¬A|·N ≤ |A|·N, and (|¬A|·N − kA) ≤ |¬A|·N.
    have hkA_le : kA.val ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N :=
      Nat.lt_succ_iff.mp kA.isLt
    have hkA_leA : kA.val ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card * N :=
      le_trans hkA_le (Nat.mul_le_mul_right N horient)
    have hkB_le : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - kA.val ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N := Nat.sub_le _ _
    exact jointLadderIterateDownS_ne_zero A hkA_leA hkB_le

omit [DecidableEq Λ] in
/-- The diagonal eigenvalue function `k_A ↦ s_A − k_A` is injective. -/
theorem jointDiagonal_eigenvalue_injective (A : Λ → Bool) :
    Function.Injective (fun kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1) =>
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (kA.val : ℂ)) := by
  intro i j hij
  simp only at hij
  have hval : (i.val : ℂ) = (j.val : ℂ) := by linear_combination -hij
  exact Fin.ext (by exact_mod_cast hval)

/-- **Linear independence of the diagonal family** (for `|¬A| ≤ |A|`). -/
theorem jointDiagonalIterate_linearIndependent (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    LinearIndependent ℂ (jointDiagonalIterate A N) := by
  apply Module.End.eigenvectors_linearIndependent' ((sublatticeSpinSOp3 N A).mulVecLin)
    (fun kA => ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (kA.val : ℂ))
    (jointDiagonal_eigenvalue_injective A)
  exact jointDiagonalIterate_hasEigenvector A horient

end LatticeSystem.Quantum
