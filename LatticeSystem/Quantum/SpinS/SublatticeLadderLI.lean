import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateNonvanishing

/-!
# Linear independence of the sublattice ladder family

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The sublattice ladder iterates `(Ŝ_A^-)^k · |σ_⊤⟩` for `k = 0, …, |A|·N` are
linearly independent: each is a non-zero `Ŝ_A^(3)`-eigenvector (#3694, #3692) at the
distinct eigenvalue `s_A − k`, and eigenvectors at distinct eigenvalues are linearly
independent (`Module.End.eigenvectors_linearIndependent'`).  Hence the maximal
`(Ŝ_A)²`-eigenspace (the A-symmetric subspace) has dimension at least `|A|·N + 1`.
Sublattice analogue of `ladderIterateUp_linearIndependent` (§2.4).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The `Ŝ_A^(3)`-eigenvalue `s_A − k` of the `k`-th sublattice ladder iterate. -/
noncomputable def sublatticeLadderEigenvalueDown (A : Λ → Bool) (N : ℕ)
    (k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1)) : ℂ :=
  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)

omit [DecidableEq Λ] in
/-- The sublattice eigenvalue function is injective. -/
theorem sublatticeLadderEigenvalueDown_injective (A : Λ → Bool) :
    Function.Injective (sublatticeLadderEigenvalueDown A N) := by
  intros i j hij
  unfold sublatticeLadderEigenvalueDown at hij
  have hval : (i.val : ℂ) = (j.val : ℂ) := by linear_combination -hij
  have hnat : i.val = j.val := by exact_mod_cast hval
  exact Fin.ext hnat

/-- The `k`-th sublattice ladder iterate (as a family indexed by
`Fin (|A|·N + 1)`). -/
noncomputable def sublatticeLadderIterateDownFin (A : Λ → Bool) (N : ℕ)
    (k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1)) :
    (Λ → Fin (N + 1)) → ℂ :=
  sublatticeLadderIterateDownS A N k.val

/-- Each iterate is a non-zero `Ŝ_A^(3)`-eigenvector at `s_A − k`. -/
theorem sublatticeLadderIterateDownFin_hasEigenvector (A : Λ → Bool)
    (k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1)) :
    Module.End.HasEigenvector ((sublatticeSpinSOp3 N A).mulVecLin)
      (sublatticeLadderEigenvalueDown A N k) (sublatticeLadderIterateDownFin A N k) := by
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    have hmem := sublatticeLadderIterateDownS_mem_sublatticeMagSubspaceS (N := N) A k.val
    rw [mem_sublatticeMagSubspaceS_iff] at hmem
    exact hmem
  · exact sublatticeLadderIterateDownS_ne_zero A (Nat.lt_succ_iff.mp k.isLt)

/-- **Linear independence of the sublattice ladder family**: the iterates
`(Ŝ_A^-)^k · |σ_⊤⟩` for `k = 0, …, |A|·N` are linearly independent. -/
theorem sublatticeLadderIterateDownFin_linearIndependent (A : Λ → Bool) :
    LinearIndependent ℂ (sublatticeLadderIterateDownFin A N) :=
  Module.End.eigenvectors_linearIndependent' ((sublatticeSpinSOp3 N A).mulVecLin)
    (sublatticeLadderEigenvalueDown A N) (sublatticeLadderEigenvalueDown_injective A)
    (sublatticeLadderIterateDownFin A N) (sublatticeLadderIterateDownFin_hasEigenvector A)

end LatticeSystem.Quantum
