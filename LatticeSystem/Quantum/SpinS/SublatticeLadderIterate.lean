import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceLadderInvariant

/-!
# Sublattice ladder iterates of the all-up state

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `k`-th sublattice ladder iterate `(Ŝ_A^-)^k · |σ_⊤⟩` of the all-up state lies
in the maximal `(Ŝ_A)²`-eigenspace (the A-symmetric subspace), since `(Ŝ_A)²`
commutes with every power of `Ŝ_A^-` and `|σ_⊤⟩` realizes the maximal Casimir.
These iterates (one per `A`-magnetization) are the spanning family of the
A-symmetric subspace, the sublattice analogue of `ladderIterateUp`
(§2.4 `SaturatedFullLadderLI`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The `k`-th sublattice ladder iterate of the all-up state:
`(Ŝ_A^-)^k · |σ_⊤⟩`. -/
noncomputable def sublatticeLadderIterateDownS (A : Λ → Bool) (N : ℕ) (k : ℕ) :
    (Λ → Fin (N + 1)) → ℂ :=
  ((sublatticeSpinSOpMinus N A) ^ k).mulVec (allAlignedStateS Λ N (0 : Fin (N + 1)))

/-- **Each sublattice ladder iterate lies in the maximal `(Ŝ_A)²`-eigenspace**:
`(Ŝ_A)² · (Ŝ_A^-)^k |σ_⊤⟩ = s_A(s_A+1) · (Ŝ_A^-)^k |σ_⊤⟩`. -/
theorem sublatticeSpinSquaredS_mulVec_sublatticeLadderIterateDownS (A : Λ → Bool) (k : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec (sublatticeLadderIterateDownS A N k) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) •
        sublatticeLadderIterateDownS A N k := by
  unfold sublatticeLadderIterateDownS
  rw [Matrix.mulVec_mulVec,
      ((sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus (Λ := Λ) (N := N) A).pow_right k).eq,
      ← Matrix.mulVec_mulVec,
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (N := N) A,
      Matrix.mulVec_smul]

end LatticeSystem.Quantum
