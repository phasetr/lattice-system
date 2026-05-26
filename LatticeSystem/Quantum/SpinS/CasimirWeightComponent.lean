import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Weight-component extraction for total-Casimir eigenvectors

Scaffold for the total-Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Since `(Ŝ_tot)²` commutes with the magnetization projection `magProjFn`, every
non-zero `(Ŝ_tot)²`-eigenvector has a non-zero magnetization-weight component
that is again a `(Ŝ_tot)²`-eigenvector at the same eigenvalue and lives in a
single magnetization subspace.  This reduces the Casimir spectral bound to
*weight* eigenvectors, on which the highest-weight argument applies.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Weight-component extraction**: a non-zero `(Ŝ_tot)²`-eigenvector at `γ`
has a non-zero magnetization-weight component `magProjFn M v` (for some
`M = |V|·N/2 − k`) which is again a `(Ŝ_tot)²`-eigenvector at `γ` and lies in
the magnetization subspace `magSubspaceS V N M`. -/
theorem totalSpinSSquared_eigenvec_exists_weight_component
    {γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    ∃ k : Fin (Fintype.card V * N + 1),
      magProjFn (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ≠ 0 ∧
      (totalSpinSSquared V N).mulVec
          (magProjFn (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v) =
        γ • magProjFn (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ∧
      magProjFn (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v ∈
        magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) := by
  classical
  have hsum_ne :
      (∑ k : Fin (Fintype.card V * N + 1),
        magProjFn (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v) ≠ 0 := by
    rw [sum_magProjFn_eq (V := V) (N := N) v]
    exact hv
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  refine ⟨k, hk, ?_, magProjFn_mem_magSubspaceS _ v⟩
  rw [totalSpinSSquared_mulVec_magProjFn_eq, hcas, magProjFn_smul]

end LatticeSystem.Quantum
