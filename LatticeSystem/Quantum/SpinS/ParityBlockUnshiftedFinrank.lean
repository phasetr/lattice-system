import LatticeSystem.Math.PerronFrobeniusFinrank

/-!
# Eigenspace shift correspondence (`c • 1 − M` ↔ `M`)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Generic linear-algebra helpers for the (f) eigenspace bridge: the `μ`-eigenspace of the shifted
matrix `c • 1 − M` equals the `c − μ`-eigenspace of `M`, hence their finite-dimensional
dimensions match.

These are reusable Mathlib-style lemmas — applied first to the parity-block PF setting of
Tasaki §2.5 Theorem 2.4 (where #3825's Perron `finrank ≤ 1` bound for the shifted parity-block
matrix transfers to the un-shifted real-form parity-block matrix), and later to the analogous
sector / Hamiltonian eigenspace bridges in the obligation (1) finishing arc.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Module Matrix

/-- **Generic shift correspondence**: the `μ`-eigenspace of `c • 1 − M` equals the
`c − μ`-eigenspace of `M`.  Pure linear algebra over ℝ. -/
theorem eigenspace_smul_one_sub_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (c μ : ℝ) :
    End.eigenspace (Matrix.toLin' (c • (1 : Matrix n n ℝ) - M)) μ =
      End.eigenspace (Matrix.toLin' M) (c - μ) := by
  ext v
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    rw [sub_smul, ← h]
    abel
  · intro h
    rw [h, sub_smul]
    abel

/-- **Generic shift `finrank` correspondence**: the `μ`-eigenspace of `c • 1 − M` and the
`c − μ`-eigenspace of `M` have equal `ℝ`-dimensions. -/
theorem eigenspace_smul_one_sub_finrank_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (c μ : ℝ) :
    finrank ℝ (End.eigenspace (Matrix.toLin' (c • (1 : Matrix n n ℝ) - M)) μ) =
      finrank ℝ (End.eigenspace (Matrix.toLin' M) (c - μ)) := by
  rw [eigenspace_smul_one_sub_eq]

end LatticeSystem.Quantum
