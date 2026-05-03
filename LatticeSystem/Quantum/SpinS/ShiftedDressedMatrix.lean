import LatticeSystem.Quantum.SpinS.DressedHeisenberg

/-!
# The shifted dressed Heisenberg matrix
(Tasaki §2.5 Phase B-γ γ-3 PF prep)

For Perron–Frobenius application to the dressed Heisenberg matrix, we
need a non-negative matrix derived from `dressedHeisenbergSReMatrix`.
The natural choice is the **shifted negation**:

    `shiftedDressedSReMatrix A J N c := c • 1 - dressedHeisenbergSReMatrix A J N`

For sufficiently large `c` (specifically, `c ≥ max σ, dressedHeisenbergSReMatrix σ σ`):
- Off-diagonal entries are `≥ 0` (since `dressedHeisenbergSReMatrix ≤ 0`
  off-diagonal, by the Marshall sign trick).
- Diagonal entries are `≥ 0` (since `c ≥ dressedHeisenbergSReMatrix σ σ`).

This gives a non-negative matrix to which the standard PF irreducibility
theorem (`exists_positive_eigenvector_of_irreducible`) can be applied.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The shifted negation of the dressed Heisenberg real-matrix:

    `shiftedDressedSReMatrix A J N c := c • 1 − dressedHeisenbergSReMatrix A J N`.

For `c` large enough, this matrix is non-negative everywhere and
strictly positive on bipartite raise/lower steps — the form needed
for Perron–Frobenius irreducibility on the magnetization subspace. -/
noncomputable def shiftedDressedSReMatrix
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) :
    Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ :=
  c • 1 - dressedHeisenbergSReMatrix A J N

/-- Definitional unfolding of `shiftedDressedSReMatrix`. -/
theorem shiftedDressedSReMatrix_def
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) :
    shiftedDressedSReMatrix A J N c =
      c • 1 - dressedHeisenbergSReMatrix A J N := rfl

/-- Off-diagonal entry of the shifted dressed matrix:
`shiftedDressedSReMatrix σ' σ = -dressedHeisenbergSReMatrix σ' σ`
(for `σ' ≠ σ`, the diagonal contribution `c · 1` vanishes). -/
theorem shiftedDressedSReMatrix_apply_off_diag
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    shiftedDressedSReMatrix A J N c σ' σ =
      -dressedHeisenbergSReMatrix A J N σ' σ := by
  unfold shiftedDressedSReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- Diagonal entry of the shifted dressed matrix:
`shiftedDressedSReMatrix σ σ = c − dressedHeisenbergSReMatrix σ σ`. -/
theorem shiftedDressedSReMatrix_apply_diag
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ)
    (σ : V → Fin (N + 1)) :
    shiftedDressedSReMatrix A J N c σ σ =
      c - dressedHeisenbergSReMatrix A J N σ σ := by
  unfold shiftedDressedSReMatrix
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]

end LatticeSystem.Quantum
