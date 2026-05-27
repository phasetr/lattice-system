import LatticeSystem.Math.PerronFrobeniusSimple
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Perron–Frobenius: the Perron eigenvalue eigenspace is at most one-dimensional

Building on `eigenvec_proportional_of_pos_eigenvec` (geometric simplicity): for an irreducible
non-negative matrix `A` with a strictly positive eigenvector at `μ`, the `μ`-eigenspace of
`Matrix.toLin' A` has `finrank ≤ 1` (it is contained in the span of the Perron vector).
-/

namespace LatticeSystem.Math.PerronFrobenius

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Perron eigenspace is at most one-dimensional.** If `A` is irreducible and has a strictly
positive eigenvector `v` at `μ`, then `finrank ℝ (eigenspace (toLin' A) μ) ≤ 1`. -/
theorem eigenspace_finrank_le_one_of_pos_eigenvec [Nonempty n]
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible)
    {μ : ℝ} {v : n → ℝ} (hv : A *ᵥ v = μ • v) (hv_pos : ∀ i, 0 < v i) :
    finrank ℝ (End.eigenspace (Matrix.toLin' A) μ) ≤ 1 := by
  have hsub : End.eigenspace (Matrix.toLin' A) μ ≤ Submodule.span ℝ {v} := by
    intro u hu
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply] at hu
    obtain ⟨s, hs⟩ := eigenvec_proportional_of_pos_eigenvec hIrred hv hv_pos hu
    rw [hs]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self v)
  calc finrank ℝ (End.eigenspace (Matrix.toLin' A) μ)
      ≤ finrank ℝ ↥(Submodule.span ℝ {v}) := Submodule.finrank_mono hsub
    _ ≤ ({v} : Set (n → ℝ)).toFinset.card := finrank_span_le_card {v}
    _ = 1 := by simp

end LatticeSystem.Math.PerronFrobenius
