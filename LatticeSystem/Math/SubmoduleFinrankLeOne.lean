import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Scalar dependence in a submodule of rank at most one

If a submodule `W` of `finrank K W ≤ 1` contains a nonzero vector `x`, then every element `y ∈ W`
is a scalar multiple of `x`.  This is the elementary linear-algebra core that promotes a
"unique-up-to-scalar" invariant subspace (e.g. a ground eigenspace of `finrank ≤ 1`) into a genuine
eigenvector statement for any specific nonzero vector it contains: if a linear operator maps `x`
into such a `W`, the image is forced to be a scalar multiple of `x`.
-/

namespace LatticeSystem.Math

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **Scalar dependence in a `finrank ≤ 1` submodule.** If `W` has `finrank K W ≤ 1`, then any
`y ∈ W` is a scalar multiple of any nonzero `x ∈ W`.  (Both vectors are dependent because `W` is at
most a line.) -/
theorem exists_smul_of_mem_of_finrank_le_one {W : Submodule K V}
    [Module.Free K W] [Module.Finite K W] (hW : Module.finrank K W ≤ 1)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hx0 : x ≠ 0) :
    ∃ c : K, c • x = y := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hW
  obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hv ⟨y, hy⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hx0 (by simpa using ha.symm)
  refine ⟨b * a⁻¹, ?_⟩
  have hxy : (⟨y, hy⟩ : W) = (b * a⁻¹) • (⟨x, hx⟩ : W) := by
    rw [← hb, ← ha, smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  have hcoe := congrArg (Subtype.val) hxy
  simpa using hcoe.symm

end LatticeSystem.Math
