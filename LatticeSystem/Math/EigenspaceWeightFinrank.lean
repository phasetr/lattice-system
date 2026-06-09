import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension bound from a weight (eigenspace) decomposition

If a finite-dimensional submodule `G` decomposes as the supremum of its intersections with the
eigenspaces of an operator `T` at finitely many distinct eigenvalues `wt : Fin n → 𝕜`, and each such
weight block is at most one-dimensional, then `finrank G ≤ n`.  Distinct eigenspaces are
independent,
so the blocks form an internal direct sum of `G`, whence `finrank G = ∑ finrank(block) ≤ n` (sum
of `n` ones).

This is the generic linear-algebra core of the spin-multiplet degeneracy upper bounds (e.g. the
`Ŝ^z`-weight decomposition of a ground subspace).
-/

namespace LatticeSystem.Math

open Module

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Weight-block dimension bound.**  A finite-dimensional submodule that is the supremum of its
one-dimensional intersections with the eigenspaces of `T` at `n` distinct eigenvalues has dimension
at most `n`. -/
theorem finrank_le_of_weight_blocks {n : ℕ} (G : Submodule 𝕜 V) (T : Module.End 𝕜 V)
    (wt : Fin n → 𝕜) (hwt : Function.Injective wt)
    (hsup : ⨆ a, G ⊓ T.eigenspace (wt a) = G)
    (hle1 : ∀ a, finrank 𝕜 ↥(G ⊓ T.eigenspace (wt a)) ≤ 1) :
    finrank 𝕜 ↥G ≤ n := by
  set B : Fin n → Submodule 𝕜 V := fun a => G ⊓ T.eigenspace (wt a) with hB
  have hindep : iSupIndep B :=
    ((Module.End.eigenspaces_iSupIndep T).comp hwt).mono (fun a => inf_le_right)
  have hinj : Function.Injective (DirectSum.coeLinearMap B) := hindep.dfinsupp_lsum_injective
  have hrange : LinearMap.range (DirectSum.coeLinearMap B) = G := by
    rw [DirectSum.range_coeLinearMap]; exact hsup
  have hfr : finrank 𝕜 ↥G = ∑ a, finrank 𝕜 ↥(B a) := by
    rw [← hrange, ← (LinearEquiv.ofInjective (DirectSum.coeLinearMap B) hinj).finrank_eq,
      Module.finrank_directSum]
  rw [hfr]
  calc ∑ a, finrank 𝕜 ↥(B a) ≤ ∑ _a : Fin n, 1 := Finset.sum_le_sum (fun a _ => hle1 a)
    _ = n := by simp

end LatticeSystem.Math
