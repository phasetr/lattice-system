import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# A commuting matrix preserves every eigenspace

If `A` commutes with `B`, then `A` maps each `B`-eigenspace into itself: from `B x = e x` and
`A B = B A` one gets `B (A x) = A (B x) = e (A x)`.  This is the elementary invariance fact behind
every "a symmetry operator preserves the energy/charge sector" argument.

Both carriers of the finite-dimensional matrix action are provided:

* `mulVec_mem_eigenspace_of_commute` — the plain function carrier `n → ℂ` acting by
  `Matrix.mulVecLin`;
* `toEuclideanLin_mem_eigenspace_of_commute` — the inner-product carrier `EuclideanSpace ℂ n`
  acting by `Matrix.toEuclideanLin`.

The second carries no separate computation: `WithLp.ofLp` intertwines the two actions
definitionally, so it is a transport of the first.
-/

namespace LatticeSystem.Math

open Matrix

/-- If `A` commutes with `B` then `A` maps each `B`-eigenspace into itself: from `B x = e x` and
`A B = B A` one gets `B (A x) = e (A x)`. -/
theorem mulVec_mem_eigenspace_of_commute {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (hAB : Commute A B) {e : ℂ} {x : n → ℂ}
    (hx : x ∈ Module.End.eigenspace B.mulVecLin e) :
    A.mulVec x ∈ Module.End.eigenspace B.mulVecLin e := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hx ⊢
  rw [Matrix.mulVec_mulVec, ← hAB.eq, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

/-- `EuclideanSpace` form of `mulVec_mem_eigenspace_of_commute`: if `A` commutes with `B` then `A`
maps every `B`-eigenspace of `EuclideanSpace ℂ n` into itself.  `WithLp.ofLp` turns the
`Matrix.toEuclideanLin` action into the `Matrix.mulVec` action definitionally, so this only
transports the function-carrier statement. -/
theorem toEuclideanLin_mem_eigenspace_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hAB : Commute A B) {e : ℂ} {v : EuclideanSpace ℂ n}
    (hv : v ∈ Module.End.eigenspace (Matrix.toEuclideanLin B) e) :
    Matrix.toEuclideanLin A v ∈ Module.End.eigenspace (Matrix.toEuclideanLin B) e := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hv' : WithLp.ofLp v ∈ Module.End.eigenspace B.mulVecLin e := by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    simpa using congrArg WithLp.ofLp hv
  have h := Module.End.mem_eigenspace_iff.mp (mulVec_mem_eigenspace_of_commute (A := A) hAB hv')
  rw [Matrix.mulVecLin_apply] at h
  apply WithLp.ofLp_injective (p := 2) (V := n → ℂ)
  change B.mulVec (A.mulVec (WithLp.ofLp v)) = e • A.mulVec (WithLp.ofLp v)
  exact h

end LatticeSystem.Math
