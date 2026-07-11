import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Existence of a pseudoinverse potential for a Hermitian matrix

Generic finite-dimensional linear algebra for Tasaki §4.1 Theorem 4.2 (the susceptibility sum rule,
issue #4777): if `v` is orthogonal to the kernel of a Hermitian (in particular positive
semidefinite) matrix `A`, then `v` lies in the range of `A`, and there is a preimage `y` (`A y = v`)
that is itself orthogonal to `ker A` — the Moore–Penrose pseudoinverse image `y = A⁺ v`.

The proof is the finite-dimensional Hilbert-space identity `range A = (ker A)ᗮ` for self-adjoint `A`
(`LinearMap.orthogonal_ker` together with `A† = A`), followed by an orthogonal projection of any
preimage onto `(ker A)ᗮ` to secure `y ⊥ ker A`.  This is the *forward* direction `(ker A)ᗮ ⊆
range A`; the reverse inclusion `range A ⊆ (ker A)ᗮ` already lives elsewhere
(`eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero`), so this is a distinct statement.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020, §4.1,
eq. (4.1.39), book p. 84 (second-order perturbation / resolvent identity).
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

/-- **Existence of an orthogonal pseudoinverse potential.**  For a positive-semidefinite (hence
Hermitian) matrix `A`, if `v ⊥ ker A` (every kernel vector `u` has `⟪u, v⟫ = star u ⬝ᵥ v = 0`), then
there is `y` with `A y = v` and `y ⊥ ker A`.  Since `range A = (ker A)ᗮ` for self-adjoint `A`, `v`
lies in `range A`; projecting a preimage onto `(ker A)ᗮ` keeps the image while enforcing
`y ⊥ ker A`. -/
theorem hermitian_posSemidef_exists_orthogonal_potential {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (v : n → ℂ)
    (hker : ∀ u, A.mulVec u = 0 → star u ⬝ᵥ v = 0) :
    ∃ y, A.mulVec y = v ∧ (∀ u, A.mulVec u = 0 → star u ⬝ᵥ y = 0) := by
  classical
  have hAH : A.IsHermitian := hA.1
  set f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin A with hf
  -- `A` is self-adjoint as an operator on `EuclideanSpace`.
  have hadj : LinearMap.adjoint f = f := by
    rw [hf, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hAH.eq]
  -- `(ker A)ᗮ = range A` for the self-adjoint operator.
  have hko : (LinearMap.ker f)ᗮ = LinearMap.range f := by
    rw [LinearMap.orthogonal_ker, hadj]
  -- `ṽ = v` embedded in `EuclideanSpace` is orthogonal to `ker A`, hence lies in `range A`.
  have hv_mem : (WithLp.toLp 2 v : EuclideanSpace ℂ n) ∈ (LinearMap.ker f)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hAu : A.mulVec (WithLp.ofLp u) = 0 := by
      have h1 : WithLp.ofLp (f u) = A.mulVec (WithLp.ofLp u) := rfl
      rw [hu] at h1; simpa using h1.symm
    have hz := hker (WithLp.ofLp u) hAu
    rw [show u = WithLp.toLp 2 (WithLp.ofLp u) from rfl, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
    exact hz
  rw [hko] at hv_mem
  obtain ⟨y0, hy0⟩ := hv_mem
  -- Project a preimage onto `(ker A)ᗮ` to get `y ⊥ ker A` while keeping `A y = v`.
  have hp_mem : (LinearMap.ker f).starProjection y0 ∈ LinearMap.ker f := by
    rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _
  have hy_perp : y0 - (LinearMap.ker f).starProjection y0 ∈ (LinearMap.ker f)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal y0
  set yv : EuclideanSpace ℂ n := y0 - (LinearMap.ker f).starProjection y0 with hyvdef
  have hfy : f yv = WithLp.toLp 2 v := by
    have hfp : f ((LinearMap.ker f).starProjection y0) = 0 := LinearMap.mem_ker.mp hp_mem
    rw [hyvdef, map_sub, hfp, sub_zero, hy0]
  refine ⟨WithLp.ofLp yv, ?_, ?_⟩
  · -- `A (ofLp yv) = v`.
    have h2 : WithLp.ofLp (f yv) = A.mulVec (WithLp.ofLp yv) := rfl
    rw [hfy] at h2; simpa using h2.symm
  · -- `y ⊥ ker A`.
    intro u hAu
    have hu_mem : (WithLp.toLp 2 u : EuclideanSpace ℂ n) ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      apply WithLp.ofLp_injective
      have hval : WithLp.ofLp (f (WithLp.toLp 2 u)) = A.mulVec u := rfl
      rw [hval, hAu]; simp
    have hinner := Submodule.inner_right_of_mem_orthogonal hu_mem hy_perp
    rw [show yv = WithLp.toLp 2 (WithLp.ofLp yv) from rfl, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm] at hinner
    exact hinner

end LatticeSystem.Math
