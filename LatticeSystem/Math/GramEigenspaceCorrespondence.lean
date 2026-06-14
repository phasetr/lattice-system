import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Complex.Basic

/-!
# Nonzero-eigenvalue correspondence between `Sᴴ S` and `S Sᴴ`

For any complex matrix `S`, the Gram matrices `Sᴴ S` and `S Sᴴ` have the **same positive
eigenvalues with the same multiplicities**: for every `λ ≠ 0` the `λ`-eigenspaces of `Sᴴ S` and
`S Sᴴ` have equal (finite) dimension.  The map `φ ↦ S φ` carries the `λ`-eigenspace of `Sᴴ S`
injectively into that of `S Sᴴ` (for `λ ≠ 0`, since `S φ = 0 ⟹ Sᴴ S φ = 0 = λ φ ⟹ φ = 0`), and
applying the same fact to `Sᴴ` (whose conjugate transpose is `S`) gives the reverse inequality.

This is the linear-algebra content of **Tasaki Lemma 11.14** (§11.3.3, the hopping matrices
`T = SᴴS` and `T̃ = SSᴴ` having exactly identical positive eigenvalues with identical
multiplicities); it is a general singular-value/SVD fact, so it lives here under a topic name
rather than a textbook one.

Reference for the application: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.3, Lemma 11.14, p. 406.
-/

namespace LatticeSystem.Math

open Matrix Module

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- For `λ ≠ 0`, the map `φ ↦ S φ` embeds the `λ`-eigenspace of `Sᴴ S` into that of `S Sᴴ`, so the
former has dimension at most the latter. -/
private lemma finrank_eigenspace_gram_le (S : Matrix m n ℂ) {lam : ℂ} (hlam : lam ≠ 0) :
    finrank ℂ (End.eigenspace (Sᴴ * S).mulVecLin lam)
      ≤ finrank ℂ (End.eigenspace (S * Sᴴ).mulVecLin lam) := by
  -- `S` carries the source eigenspace into the target eigenspace
  have hmaps : ∀ φ ∈ End.eigenspace (Sᴴ * S).mulVecLin lam,
      S.mulVecLin φ ∈ End.eigenspace (S * Sᴴ).mulVecLin lam := by
    intro φ hφ
    rw [End.mem_eigenspace_iff] at hφ ⊢
    have key : (S * Sᴴ).mulVecLin (S.mulVecLin φ)
        = S.mulVecLin ((Sᴴ * S).mulVecLin φ) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [key, hφ, map_smul]
  refine LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.restrict S.mulVecLin hmaps) ?_
  intro x y hxy
  have hS : S.mulVec x.1 = S.mulVec y.1 := by
    have h := Subtype.ext_iff.mp hxy
    simpa only [LinearMap.restrict_apply, Matrix.mulVecLin_apply] using h
  have hsub := Submodule.sub_mem _ x.2 y.2
  rw [End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hsub
  have hS0 : S.mulVec (x.1 - y.1) = 0 := by rw [Matrix.mulVec_sub, hS, sub_self]
  have h0 : (Sᴴ * S).mulVec (x.1 - y.1) = 0 := by
    rw [← Matrix.mulVec_mulVec, hS0, Matrix.mulVec_zero]
  have hzero : lam • (x.1 - y.1) = 0 := hsub.symm.trans h0
  apply Subtype.ext
  rcases smul_eq_zero.mp hzero with h | h
  · exact absurd h hlam
  · exact sub_eq_zero.mp h

/-- **Tasaki Lemma 11.14 (positive-eigenvalue correspondence of `Sᴴ S` and `S Sᴴ`).**  For any
complex matrix `S` and any `λ ≠ 0`, the `λ`-eigenspaces of `Sᴴ S` and `S Sᴴ` have equal dimension —
so the two Gram matrices share their positive eigenvalues with identical multiplicities.  Proved by
the injection `φ ↦ S φ` and its mirror `ψ ↦ Sᴴ ψ` (applied to `S` and to `Sᴴ`). -/
theorem finrank_eigenspace_gram_eq (S : Matrix m n ℂ) {lam : ℂ} (hlam : lam ≠ 0) :
    finrank ℂ (End.eigenspace (Sᴴ * S).mulVecLin lam)
      = finrank ℂ (End.eigenspace (S * Sᴴ).mulVecLin lam) := by
  refine le_antisymm (finrank_eigenspace_gram_le S hlam) ?_
  have h := finrank_eigenspace_gram_le Sᴴ hlam
  rwa [Matrix.conjTranspose_conjTranspose] at h

end LatticeSystem.Math
