import Mathlib.Analysis.Matrix.PosDef

/-!
# Positivity of the trace of a product of positive-definite matrices

Generic finite-dimensional linear algebra.  For two positive-definite complex matrices `A` and
`B` (over a nonempty index type), the trace of the product is strictly positive (as a complex
number, under the `ComplexOrder` order in which `0 < z ↔ 0 < z.re ∧ z.im = 0`):
`0 < Tr(A · B)`.

The proof diagonalizes `B` by the spectral theorem (`Matrix.IsHermitian.spectral_theorem`),
`B = U · diag(λ) · Uᴴ` with `U` unitary and eigenvalues `λ_i > 0`
(`Matrix.PosDef.eigenvalues_pos`).  Cycling the trace (`Matrix.trace_mul_cycle`) gives
`Tr(A · B) = Tr((Uᴴ · A · U) · diag(λ)) = Σ_i (Uᴴ · A · U)_{ii} · λ_i`, where each diagonal
entry `(Uᴴ · A · U)_{ii}` is positive because `Uᴴ · A · U` is again positive definite
(`Matrix.PosDef.conjTranspose_mul_mul_same`, using that a unitary matrix has injective `mulVec`)
and hence has positive diagonal (`Matrix.PosDef.diag_pos`).  A sum of positive terms over a
nonempty index set is positive (`Finset.sum_pos`).

This is the generic step behind the non-orthogonality (`Tr(W'W) > 0`) argument in the
uniqueness proof of Tasaki §10.2.4 (Lieb's theorem for the attractive Hubbard model, Issue #4852).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§10.2.4, p. 372.
-/

namespace Matrix.PosDef

open Matrix
open scoped ComplexOrder

/-- **The trace of a product of two positive-definite matrices is strictly positive.**
For positive-definite complex matrices `A`, `B` over a nonempty (finite, decidable) index type,
`0 < Tr(A · B)` in the `ComplexOrder`.  The trace is real and positive: diagonalizing `B` as
`U · diag(λ) · Uᴴ` and cycling the trace expresses `Tr(A · B) = Σ_i (Uᴴ · A · U)_{ii} · λ_i`, a
sum of products of positive reals (positive diagonal of the positive-definite `Uᴴ · A · U`, times
positive eigenvalues of `B`).  Generic ingredient for the `Tr(W'W) > 0` non-orthogonality step of
Tasaki §10.2.4. -/
theorem trace_mul_pos {n : Type*} [Fintype n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    0 < (A * B).trace := by
  classical
  have hBH : B.IsHermitian := hB.isHermitian
  have hu : IsUnit (hBH.eigenvectorUnitary : Matrix n n ℂ) :=
    IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self hBH.eigenvectorUnitary)
  have hUinj : Function.Injective (hBH.eigenvectorUnitary : Matrix n n ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hu
  have hS : ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
      (hBH.eigenvectorUnitary : Matrix n n ℂ)).PosDef :=
    hA.conjTranspose_mul_mul_same hUinj
  have key : (A * B).trace
      = ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
          (hBH.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hBH.eigenvalues)).trace := by
    conv_lhs =>
      rw [hBH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  rw [key]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Function.comp_apply]
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  exact mul_pos hS.diag_pos (RCLike.ofReal_pos.mpr (hB.eigenvalues_pos i))

/-- **The trace of `A · B` is strictly positive when `A` is positive definite and `B` is a
nonzero positive-semidefinite matrix.**  For a positive-definite complex matrix `A` and a nonzero
positive-semidefinite complex matrix `B` over a (finite, decidable) index type, `0 < Tr(A · B)`
in the `ComplexOrder`.  Diagonalizing `B` as `U · diag(λ) · Uᴴ` with `λ_i ≥ 0` (and at least one
`λ_i > 0` because `B ≠ 0`) and cycling the trace gives
`Tr(A · B) = Σ_i (Uᴴ · A · U)_{ii} · λ_i`, a sum of nonnegative terms (positive diagonal of the
positive-definite `Uᴴ · A · U` times nonnegative eigenvalues of `B`) with at least one strictly
positive term.  This is the footnote-16 ingredient, extended to a positive-semidefinite second
factor, behind the pair-correlation positivity `Tr(W_GS · S · W_GS · Sᵀ) > 0` of Tasaki §10.2.4
(Theorem 10.3, 1st ed., Springer 2020, p. 372). -/
theorem trace_mul_posSemidef_pos {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosSemidef) (hB_ne : B ≠ 0) :
    0 < (A * B).trace := by
  classical
  have hBH : B.IsHermitian := hB.isHermitian
  have hu : IsUnit (hBH.eigenvectorUnitary : Matrix n n ℂ) :=
    IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self hBH.eigenvectorUnitary)
  have hUinj : Function.Injective (hBH.eigenvectorUnitary : Matrix n n ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hu
  have hS : ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
      (hBH.eigenvectorUnitary : Matrix n n ℂ)).PosDef :=
    hA.conjTranspose_mul_mul_same hUinj
  have key : (A * B).trace
      = ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
          (hBH.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hBH.eigenvalues)).trace := by
    conv_lhs =>
      rw [hBH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  have hex : ∃ i, 0 < hBH.eigenvalues i := by
    by_contra h
    push Not at h
    apply hB_ne
    have hfun : (RCLike.ofReal ∘ hBH.eigenvalues : n → ℂ) = 0 := by
      funext i
      have : hBH.eigenvalues i = 0 := le_antisymm (h i) (hB.eigenvalues_nonneg i)
      simp [Function.comp_apply, this]
    rw [hBH.spectral_theorem, hfun]
    simp
  rw [key]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Function.comp_apply]
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · exact mul_nonneg hS.diag_pos.le (RCLike.ofReal_nonneg.mpr (hB.eigenvalues_nonneg i))
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, mul_pos hS.diag_pos (RCLike.ofReal_pos.mpr hi)⟩

/-- **`Nᴴ · R · N` is nonzero whenever `R` is positive definite and `N` is nonzero.**
If `N a b ≠ 0`
then the `(b, b)` diagonal entry of `Nᴴ · R · N` is the positive-definite quadratic form of `R` on
the nonzero `b`-th column of `N`, hence strictly positive, so the matrix is nonzero.  This resolves
the nonvanishing hypothesis of `trace_mul_posSemidef_pos` for the second factor `S_cᴴ · R · S_c` in
the pair-correlation positivity of Tasaki §10.2.4 (Theorem 10.3). -/
theorem conjTranspose_mul_mul_ne_zero {n : Type*} [Fintype n]
    {R N : Matrix n n ℂ} (hR : R.PosDef) (hN : N ≠ 0) : Nᴴ * R * N ≠ 0 := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, N a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (by ext a b; exact h a b)
  have hv : (fun i => N i b) ≠ 0 := fun h => hab (congrFun h a)
  have hpos : 0 < star (fun i => N i b) ⬝ᵥ R *ᵥ (fun i => N i b) :=
    hR.dotProduct_mulVec_pos hv
  have hentry : (Nᴴ * R * N) b b = star (fun i => N i b) ⬝ᵥ R *ᵥ (fun i => N i b) := by
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
      Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hbb : (Nᴴ * R * N) b b ≠ 0 := by rw [hentry]; exact ne_of_gt hpos
  intro hzero
  rw [hzero, Matrix.zero_apply] at hbb
  exact hbb rfl

end Matrix.PosDef
