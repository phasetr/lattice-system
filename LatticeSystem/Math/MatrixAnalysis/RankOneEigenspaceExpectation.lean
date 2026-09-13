import LatticeSystem.Math.MatrixAnalysis.UniqueEigenspaceInvolution

/-!
# Expectation values on an eigenspace of rank at most one

If a matrix `H` has a `μ`-eigenspace of `finrank ≤ 1` then all of its `μ`-eigenvectors are
proportional, so the expectation value `⟨Φ, O Φ⟩` of an arbitrary operator `O` is the same for
every one of them once the vector is normalised.  This is the bridge that turns a statement
proved for **one** explicitly constructed ground state into a statement about **every**
normalised ground state.

The identity is stated in the cleared form `⟨Ψ, Ψ⟩ · ⟨Φ, O Φ⟩ = ⟨Ψ, O Ψ⟩` rather than as a
quotient, so that the comparison vector `Ψ` need not be normalised: only `Φ` is.  Callers that
hold a non-normalised reference eigenvector (a Perron–Frobenius vector, say) can therefore use
it directly, and recover the expectation of any normalised eigenvector by dividing by the
positive real number `⟨Ψ, Ψ⟩`.
-/

namespace LatticeSystem.Math

open Matrix Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Expectation values agree across a `finrank ≤ 1` eigenspace.**  Let `Φ` be a non-zero
normalised `μ`-eigenvector of `H` whose `μ`-eigenspace has `finrank ≤ 1`, and let `Ψ` be any
`μ`-eigenvector of `H` (neither normalised nor assumed non-zero).  Then `Ψ = c • Φ` for a
scalar `c`, so `⟨Ψ, Ψ⟩` and `⟨Ψ, O Ψ⟩` both carry the same factor `star c * c`, and the
normalisation `⟨Φ, Φ⟩ = 1` turns that common factor into the stated identity. -/
theorem dotProduct_star_mulVec_eq_of_finrank_eigenspace_le_one
    {H O : Matrix ι ι ℂ} {μ : ℂ} {Φ Ψ : ι → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦeig : H.mulVec Φ = μ • Φ)
    (hΨeig : H.mulVec Ψ = μ • Ψ) :
    (star Ψ ⬝ᵥ Ψ) * (star Φ ⬝ᵥ O.mulVec Φ) = star Ψ ⬝ᵥ O.mulVec Ψ := by
  have hΦ_in : Φ ∈ End.eigenspace (Matrix.toLin' H) μ := by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦeig
  have hΨ_in : Ψ ∈ End.eigenspace (Matrix.toLin' H) μ := by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΨeig
  obtain ⟨c, hc⟩ := exists_smul_of_mem_finrank_le_one huniq hΦ_in hΦ_ne hΨ_in
  have hstar : star (c • Φ) = star c • star Φ := by
    funext i
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul]
    exact star_mul' c (Φ i)
  have hself : star Ψ ⬝ᵥ Ψ = (star c * c) * (star Φ ⬝ᵥ Φ) := by
    rw [hc, hstar, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hop : star Ψ ⬝ᵥ O.mulVec Ψ = (star c * c) * (star Φ ⬝ᵥ O.mulVec Φ) := by
    rw [hc, hstar, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hself, hop, hΦnorm, mul_one]

end LatticeSystem.Math
