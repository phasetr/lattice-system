import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingRayleighBridge

/-!
# Tasaki 11.5: lifting compressed eigenvectors back to `W`-eigenvectors (Prop 11.24 PR-E2 ≥)

An eigenvector of the compression `compress(A) = Tᴴ A T` lifts, when `A` preserves the filling space
`W`, to an eigenvector of `A` itself on `W`:
`compress(A) Φ = E Φ ⟹ A (tJFillingExpansion Φ) = E (tJFillingExpansion Φ)`
(`mulVec_tJFillingExpansion_of_compress_eigen`).  The proof uses that the lifted vector lies in `W`
and that `T Tᴴ` acts as the identity there (the projection identity).

This is the bridge that turns the filling-index eigenstate produced by the matrix Theorem A.17 into
a genuine `Ĥ_tJ`/`Ŝ³`-eigenstate inside `W`, the final input to `groundEnergyAtFilling = μ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A filling expansion lies in the filling space `W` (a sum of `W`-members). -/
theorem tJFillingExpansion_mem_tJFillingWSubmodule (Ne : ℕ) (Φ : TJFillingSector N Ne → ℂ) :
    tJFillingExpansion N Ne Φ ∈ tJFillingWSubmodule N Ne := by
  unfold tJFillingExpansion
  exact Submodule.sum_mem _
    (fun s _ => Submodule.smul_mem _ _ (basisVec_tJConfigOf_mem_tJFillingWSubmodule Ne s))

/-- **Eigenvector lift.** If `A` preserves `W` and `Φ` is an eigenvector of the compression
`compress(A)` at `E`, then the lift `tJFillingExpansion Φ` is an eigenvector of `A` at `E`. -/
theorem mulVec_tJFillingExpansion_of_compress_eigen (Ne : ℕ)
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : PreservesTJFillingW N Ne A)
    {Φ : TJFillingSector N Ne → ℂ} {E : ℂ}
    (hE : (tJFillingCompress N Ne A).mulVec Φ = E • Φ) :
    A.mulVec (tJFillingExpansion N Ne Φ) = E • tJFillingExpansion N Ne Φ := by
  have hAW := hA _ (tJFillingExpansion_mem_tJFillingWSubmodule Ne Φ)
  have hinner : (tJFillingEmbedding N Ne)ᴴ.mulVec
      (A.mulVec ((tJFillingEmbedding N Ne).mulVec Φ)) = (tJFillingCompress N Ne A).mulVec Φ := by
    unfold tJFillingCompress
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← tJFillingProjection_mulVec_eq_of_mem Ne hAW, ← tJFillingEmbedding_mulVec,
    ← Matrix.mulVec_mulVec, hinner, hE, Matrix.mulVec_smul]

end LatticeSystem.Fermion
