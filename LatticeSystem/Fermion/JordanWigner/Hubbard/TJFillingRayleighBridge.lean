import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingCompress
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity

/-!
# Tasaki 11.5: the filling embedding is an isometry, and the Rayleigh bridge (Prop 11.24 PR-E2 ≥)

The orthonormal filling embedding `T` satisfies `Tᴴ T = 1`
(`tJFillingEmbedding_conjTranspose_mul_self`),
so it is an isometry: `⟨T c, T c⟩ = ⟨c, c⟩`.  Consequently the operator Rayleigh quotient of `Ĥ_tJ`
on a lifted filling vector equals the matrix Rayleigh quotient of the compression `Ĥ_W`:
`rayleighOnVec Ĥ_tJ (tJFillingExpansion c) = rayleighOnVec (tJFillingCompress Ĥ_tJ) c`
(`rayleighOnVec_tJFillingCompress`).  This bridges the operator-side variational problem
(`groundEnergyAtFilling`) to the finite matrix `Ĥ_W`, whose minimum eigenvalue is then identified
with `μ` via the W-restricted A.17.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The (rectangular) adjoint identity for the matrix inner product: `⟨c, Tᴴ y⟩ = ⟨T c, y⟩`. -/
private theorem dotProduct_star_conjTranspose_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (T : Matrix m n ℂ) (c : n → ℂ) (y : m → ℂ) :
    dotProduct (star c) (Tᴴ.mulVec y) = dotProduct (star (T.mulVec c)) y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun s _ => by ring))

/-- **The filling embedding has orthonormal columns:** `Tᴴ T = 1`. -/
theorem tJFillingEmbedding_conjTranspose_mul_self (Ne : ℕ) :
    (tJFillingEmbedding N Ne)ᴴ * tJFillingEmbedding N Ne = 1 := by
  ext s s'
  rw [Matrix.mul_apply]
  rw [show (∑ w, (tJFillingEmbedding N Ne)ᴴ s w * tJFillingEmbedding N Ne w s')
      = ∑ w, basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w from by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, tJFillingEmbedding, Matrix.of_apply, Matrix.of_apply,
      show star (basisVec (tJConfigOf N s.val) w) = basisVec (tJConfigOf N s.val) w from by
        rw [basisVec_apply]; split <;> simp]]
  rw [tJConfigOf_basisVec_inner, Matrix.one_apply]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg (fun hc => h (Subtype.ext hc)), if_neg h]

/-- **The filling embedding is an isometry:** `⟨T c, T c⟩ = ⟨c, c⟩`. -/
theorem tJFillingExpansion_dotProduct_self (Ne : ℕ) (c : TJFillingSector N Ne → ℂ) :
    dotProduct (star (tJFillingExpansion N Ne c)) (tJFillingExpansion N Ne c) =
      dotProduct (star c) c := by
  rw [← tJFillingEmbedding_mulVec,
    ← dotProduct_star_conjTranspose_mulVec (tJFillingEmbedding N Ne) c
      ((tJFillingEmbedding N Ne).mulVec c),
    Matrix.mulVec_mulVec, tJFillingEmbedding_conjTranspose_mul_self, Matrix.one_mulVec]

/-- **The Rayleigh bridge.** The operator Rayleigh quotient of `A` on a lifted filling vector equals
the matrix Rayleigh quotient of its compression `Ĥ_W = Tᴴ A T`:
`rayleighOnVec A (T c) = rayleighOnVec (compress A) c`. -/
theorem rayleighOnVec_tJFillingCompress (Ne : ℕ) (A : ManyBodyOp (Fin (2 * N + 2)))
    (c : TJFillingSector N Ne → ℂ) :
    rayleighOnVec (tJFillingCompress N Ne A) c =
      rayleighOnVec A (tJFillingExpansion N Ne c) := by
  have hmv : (tJFillingCompress N Ne A).mulVec c
      = (tJFillingEmbedding N Ne)ᴴ.mulVec (A.mulVec ((tJFillingEmbedding N Ne).mulVec c)) := by
    unfold tJFillingCompress
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have key : dotProduct (star c) ((tJFillingCompress N Ne A).mulVec c)
      = dotProduct (star (tJFillingExpansion N Ne c)) (A.mulVec (tJFillingExpansion N Ne c)) := by
    rw [hmv, dotProduct_star_conjTranspose_mulVec, tJFillingEmbedding_mulVec]
  unfold rayleighOnVec
  rw [key]

end LatticeSystem.Fermion
