import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# Rayleigh quotient under unitary similarity

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

For a matrix `U` with `(star v) ᵥ* U = star (U.conjTranspose.mulVec v)` (the
matrix-side adjoint identity), the Rayleigh quotient transforms as
`rayleighOnVec (U * M * Uᴴ) v = rayleighOnVec M (Uᴴ.mulVec v)`.

Combined with the spectral theorem and the variational lower bound for
diagonal matrices (PR #3944), this gives the variational principle for any
Hermitian matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix-side adjoint identity for vecMul: `star v ᵥ* U = star (Uᴴ *ᵥ v)`. -/
theorem star_vecMul (U : Matrix n n ℂ) (v : n → ℂ) :
    star v ᵥ* U = star (U.conjTranspose.mulVec v) := by
  funext i
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, RCLike.star_def,
             star_sum, star_mul', Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [star_star]
  ring

/-- `rayleighOnVec` under unitary similarity: for any matrix `U`,
`rayleighOnVec (U * M * Uᴴ) v = rayleighOnVec M (Uᴴ.mulVec v)`. -/
theorem rayleighOnVec_unitary_conj (U M : Matrix n n ℂ) (v : n → ℂ) :
    rayleighOnVec (U * M * U.conjTranspose) v =
      rayleighOnVec M (U.conjTranspose.mulVec v) := by
  unfold rayleighOnVec
  -- (U * M * U†) *ᵥ v = U *ᵥ (M *ᵥ (U† *ᵥ v))
  rw [show (U * M * U.conjTranspose).mulVec v =
        U.mulVec (M.mulVec (U.conjTranspose.mulVec v)) from by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
  -- star v ⬝ᵥ (U *ᵥ w) = (star v ᵥ* U) ⬝ᵥ w = star (Uᴴ *ᵥ v) ⬝ᵥ w
  rw [dotProduct_mulVec]
  rw [star_vecMul]

/-- For unitary `U` (with `Uᴴ * U = 1`), unit-normalisation is preserved by `Uᴴ`:
`dotProduct (star (Uᴴ.mulVec v)) (Uᴴ.mulVec v) = dotProduct (star v) v`. -/
theorem dotProduct_star_conjTranspose_mulVec_self
    {U : Matrix n n ℂ} (hU : U * U.conjTranspose = 1) (v : n → ℂ) :
    dotProduct (star (U.conjTranspose.mulVec v)) (U.conjTranspose.mulVec v) =
      dotProduct (star v) v := by
  -- star (Uᴴ v) ⬝ᵥ (Uᴴ v) = (Uᴴ v) ᵥ* Uᴴ ⬝ᵥ ... hmm. Use star_vecMul trick.
  -- star (Uᴴ *ᵥ v) = star v ᵥ* U (from star_vecMul U v applied carefully... wait,
  -- the original star_vecMul gives star v ᵥ* U = star (Uᴴ *ᵥ v),
  -- so reverse: star (Uᴴ *ᵥ v) = star v ᵥ* U).
  rw [← star_vecMul]
  -- Now goal: (star v ᵥ* U) ⬝ᵥ (Uᴴ *ᵥ v) = star v ⬝ᵥ v
  -- Use vecMul_dotProduct + mulVec_mulVec: (v ᵥ* U) ⬝ᵥ (Uᴴ *ᵥ v) = v ᵥ* U ⬝ᵥ Uᴴ *ᵥ v
  -- = ? Need to relate to (U * Uᴴ).
  rw [show (star v ᵥ* U) ⬝ᵥ U.conjTranspose.mulVec v =
        star v ⬝ᵥ (U * U.conjTranspose).mulVec v from by
        rw [← Matrix.mulVec_mulVec, ← dotProduct_mulVec]]
  rw [hU, Matrix.one_mulVec]

end LatticeSystem.Quantum
