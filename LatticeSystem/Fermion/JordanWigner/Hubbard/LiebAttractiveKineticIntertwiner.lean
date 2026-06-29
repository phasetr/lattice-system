import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticConj
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticReal

/-!
# The kinetic intertwiner `blockWCoeff (Ĥ_kin ψ) = A·W + W·Aᴴ` (Tasaki §10.2.4)

Layer PR36a of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet`. To show the Hamiltonian commutes with
the Γ-reflection `Θ` (so `Θ` preserves the ground eigenspace), we compute how `Ĥ` acts
in the `W`-coordinate `W := blockWCoeff ψ = hubbardBlockCoeff (Uᴴψ) · P`.

This file handles the **kinetic** part `Ĥ_kin = hubbardKinetic`. Conjugating to block
order (`Uᴴ·Ĥ_kin·U = hubbardBlockKinetic`, PR16) and applying the block kinetic
coefficient action `C ↦ A·C + C·Bᵣ` (with `Bᵣ = P·Aᴴ·P`, PR15/PR22), the `·P` reindex
collapses the gauge:

  `blockWCoeff (Ĥ_kin ψ) = A·W + W·Aᴴ`,

`A = hubbardBlockKineticUpFixedMatrix T`. This is manifestly equivariant under
`W ↦ Wᴴ` (`(A·W + W·Aᴴ)ᴴ = A·Wᴴ + Wᴴ·Aᴴ`), the kinetic half of the commutation.

## Main results

* `blockWCoeff_hubbardKinetic_mulVec` — `blockWCoeff (hubbardKinetic T ψ) = A·W + W·Aᴴ`
  for entrywise-real `T`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **The kinetic intertwiner.** For entrywise-real hopping `T`, the reconciliation
coefficient of `Ĥ_kin ψ` is `A·W + W·Aᴴ` with `W := blockWCoeff ψ` and
`A := hubbardBlockKineticUpFixedMatrix T`. -/
theorem blockWCoeff_hubbardKinetic_mulVec (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (hTreal : ∀ i j, star (T i j) = T i j)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N ((hubbardKinetic N T).mulVec ψ)
      = hubbardBlockKineticUpFixedMatrix N T * blockWCoeff N ψ
        + blockWCoeff N ψ * (hubbardBlockKineticUpFixedMatrix N T)ᴴ := by
  -- Step 1: back-rotate the kinetic operator to block order.
  have hconj : (hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec
        ((hubbardKinetic N T).mulVec ψ)
      = (hubbardBlockKinetic N T).mulVec
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hubbardBlockKinetic_conj_eq T]
    congr 1
    rw [hubbardBlockToSpinfulPermutationOperator, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      permutationOperator_conjTranspose_mul, Matrix.one_mul]
  -- Step 2: block coefficient action, then collapse the `·P` gauge.
  rw [blockWCoeff, hconj, hubbardBlockCoeff_hubbardBlockKinetic_mulVec,
    hubbardBlockKineticCoeffAction,
    hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose N hTreal,
    Matrix.add_mul]
  congr 1
  · rw [blockWCoeff, Matrix.mul_assoc]
  · rw [blockWCoeff, show hubbardBlockCoeff N
        ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)
        * (particleHoleConfigPermMatrix N * (hubbardBlockKineticUpFixedMatrix N T)ᴴ
            * particleHoleConfigPermMatrix N) * particleHoleConfigPermMatrix N
      = hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)
        * particleHoleConfigPermMatrix N * (hubbardBlockKineticUpFixedMatrix N T)ᴴ
        * (particleHoleConfigPermMatrix N * particleHoleConfigPermMatrix N) from by
      simp only [Matrix.mul_assoc], particleHoleConfigPermMatrix_mul_self, Matrix.mul_one]

end LatticeSystem.Fermion
