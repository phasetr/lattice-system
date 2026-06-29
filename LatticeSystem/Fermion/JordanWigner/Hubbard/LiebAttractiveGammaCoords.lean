import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePHConjDiag
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePermutation

/-!
# Γ coordinates: the reconciliation `W` is a linear-isomorphism image of the state (Tasaki §10.2.4)

First layer (PR34) of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model). The reconciliation (PR33d) expresses the half-filled energy as the
abstract Lieb functional on `W := hubbardBlockCoeff (Uᴴψ) · P`, conditional on `W`
being Hermitian. To run Lieb's variational argument over Hermitian `W`, we first need
the **Γ-coordinate** picture: `W` is a linear-isomorphism image of the state vector,
so every matrix `W` is realized by some state (`Γ(W)`).

The key observation is a **gauge cancellation**: the particle-hole column reindex `P`
exactly undoes the particle-hole gauge baked into `hubbardBlockCoeff`, so

  `hubbardBlockCoeff ψ · P = hubbardBlockCoeffLinearEquiv ψ`

is the *plain* block coefficient linear isomorphism (no gauge twist). Composing with the
unitary block↔interleaved relabeling `U`, the reconciliation's `W` is

  `W = hubbardBlockCoeffLinearEquiv (Uᴴψ)`,

a composition of linear isomorphisms — hence surjective, with explicit inverse
`Γ(W) := U · (hubbardBlockCoeffLinearEquiv⁻¹ W)`.

## Main results

* `hubbardBlockCoeff_mul_permMatrix` — `hubbardBlockCoeff ψ · P = hubbardBlockCoeffLinearEquiv ψ`.
* `gammaWState` — the state `Γ(W) := U · (LE⁻¹ W)` realizing a given coefficient matrix.
* `blockWCoeff_gammaWState` — `hubbardBlockCoeff (Uᴴ Γ(W)) · P = W` (surjectivity).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix PEquiv
open scoped BigOperators

variable {N : ℕ}

/-- **Gauge cancellation.** The particle-hole column reindex `P` undoes the
particle-hole gauge in `hubbardBlockCoeff`, leaving the plain block coefficient
linear isomorphism: `hubbardBlockCoeff ψ · P = hubbardBlockCoeffLinearEquiv ψ`. -/
theorem hubbardBlockCoeff_mul_permMatrix (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N ψ * particleHoleConfigPermMatrix N
      = hubbardBlockCoeffLinearEquiv N ψ := by
  rw [particleHoleConfigPermMatrix, mul_toMatrix_toPEquiv]
  funext u h
  simp only [Matrix.submatrix_apply, id_eq, particleHoleConfigEquiv_symm, hubbardBlockCoeff,
    hubbardBlockCoeffLinearEquiv, LinearEquiv.coe_mk]
  rw [show (particleHoleConfig N) ((particleHoleConfigEquiv N) h) = h from by
    simp only [particleHoleConfigEquiv, Function.Involutive.coe_toPerm]
    exact particleHoleConfig_involutive N h]
  rfl

/-- The state `Γ(W) := U · (hubbardBlockCoeffLinearEquiv⁻¹ W)` realizing a given
coefficient matrix `W` in the reconciliation. -/
noncomputable def gammaWState (N : ℕ)
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  (hubbardBlockToSpinfulPermutationOperator N).mulVec
    ((hubbardBlockCoeffLinearEquiv N).symm W)

/-- **Surjectivity of the Γ coordinates.** The reconciliation's coefficient map
`ψ ↦ hubbardBlockCoeff (Uᴴψ) · P` sends `Γ(W)` back to `W`. -/
theorem blockWCoeff_gammaWState
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    hubbardBlockCoeff N
        ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec (gammaWState N W))
      * particleHoleConfigPermMatrix N = W := by
  rw [hubbardBlockCoeff_mul_permMatrix, gammaWState,
    Matrix.mulVec_mulVec, hubbardBlockToSpinfulPermutationOperator_conjTranspose_mul,
    Matrix.one_mulVec, LinearEquiv.apply_symm_apply]

end LatticeSystem.Fermion
