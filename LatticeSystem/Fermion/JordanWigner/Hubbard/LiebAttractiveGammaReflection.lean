import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaCoords

/-!
# The Γ-reflection `Θ` and the Hermitian-`W` ⟺ Θ-fixed criterion (Tasaki §10.2.4)

Second layer (PR35) of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model). Building on the Γ-coordinate picture (PR34), this layer defines the
**Γ-reflection** `Θ` — the state map that conjugate-transposes the coefficient matrix
`W ↦ Wᴴ` in Γ coordinates — and proves the crucial criterion

  `(blockWCoeff ψ).IsHermitian ↔ Θ ψ = ψ`,

i.e. a state has a Hermitian reconciliation coefficient `W` exactly when it is fixed
by the Γ-reflection. This is the clean, ε-bridge-free analogue of
`spinReflectionCoeff_isHermitian_iff_thetaFixed`, stated for the matrix `W = C·P` that
the energy reconciliation actually uses (the existing θ-criterion is about
`spinReflectionCoeff ψ` and the Jordan-Wigner ε-sign + particle-hole reindex obstruct
transporting it directly — see `LiebAttractiveCoeffBridge.lean`).

## Main results

* `blockWCoeff` — the reconciliation coefficient map `ψ ↦ hubbardBlockCoeff (Uᴴψ)·P`.
* `blockWCoeff_injective` — `blockWCoeff` is injective.
* `gammaThetaVec` — the Γ-reflection `Θ ψ := Γ((blockWCoeff ψ)ᴴ)`.
* `blockWCoeff_gammaThetaVec` — `blockWCoeff (Θ ψ) = (blockWCoeff ψ)ᴴ`.
* `blockWCoeff_isHermitian_iff_gammaThetaFixed` — `(blockWCoeff ψ).IsHermitian ↔ Θ ψ = ψ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The **reconciliation coefficient map** `ψ ↦ hubbardBlockCoeff (Uᴴψ)·P`, i.e. the
matrix `W` whose Lieb energy functional equals the physical energy (PR33d). -/
noncomputable def blockWCoeff (N : ℕ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)
    * particleHoleConfigPermMatrix N

/-- `blockWCoeff` is the composition of the unitary `Uᴴ` with the block-coefficient
linear isomorphism (PR34 gauge cancellation). -/
theorem blockWCoeff_eq_linearEquiv (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N ψ
      = hubbardBlockCoeffLinearEquiv N
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) :=
  hubbardBlockCoeff_mul_permMatrix _

/-- The reconciliation coefficient map is injective (composition of the injective
unitary `Uᴴ` and the injective block-coefficient isomorphism). -/
theorem blockWCoeff_injective : Function.Injective (blockWCoeff N) := by
  intro ψ φ h
  rw [blockWCoeff_eq_linearEquiv, blockWCoeff_eq_linearEquiv] at h
  have h2 := (hubbardBlockCoeffLinearEquiv N).injective h
  have h3 : (hubbardBlockToSpinfulPermutationOperator N).mulVec
      ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)
      = (hubbardBlockToSpinfulPermutationOperator N).mulVec
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec φ) := by
    rw [h2]
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hubbardBlockToSpinfulPermutationOperator_mul_conjTranspose,
    Matrix.one_mulVec, Matrix.one_mulVec] at h3

/-- The **Γ-reflection** `Θ ψ := Γ((blockWCoeff ψ)ᴴ)`: the state whose reconciliation
coefficient is the conjugate transpose of that of `ψ`. -/
noncomputable def gammaThetaVec (N : ℕ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  gammaWState N (blockWCoeff N ψ)ᴴ

/-- The Γ-reflection conjugate-transposes the reconciliation coefficient:
`blockWCoeff (Θ ψ) = (blockWCoeff ψ)ᴴ`. -/
theorem blockWCoeff_gammaThetaVec (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N (gammaThetaVec N ψ) = (blockWCoeff N ψ)ᴴ := by
  rw [gammaThetaVec, blockWCoeff]
  exact blockWCoeff_gammaWState _

/-- **The Hermitian-`W` criterion.** A state has a Hermitian reconciliation
coefficient exactly when it is fixed by the Γ-reflection:
`(blockWCoeff ψ).IsHermitian ↔ Θ ψ = ψ`. -/
theorem blockWCoeff_isHermitian_iff_gammaThetaFixed
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (blockWCoeff N ψ).IsHermitian ↔ gammaThetaVec N ψ = ψ := by
  constructor
  · intro hH
    apply blockWCoeff_injective
    rw [blockWCoeff_gammaThetaVec]
    exact hH.eq
  · intro hfix
    have h := congrArg (blockWCoeff N) hfix
    rw [blockWCoeff_gammaThetaVec] at h
    exact h

end LatticeSystem.Fermion
