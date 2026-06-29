import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHamiltonianCommute

/-!
# The Γ-reflection is anti-linear and preserves eigenvectors (Tasaki §10.2.4)

Layer PR36d of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet`. The Γ-reflection `Θ` conjugate-transposes
the coefficient `W ↦ Wᴴ` (PR35), so it is **anti-linear** in the state:

  `Θ (c • ψ) = (conj c) • Θ ψ`,

and it is an involution (`Θ² = id`). Combined with the commutation `Ĥ ∘ Θ = Θ ∘ Ĥ`
(PR36c), anti-linearity gives **eigenvector preservation at real eigenvalues**: if
`Ĥ ψ = E·ψ` with `E ∈ ℝ`, then `Ĥ (Θ ψ) = E·(Θ ψ)`. Since ground energies are real,
`Θ` maps every ground vector to a ground vector — the input that lets PR37 build a
nonzero `Θ`-fixed (Hermitian-`W`) ground representative.

## Main results

* `blockWCoeff_smul` / `gammaWState_smul` — linearity of the coordinate maps.
* `gammaThetaVec_smul` — `Θ (c • ψ) = (conj c) • Θ ψ` (anti-linearity).
* `gammaThetaVec_gammaThetaVec` — `Θ² = id`.
* `gammaThetaVec_preserves_eigenvector` — `Ĥ ψ = E·ψ` (real `E`) ⟹ `Ĥ (Θ ψ) = E·(Θ ψ)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The block coefficient is homogeneous: `hubbardBlockCoeff (c • ψ) = c • hubbardBlockCoeff ψ`. -/
theorem hubbardBlockCoeff_smul (c : ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N (c • ψ) = c • hubbardBlockCoeff N ψ := by
  funext u h
  simp only [hubbardBlockCoeff, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]

/-- `blockWCoeff` is homogeneous: `blockWCoeff (c • ψ) = c • blockWCoeff ψ`. -/
theorem blockWCoeff_smul (c : ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N (c • ψ) = c • blockWCoeff N ψ := by
  rw [blockWCoeff, blockWCoeff, Matrix.mulVec_smul, hubbardBlockCoeff_smul, Matrix.smul_mul]

/-- `gammaWState` is homogeneous: `gammaWState (c • W) = c • gammaWState W`. -/
theorem gammaWState_smul (c : ℂ)
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    gammaWState N (c • W) = c • gammaWState N W := by
  rw [gammaWState, gammaWState, map_smul, Matrix.mulVec_smul]

/-- **Anti-linearity of the Γ-reflection:** `Θ (c • ψ) = (conj c) • Θ ψ`. -/
theorem gammaThetaVec_smul (c : ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    gammaThetaVec N (c • ψ) = (starRingEnd ℂ c) • gammaThetaVec N ψ := by
  rw [gammaThetaVec, gammaThetaVec, blockWCoeff_smul, Matrix.conjTranspose_smul,
    gammaWState_smul, starRingEnd_apply]

/-- The Γ-reflection is an involution: `Θ² = id`. -/
theorem gammaThetaVec_gammaThetaVec (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    gammaThetaVec N (gammaThetaVec N ψ) = ψ := by
  apply blockWCoeff_injective
  rw [blockWCoeff_gammaThetaVec, blockWCoeff_gammaThetaVec, Matrix.conjTranspose_conjTranspose]

/-- **The Γ-reflection preserves eigenvectors at real eigenvalues.** If `Ĥ ψ = E·ψ`
with `E ∈ ℝ`, then `Ĥ (Θ ψ) = E·(Θ ψ)`. Since ground energies are real, `Θ` maps
ground vectors to ground vectors. -/
theorem gammaThetaVec_preserves_eigenvector
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℝ)
    (hψ : (attractiveHubbardHamiltonian N T U).mulVec ψ = (E : ℂ) • ψ) :
    (attractiveHubbardHamiltonian N T U).mulVec (gammaThetaVec N ψ)
      = (E : ℂ) • gammaThetaVec N ψ := by
  rw [attractiveHubbardHamiltonian_gammaThetaVec_commute, hψ, gammaThetaVec_smul,
    Complex.conj_ofReal]

end LatticeSystem.Fermion
