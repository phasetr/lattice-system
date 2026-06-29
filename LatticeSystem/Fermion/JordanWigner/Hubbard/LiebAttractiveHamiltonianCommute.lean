import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticIntertwiner
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionIntertwiner

/-!
# The Hamiltonian commutes with the Γ-reflection `Ĥ ∘ Θ = Θ ∘ Ĥ` (Tasaki §10.2.4)

Layer PR36c of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet`. Assembling the kinetic (PR36a) and
interaction (PR36b) intertwiners into the full `W`-coordinate action of `Ĥ`,

  `blockWCoeff (Ĥ ψ) = A·W + W·Aᴴ + Σ_x (−U_x)·D_x·W·D_x =: G(W)`,

we observe `G` is equivariant under conjugate transpose, `G(Wᴴ) = (G W)ᴴ`
(`A·Wᴴ + Wᴴ·Aᴴ` is symmetric under `W ↦ Wᴴ`; the interaction term needs `D_x`
Hermitian and `U` real). Since the Γ-reflection `Θ` acts as `W ↦ Wᴴ` in the (injective)
`W`-coordinate (`blockWCoeff (Θ ψ) = (blockWCoeff ψ)ᴴ`, PR35), this yields

  `Ĥ (Θ ψ) = Θ (Ĥ ψ)`.

So `Θ` commutes with `Ĥ`; in particular `Θ` preserves every eigenspace of `Ĥ`. This is
the key input for producing a Hermitian-`W` ground-state representative (PR37).

## Main results

* `blockWCoeff_add` — `blockWCoeff` is additive.
* `blockWCoeff_attractiveHubbardHamiltonian_mulVec` — the full intertwiner
  `blockWCoeff (Ĥψ) = G(W)`.
* `attractiveHubbardHamiltonian_gammaThetaVec_commute` — `Ĥ (Θ ψ) = Θ (Ĥ ψ)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- `blockWCoeff` is additive (it is `hubbardBlockCoeff (Uᴴ·) · P`, a composition of
linear maps). -/
theorem blockWCoeff_add (ψ φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N (ψ + φ) = blockWCoeff N ψ + blockWCoeff N φ := by
  rw [blockWCoeff, blockWCoeff, blockWCoeff, Matrix.mulVec_add, hubbardBlockCoeff_add,
    Matrix.add_mul]

/-- **The full intertwiner.** The reconciliation coefficient of `Ĥ ψ` is
`G(W) = A·W + W·Aᴴ + Σ_x (−U_x)·D_x·W·D_x`, `W := blockWCoeff ψ`,
`A := hubbardBlockKineticUpFixedMatrix (T : ℂ)`, `D_x := hubbardUpOccupationDiag x`. -/
theorem blockWCoeff_attractiveHubbardHamiltonian_mulVec
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N ((attractiveHubbardHamiltonian N T U).mulVec ψ)
      = hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * blockWCoeff N ψ
        + blockWCoeff N ψ * (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))ᴴ
        + ∑ x : Fin (N + 1), (-(U x : ℂ)) •
            (hubbardUpOccupationDiag N x * blockWCoeff N ψ * hubbardUpOccupationDiag N x) := by
  have hTreal : ∀ i j, star ((T i j : ℂ)) = (T i j : ℂ) := fun i j => by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  rw [attractiveHubbardHamiltonian, Matrix.add_mulVec, blockWCoeff_add,
    blockWCoeff_hubbardKinetic_mulVec _ hTreal, blockWCoeff_attractiveHubbardInteraction_mulVec]

/-- **The Hamiltonian commutes with the Γ-reflection:** `Ĥ (Θ ψ) = Θ (Ĥ ψ)`.
Hence `Θ` preserves every eigenspace of `Ĥ`. -/
theorem attractiveHubbardHamiltonian_gammaThetaVec_commute
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (attractiveHubbardHamiltonian N T U).mulVec (gammaThetaVec N ψ)
      = gammaThetaVec N ((attractiveHubbardHamiltonian N T U).mulVec ψ) := by
  apply blockWCoeff_injective
  rw [blockWCoeff_attractiveHubbardHamiltonian_mulVec, blockWCoeff_gammaThetaVec,
    blockWCoeff_gammaThetaVec, blockWCoeff_attractiveHubbardHamiltonian_mulVec]
  -- goal: `G(Wᴴ) = (G W)ᴴ`.
  set W := blockWCoeff N ψ
  set A := hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ))
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    show (∑ x : Fin (N + 1), (-(U x : ℂ)) •
        (hubbardUpOccupationDiag N x * W * hubbardUpOccupationDiag N x))ᴴ
      = ∑ x : Fin (N + 1), (-(U x : ℂ)) •
          (hubbardUpOccupationDiag N x * Wᴴ * hubbardUpOccupationDiag N x) from by
      rw [Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        star_neg, ← starRingEnd_apply, Complex.conj_ofReal, ← Matrix.mul_assoc]
      simp only [(hubbardUpOccupationDiag_isHermitian x).eq]]
  abel

end LatticeSystem.Fermion
