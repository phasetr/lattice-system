import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticReal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticW
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionW
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePHConjDiag
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveEnergyMonotone

/-!
# The full energy reconciliation `⟨ψ|Ĥ|ψ⟩ = liebSRPEnergy A D (U/2) W` (Tasaki §10.2.4)

Thirty-third layer (PR33d) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**. This is the assembly
that ties the whole reconciliation together.

Combining the energy decomposition (PR26, `attractiveHubbardHamiltonian_dotProduct_eq_block`)
with the kinetic identity (PR33a), the interaction trace form (PR27), the
particle-hole conjugation facts (PR33c), and the interaction identity (PR33b), the
half-filled attractive-Hubbard energy of a state `ψ` whose block coefficient matrix
gives a **Hermitian** `W := C·P` is exactly the abstract Lieb energy functional on `W`:

  `⟨ψ|Ĥ|ψ⟩ = 2·tr(W²·A) − Σ_x U_x·tr(W·D_x·W·D_x)`,
  `Re⟨ψ|Ĥ|ψ⟩ = liebSRPEnergy A D (U/2) W`,

with `A = hubbardBlockKineticUpFixedMatrix T`, `D_x = hubbardUpOccupationDiag x`,
`C = hubbardBlockCoeff (Uᴴψ)`, `P = particleHoleConfigPermMatrix`, `W = C·P`.

The Hermiticity hypothesis `(C·P).IsHermitian` is **not** automatic for a general `ψ`
— in Lieb's argument the trial states are parametrized by a Hermitian `W` (the `Γ(W)`
ansatz). This layer therefore states the reconciliation conditionally on that
hypothesis; a later layer identifies the ground energy with a Hermitian-`W` state and
then invokes `liebSRPEnergy_abs_le` to replace `W` by its positive-semidefinite
spectral absolute value `|W|`.

## Main results

* `attractiveHubbardHamiltonian_energy_eq_liebSRP_trace_of_blockW_isHermitian` — the
  `ℂ`-valued trace identity `⟨ψ|Ĥ|ψ⟩ = 2·tr(W²·A) − Σ_x U_x·tr(W·D_x·W·D_x)`.
* `attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian` — the
  real-part consumer `Re⟨ψ|Ĥ|ψ⟩ = liebSRPEnergy A D (U/2) W`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.39), pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **The full attractive-Hubbard energy as a Lieb trace functional on `W = C·P`**
(`ℂ`-valued form), conditional on the block coefficient giving a Hermitian `W`.
For a symmetric hopping matrix `T` and a state `ψ` whose block coefficient matrix
`C = hubbardBlockCoeff (Uᴴψ)` satisfies `(C·P).IsHermitian`,

  `⟨ψ|Ĥ|ψ⟩ = 2·tr(W·W·A) − Σ_x U_x·tr(W·D_x·W·D_x)`,

where `A = hubbardBlockKineticUpFixedMatrix T`, `D_x = hubbardUpOccupationDiag x`,
`W = C·P`. -/
theorem attractiveHubbardHamiltonian_energy_eq_liebSRP_trace_of_blockW_isHermitian
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hW : ((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
            * particleHoleConfigPermMatrix N).IsHermitian) :
    dotProduct (star ψ) ((attractiveHubbardHamiltonian N T U).mulVec ψ)
      = 2 * Matrix.trace
            (((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
                * particleHoleConfigPermMatrix N)
              * ((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
                  * particleHoleConfigPermMatrix N)
              * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
        - ∑ x : Fin (N + 1), (U x : ℂ) * Matrix.trace
            (((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
                * particleHoleConfigPermMatrix N)
              * hubbardUpOccupationDiag N x
              * ((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
                  * particleHoleConfigPermMatrix N)
              * hubbardUpOccupationDiag N x) := by
  set C := hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)
    with hCdef
  set P := particleHoleConfigPermMatrix N with hPdef
  set A := hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) with hAdef
  -- The complexified hopping is entrywise real and (with `hT`) symmetric-Hermitian.
  have hTreal : ∀ i j, star ((T i j : ℂ)) = (T i j : ℂ) := fun i j => by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  have hTherm : ∀ i j, star ((T i j : ℂ)) = (T j i : ℂ) := fun i j => by
    rw [hTreal i j]; exact_mod_cast hT i j
  have hA : A.IsHermitian := hubbardBlockKineticUpFixedMatrix_isHermitian N hTherm
  have hP : P.IsHermitian := particleHoleConfigPermMatrix_isHermitian
  have hPinv : P * P = 1 := particleHoleConfigPermMatrix_mul_self
  -- Kinetic term collapses via PR33a.
  have hkin : Matrix.trace (Cᴴ * hubbardBlockKineticCoeffAction N (fun x y => (T x y : ℂ)) C)
      = 2 * Matrix.trace (C * P * (C * P) * A) := by
    simp only [hubbardBlockKineticCoeffAction]
    rw [← hAdef, hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose N hTreal,
      ← hAdef, ← hPdef]
    exact trace_conj_kinetic_eq_two_trace_W_sq A C P hA hP hPinv hW
  -- Interaction term collapses via PR27 (trace form), PR33c (E = P D P), PR33b.
  have hint : (∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
        ((∑ x : Fin (N + 1), -U x * ((u x).val : ℝ) * (1 - ((h x).val : ℝ)) : ℝ) : ℂ) *
          (Complex.normSq (C u h) : ℂ))
      = -∑ x : Fin (N + 1), (U x : ℂ) * Matrix.trace
          (C * P * hubbardUpOccupationDiag N x * (C * P) * hubbardUpOccupationDiag N x) := by
    rw [attractiveInteraction_normSq_sum_eq_trace_form, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hubbardHoleOccupationDiag_eq_permConj, ← hPdef,
      show Cᴴ * (hubbardUpOccupationDiag N x * C * (P * hubbardUpOccupationDiag N x * P))
        = Cᴴ * hubbardUpOccupationDiag N x * C * (P * hubbardUpOccupationDiag N x * P) from by
        simp only [Matrix.mul_assoc],
      trace_conj_interaction_eq_trace_W C P (hubbardUpOccupationDiag N x) hP hPinv hW,
      neg_mul]
  rw [attractiveHubbardHamiltonian_dotProduct_eq_block, hkin, hint, sub_eq_add_neg]

/-- **The full attractive-Hubbard energy real part equals the abstract Lieb energy
functional** on `W = C·P`, conditional on `(C·P).IsHermitian`:

  `Re⟨ψ|Ĥ|ψ⟩ = liebSRPEnergy A D (fun x => U x / 2) W`.

This is the consumer that feeds `liebSRPEnergy_abs_le`. -/
theorem attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hW : ((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
            * particleHoleConfigPermMatrix N).IsHermitian) :
    (dotProduct (star ψ) ((attractiveHubbardHamiltonian N T U).mulVec ψ)).re
      = liebSRPEnergy (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
          (fun x => hubbardUpOccupationDiag N x) (fun x => U x / 2)
          ((hubbardBlockCoeff N ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))
            * particleHoleConfigPermMatrix N) := by
  rw [attractiveHubbardHamiltonian_energy_eq_liebSRP_trace_of_blockW_isHermitian T U hT ψ hW,
    liebSRPEnergy]
  rw [Complex.sub_re, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_ofNat, Complex.im_ofNat]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by ring)

end LatticeSystem.Fermion
