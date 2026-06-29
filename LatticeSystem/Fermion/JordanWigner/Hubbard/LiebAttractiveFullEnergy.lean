import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInterleavedEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffNormSq

/-!
# The full attractive-Hubbard energy functional (Tasaki §10.2.1)

Twenty-sixth layer (PR26) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

Assembling the kinetic energy (PR23, a trace on the block coefficient matrix
`C' = hubbardBlockCoeff (Uᴴψ)`) and the interaction energy (PR24, a diagonal `normSq`
sum on the spin-reflection coefficient matrix `spinReflectionCoeff ψ`), and bridging
the two coordinate systems via the equal-magnitude relation (PR25), the energy of the
attractive Hubbard Hamiltonian is expressed entirely on the block coefficient matrix:

  `⟨ψ| Ĥ |ψ⟩ = tr(C'ᴴ·(A·C' + C'·Bᵣ)) + Σ_{u,h} (Σ_x −U_x·u_x·(1−h_x))·|C'_{u,h}|²`.

This is the energy functional whose minimization by the spin-reflection variational
argument (a later layer: matrix polar replacement `C ↦ |C| = (CᴴC)^{1/2}`, the Lieb
trace inequality, Perron–Frobenius uniqueness, and the spin-flip singlet) discharges
Lieb's theorem.

## Main results

* `attractiveHubbardHamiltonian_dotProduct_eq_block` — the full energy as a trace
  plus a diagonal `normSq` sum, both on the block coefficient matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Complex
open scoped BigOperators

variable {N : ℕ}

/-- **The full attractive-Hubbard energy functional on the block coefficient
matrix.** The energy of `Ĥ = Ĥkin + Ĥint` in a state `ψ` is the sum of the kinetic
trace (PR23) and the attractive interaction's diagonal `normSq` sum (PR24), both
transported onto the block coefficient matrix `C' = hubbardBlockCoeff (Uᴴψ)` via the
equal-magnitude bridge (PR25). -/
theorem attractiveHubbardHamiltonian_dotProduct_eq_block (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) ((attractiveHubbardHamiltonian N T U).mulVec ψ)
      = Matrix.trace
          ((hubbardBlockCoeff N
              ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ))ᴴ *
            hubbardBlockKineticCoeffAction N (fun x y => (T x y : ℂ))
              (hubbardBlockCoeff N
                ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)))
        + ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
            ((∑ x : Fin (N + 1), -U x * ((u x).val : ℝ) * (1 - ((h x).val : ℝ)) : ℝ) : ℂ) *
              (Complex.normSq (hubbardBlockCoeff N
                ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) u h) : ℂ) := by
  rw [attractiveHubbardHamiltonian, Matrix.add_mulVec, dotProduct_add,
    hubbardKinetic_dotProduct_eq_block_trace_of_interleaved,
    attractiveHubbardInteraction_dotProduct_eq_spinReflectionCoeff_normSq]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun h _ => ?_))
  rw [spinReflectionCoeff_normSq_eq_hubbardBlockCoeff]

end LatticeSystem.Fermion
