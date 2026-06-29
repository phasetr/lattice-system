import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHamiltonianCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaAntilinear

/-!
# The W-space Lyapunov equation for a Hubbard ground coefficient (Tasaki §10.2.4)

Layer PR39d toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. A
`Ĥ`-eigenvector `ψ` at eigenvalue `E`, transported through the intertwiner (PR36c) and
the linearity of `blockWCoeff`, gives the **W-space Lyapunov (Schrödinger) equation** for
its reconciliation coefficient `R := blockWCoeff ψ`:

  `A·R + R·Aᴴ − Σ_x U_x·(D_x·R·D_x) = E·R`,

`A = hubbardBlockKineticUpFixedMatrix T`, `D_x = hubbardUpOccupationDiag x`. This is
exactly the hypothesis form of the abstract ground-state kernel-propagation /
connected-support dichotomy (`posSemidef_ground_kernel_propagation`,
`posDef_or_eq_zero_of_connected_support`), feeding Tasaki Lemma 10.10.

## Main result

* `blockWCoeff_lyapunov_of_eigenvector` — the Lyapunov equation for `blockWCoeff ψ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **The W-space Lyapunov equation.** If `ψ` is a `Ĥ`-eigenvector at eigenvalue `E`,
its reconciliation coefficient `R := blockWCoeff ψ` solves
`A·R + R·Aᴴ − Σ_x U_x·(D_x·R·D_x) = E·R`. -/
theorem blockWCoeff_lyapunov_of_eigenvector
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℝ)
    (heig : (attractiveHubbardHamiltonian N T U).mulVec ψ = (E : ℂ) • ψ) :
    hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * blockWCoeff N ψ
        + blockWCoeff N ψ * (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))ᴴ
        - ∑ x : Fin (N + 1), (U x : ℂ) •
            (hubbardUpOccupationDiag N x * blockWCoeff N ψ * hubbardUpOccupationDiag N x)
      = (E : ℂ) • blockWCoeff N ψ := by
  have key := blockWCoeff_attractiveHubbardHamiltonian_mulVec T U ψ
  rw [heig, blockWCoeff_smul] at key
  rw [key, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine congrArg (_ + ·) (Finset.sum_congr rfl (fun x _ => ?_))
  rw [neg_smul]

end LatticeSystem.Fermion
