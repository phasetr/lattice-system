import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisingTermination

/-!
# Tasaki 11.5: the raised sector ground state is a highest weight (Prop 11.24 E3b PR4)

Combining the raising-tower tracking (PR2) and termination (PR3): a sector ground state `Φ` with
`Ŝ³ Φ = ½ Φ`, `N̂_↓ Φ = m Φ`, `Ĥ_tJ Φ = μ Φ` produces, at the top `Ω = (Ŝ⁺_tot)^m Φ`, a
**highest-weight ground state**:

* `Ŝ⁺ Ω = 0` (termination, PR3),
* `Ŝ³ Ω = (m + ½) Ω` (tracking, PR2),
* `Ĥ_tJ Ω = μ Ω` (energy preserved, PR2).

For the d=1 ferromagnetic t-J ground state (`m = (Ne−1)/2`) this gives `Ŝ³ Ω = (Ne/2) Ω` — the
maximal-spin highest weight feeding `highestWeight_spinMultiplet_general`.  The remaining input is
`Ω ≠ 0` (the Marshall positivity, next PR).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum SimpleGraph

variable {N : ℕ}

/-- **The top of the raising tower is a highest-weight ground state.**  From `Ŝ³ Φ = ½ Φ`,
`N̂_↓ Φ = m Φ`, `Ĥ_tJ Φ = μ Φ`, the state `Ω = (Ŝ⁺)^m Φ` satisfies `Ŝ⁺ Ω = 0`,
`Ŝ³ Ω = (m + ½) Ω`, and `Ĥ_tJ Ω = μ Ω`. -/
theorem tJ_raised_highestWeight (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (μ : ℂ) (m : ℕ) (Φ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsz : (fermionTotalSpinZ N).mulVec Φ = ((1 : ℂ) / 2) • Φ)
    (hd : (fermionTotalDownNumber N).mulVec Φ = (m : ℂ) • Φ)
    (hH : (tJHamiltonian N G τ J).mulVec Φ = μ • Φ) :
    (fermionTotalSpinPlus N).mulVec (((fermionTotalSpinPlus N) ^ m).mulVec Φ) = 0 ∧
      (fermionTotalSpinZ N).mulVec (((fermionTotalSpinPlus N) ^ m).mulVec Φ) =
        ((m : ℂ) + 1 / 2) • (((fermionTotalSpinPlus N) ^ m).mulVec Φ) ∧
      (tJHamiltonian N G τ J).mulVec (((fermionTotalSpinPlus N) ^ m).mulVec Φ) =
        μ • (((fermionTotalSpinPlus N) ^ m).mulVec Φ) := by
  refine ⟨?_, ?_, tJHamiltonian_mulVec_spinPlusPow N G τ J Φ μ m hH⟩
  · have h := spinPlusPow_succ_eq_zero_of_downNumber N Φ m hd
    rwa [pow_succ', ← Matrix.mulVec_mulVec] at h
  · rw [fermionTotalSpinZ_mulVec_spinPlusPow N Φ ((1 : ℂ) / 2) m hsz]
    congr 1
    ring

end LatticeSystem.Fermion
