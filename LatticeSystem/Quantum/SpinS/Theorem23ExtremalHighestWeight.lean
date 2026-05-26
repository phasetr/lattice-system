import LatticeSystem.Quantum.SpinS.Theorem23ExtremalSector
import LatticeSystem.Quantum.SpinS.Theorem23Casimir

/-!
# Extremal-sector highest weight has the predicted total Casimir

Scaffold for the minimal-total-spin joint eigenstate (Issue #3674, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

A vector in the extremal magnetization sector `M = min(|A|, |¬A|)·N` (magnetization
`|s_A − s_B|`) annihilated by `Ŝ⁺_tot` is a `(Ŝ_tot)²`-eigenvector at exactly the
predicted Casimir value `tasaki23PredictedCasimirValue A N`: the total highest-weight
relation gives `(Ŝ_tot)² = m(m+1)` with `m = |s_A − s_B|` (`Theorem23ExtremalSector`).

Together with the maximal sublattice Casimirs (`Theorem23AntialignedJointEigenvector`),
such a highest-weight vector is the minimal-total-spin joint eigenstate; its existence
(the Clebsch–Gordan content) is the last remaining obligation.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Extremal-sector highest weight has the predicted total Casimir**: a vector in
the extremal magnetization sector annihilated by `Ŝ⁺_tot` is a `(Ŝ_tot)²`-eigenvector
at the predicted Casimir value. -/
theorem tasaki23_extremal_highestWeight_totalCasimir_eq_predicted (A : V → Bool)
    {w : (V → Fin (N + 1)) → ℂ}
    (hw_mem : w ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) -
        ((min (Finset.univ.filter (fun x : V => A x = true)).card
            (Finset.univ.filter (fun x : V => (! A x) = true)).card * N : ℕ) : ℂ)))
    (hker : (totalSpinSOpPlus V N).mulVec w = 0) :
    (totalSpinSSquared V N).mulVec w =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • w := by
  set m : ℂ := ((Fintype.card V : ℂ) * (N : ℂ) / 2) -
      ((min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N : ℕ) : ℂ) with hm
  have hhw := tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS
    hw_mem hker
  -- m is real with m.re = predicted total spin.
  have hm_re : m.re = tasaki23PredictedTotalSpin (V := V) A N :=
    tasaki23_extremal_sector_magnetization_re_eq_predicted A N
  have hm_im : m.im = 0 := by rw [hm]; simp [Complex.sub_im, Complex.mul_im]
  have hm_eq : m = ((tasaki23PredictedTotalSpin (V := V) A N : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hm_re, Complex.ofReal_re]
    · rw [hm_im, Complex.ofReal_im]
  rw [hhw, hm_eq]
  rw [tasaki23PredictedCasimirValue]
  push_cast
  ring_nf

end LatticeSystem.Quantum
