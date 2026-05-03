import LatticeSystem.Quantum.SpinS.SingleSiteCasimirExpectation
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Sum of two-site correlations on a singlet vanishes

For any singlet state `Φ` (i.e., a `Ŝ_tot²`-eigenvector at
eigenvalue `0`) on the multi-site spin-`S` Hilbert space, the
double sum of two-site correlations vanishes:

  `∑_{x : V} ∑_{y : V} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = 0`.

Proof: by `totalSpinSSquared_eq_sum_spinSDot`, the LHS equals
`⟨Φ, Ŝ_tot² · Φ⟩`. The singlet condition `Ŝ_tot² Φ = 0` gives
the result via `dotProduct_zero`.

Useful for Tasaki Problem 2.5.d (γ-8) two-spin correlations.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The full two-site correlation sum on a singlet vanishes:

  `∑_{x, y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = 0`.

Combines `totalSpinSSquared_eq_sum_spinSDot` with the singlet
condition. -/
theorem totalSpinSSquared_singlet_correlation_full_sum
    {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared V N).mulVec Φ = 0) :
    ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) = 0 := by
  -- Step 1: combine all `dotProduct` terms via linearity to a single
  -- `dotProduct (star Φ) ((∑_{x,y} Ŝ_x · Ŝ_y).mulVec Φ)`.
  have h_distrib : ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) =
      dotProduct (star Φ)
        ((∑ x : V, ∑ y : V, spinSDot x y N).mulVec Φ) := by
    rw [Matrix.sum_mulVec]
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.sum_mulVec]
    rw [dotProduct_sum]
  rw [h_distrib]
  -- Step 2: ∑_{x,y} Ŝ_x · Ŝ_y = Ŝ_tot² (Casimir decomposition).
  rw [← totalSpinSSquared_eq_sum_spinSDot]
  -- Step 3: Ŝ_tot² Φ = 0 (singlet condition).
  rw [hΦ, dotProduct_zero]

end LatticeSystem.Quantum
