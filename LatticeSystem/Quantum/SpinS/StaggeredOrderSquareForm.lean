/-
Ground-state two-point expansion of the staggered order parameter
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

In the quadratic-form (state expectation) used by Corollary 4.3, the squared staggered order
parameter expands as the double sum of two-point expectations:
`⟨Φ, Ô² Φ⟩ = Σ_x Σ_y ε_x ε_y ⟨Φ, Ŝ_x^{(3)} Ŝ_y^{(3)} Φ⟩`.
This rewrites the order parameter directly in the form `star Φ ⬝ᵥ (Ô²).mulVec Φ` appearing in the
Corollary, through the two-point functions that the reflection-positivity machinery bounds.
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderSquare

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Ground-state two-point expansion of the squared order parameter**:
`⟨Φ, Ô² Φ⟩ = Σ_x Σ_y ε_x ε_y ⟨Φ, Ŝ_x^{(3)} Ŝ_y^{(3)} Φ⟩`. -/
theorem staggeredOrderOpS_sq_dotProduct (A : Λ → Bool) (N : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ
      = ∑ x : Λ, ∑ y : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A y then (1 : ℂ) else -1))
            • (star Φ ⬝ᵥ (spinSSiteOp3 x N * spinSSiteOp3 y N).mulVec Φ) := by
  rw [staggeredOrderOpS_sq_eq_sum]
  simp only [Matrix.sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul]

end LatticeSystem.Quantum
