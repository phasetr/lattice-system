/-
The f-sum-rule oscillator strength as a double sum of two-site double-commutator expectations
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

In the quadratic form of a state `Φ`, the oscillator strength expands as a double site sum:
`⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩ = Σ_x Σ_z ε_x ε_z ⟨Φ, [Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]] Φ⟩`.
Each summand vanishes unless `x` and `z` are adjacent, so the apparent `O(L²)` sum reduces to `O(L)`
bounded terms — the numerator of the Falk–Bruch bound on the staggered order parameter.
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderDoubleCommutator

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The oscillator strength as a double sum of two-site expectations**:
`⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩ = Σ_x Σ_z ε_x ε_z ⟨Φ, [Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]] Φ⟩`. -/
theorem staggeredOrderOpS_double_commutator_dotProduct (A : Λ → Bool) (N : ℕ)
    (H : ManyBodyOpS Λ N) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (staggeredOrderOpS A N * (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H)
        - (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H) * staggeredOrderOpS A N).mulVec Φ
      = ∑ x : Λ, ∑ z : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A z then (1 : ℂ) else -1))
            • (star Φ ⬝ᵥ (spinSSiteOp3 x N * (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H)
                - (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H) * spinSSiteOp3 x N).mulVec Φ) := by
  rw [staggeredOrderOpS_double_commutator]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul]

end LatticeSystem.Quantum
