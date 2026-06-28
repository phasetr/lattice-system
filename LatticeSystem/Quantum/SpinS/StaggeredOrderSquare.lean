/-
Two-point expansion of the staggered order operator squared
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The staggered order operator `Ô = Σ_x ε_x Ŝ_x^{(3)}` (with sublattice sign `ε_x = ±1`) squares
to the double sum of two-site `Ŝ^{(3)}` products, `Ô² = Σ_x Σ_y ε_x ε_y Ŝ_x^{(3)} Ŝ_y^{(3)}`.  This
is the bridge from the order parameter to the two-point functions `⟨Ŝ_x^{(3)} Ŝ_y^{(3)}⟩` that the
reflection-positivity / infrared machinery bounds: the squared order parameter per `L²` is
controlled by the total two-point sum, which in one dimension is only `O(L)`.
-/
import LatticeSystem.Quantum.SpinS.DysonLiebSimon

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The staggered order operator squared as a two-point double sum**:
`Ô² = Σ_x Σ_y ε_x ε_y Ŝ_x^{(3)} Ŝ_y^{(3)}`, where `ε_x = ±1` is the sublattice sign. -/
theorem staggeredOrderOpS_sq_eq_sum (A : Λ → Bool) (N : ℕ) :
    staggeredOrderOpS A N * staggeredOrderOpS A N
      = ∑ x : Λ, ∑ y : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A y then (1 : ℂ) else -1))
            • (spinSSiteOp3 x N * spinSSiteOp3 y N) := by
  rw [staggeredOrderOpS, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

end LatticeSystem.Quantum
