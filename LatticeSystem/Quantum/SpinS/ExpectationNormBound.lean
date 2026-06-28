/-
The expectation of an operator in a normalized state is bounded by its operator norm
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

For any many-body operator `M` and a normalized state `Φ` (`star Φ ⬝ᵥ Φ = 1`), the real part of the
expectation is bounded by the operator norm: `|⟨Φ, M Φ⟩.re| ≤ ‖M‖` — the general
norm-to-expectation bound (normalized-state form of `abs_re_dotProduct_mulVec_le_norm_mul`), used to
turn the per-bond and oscillator-strength norm bounds into expectation bounds in the Falk–Bruch
argument.
-/
import LatticeSystem.Quantum.SpinS.TransverseBondEnergyExpectation

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Expectation bounded by the operator norm in a normalized state**:
`|⟨Φ, M Φ⟩.re| ≤ ‖M‖` whenever `star Φ ⬝ᵥ Φ = 1`. -/
theorem expectation_abs_le_manyBodyOperatorNormS (M : ManyBodyOpS Λ N)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) :
    |(star Φ ⬝ᵥ M.mulVec Φ).re| ≤ manyBodyOperatorNormS M := by
  have hbridge := abs_re_dotProduct_mulVec_le_norm_mul M Φ Φ
  rwa [toLp_norm_eq_one_of_normalized hΦ, mul_one, mul_one] at hbridge

end LatticeSystem.Quantum
