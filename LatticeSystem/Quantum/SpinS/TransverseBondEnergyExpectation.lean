/-
Expectation bound on the transverse bond energy in a normalized state
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

In any normalized state `Φ` (`star Φ ⬝ᵥ Φ = 1`) the expectation of the transverse bond energy is
bounded by its operator norm: `|⟨Φ, (Ŝ_a^{(1)} Ŝ_b^{(1)} + Ŝ_a^{(2)} Ŝ_b^{(2)}) Φ⟩| ≤ 2 N²`.  Summed
over the `O(L)` bonds adjacent to a site this bounds the f-sum-rule oscillator strength
`⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩` by `O(L)` — the numerator of the Falk–Bruch bound.
-/
import LatticeSystem.Quantum.SpinS.TransverseBondEnergyNorm

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The Euclidean (ℓ²) norm of a normalized raw vector is `1`. -/
theorem toLp_norm_eq_one_of_normalized {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) :
    ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ ^ 2 = 1 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [← h, dotProduct_comm, hΦ]
    simp
  nlinarith [hsq, norm_nonneg (WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))]

/-- **Expectation bound on the transverse bond energy**: in a normalized state `Φ`,
`|⟨Φ, (Ŝ_a^{(1)} Ŝ_b^{(1)} + Ŝ_a^{(2)} Ŝ_b^{(2)}) Φ⟩.re| ≤ 2 N²`. -/
theorem transverseBondEnergy_expectation_abs_le (a b : Λ) (hN : 1 ≤ N)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) :
    |(star Φ ⬝ᵥ (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)
        + onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)).mulVec Φ).re| ≤ 2 * (N : ℝ) ^ 2 := by
  have hbridge := abs_re_dotProduct_mulVec_le_norm_mul
    (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)
      + onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)) Φ Φ
  rw [toLp_norm_eq_one_of_normalized hΦ, mul_one, mul_one] at hbridge
  exact le_trans hbridge (transverseBondEnergy_manyBodyOperatorNormS_le a b hN)

end LatticeSystem.Quantum
