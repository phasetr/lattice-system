/-
The double commutator equals twice the variational energy of `A Φ` above the ground state
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

For a ground state `Φ` (`H Φ = E₀ Φ`, `E₀` real) and a Hermitian observable `A`, the f-sum-rule
"oscillator strength" `⟨Φ, [A, [H, A]] Φ⟩` equals twice the variational energy of the excited vector
`A Φ` above the ground energy: `Re⟨Φ, [A,[H,A]] Φ⟩ = 2 (Re⟨AΦ, H AΦ⟩ − E₀ Re⟨AΦ, AΦ⟩)`.  This is
denominator (numerator) of the ground-state Falk–Bruch inequality bounding the static two-point
function; together with the variational positivity it shows the double commutator is nonnegative.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBound

namespace LatticeSystem.Quantum

open Matrix Complex

/-- **Double commutator as twice the variational energy** (complex form): for Hermitian `H`, `A`
and a ground state `H Φ = E₀ Φ` (`E₀` real),
`⟨Φ, [A, [H, A]] Φ⟩ = 2 ⟨AΦ, H AΦ⟩ − 2 E₀ ⟨AΦ, AΦ⟩`. -/
theorem double_commutator_ground_state_eq {n : Type*} [Fintype n] {H A : Matrix n n ℂ}
    {Φ : n → ℂ} {E₀ : ℝ} (hH : H.IsHermitian) (hA : A.IsHermitian)
    (hΦ : H.mulVec Φ = (E₀ : ℂ) • Φ) :
    star Φ ⬝ᵥ (A * (H * A - A * H) - (H * A - A * H) * A).mulVec Φ
      = 2 * (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ))
        - 2 * (E₀ : ℂ) * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ) := by
  have hop : A * (H * A - A * H) - (H * A - A * H) * A
      = A * (H * A) + A * (H * A) - A * (A * H) - H * (A * A) := by noncomm_ring
  have hT1 : star Φ ⬝ᵥ (A * (H * A)).mulVec Φ
      = star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ) := by
    rw [hermitian_dotProduct_shift hA, ← Matrix.mulVec_mulVec]
  have hT3 : star Φ ⬝ᵥ (A * (A * H)).mulVec Φ
      = (E₀ : ℂ) * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ) := by
    rw [hermitian_dotProduct_shift hA, ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
  have hT4 : star Φ ⬝ᵥ (H * (A * A)).mulVec Φ
      = (E₀ : ℂ) * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ) := by
    rw [hermitian_dotProduct_shift hH, hΦ, star_smul, smul_dotProduct, smul_eq_mul,
      hermitian_dotProduct_shift hA, RCLike.star_def, conj_ofReal]
  rw [hop]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub, hT1, hT3, hT4]
  ring

end LatticeSystem.Quantum
