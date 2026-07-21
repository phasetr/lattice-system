import LatticeSystem.Math.RayleighPosSemidefKernel

/-!
# Tasaki Appendix A.2.3: zeros of the energy form are kernel vectors (Lemma A.11)

Tasaki's Lemma A.11, "sometimes powerful and useful": if `Â ≥ 0` and the energy expectation
`⟨Φ|Â|Φ⟩ = 0`, then `Â|Φ⟩ = 0`; and if `Â = B̂†B̂`, then `⟨Φ|Â|Φ⟩ = 0` (equivalently
`Â|Φ⟩ = 0`) implies `B̂|Φ⟩ = 0`.  The model-agnostic content is already proved in
`Math/RayleighPosSemidefKernel`; this file states it with Tasaki's `⟨Φ|Â|Φ⟩`-form (the full
complex inner product `star Φ ⬝ᵥ Â Φ`, rather than the real Rayleigh part) and records the
angular-momentum corollary Tasaki gives as an illustration.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Lemma A.11, p. 469.
-/

namespace LatticeSystem.Math

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- **Tasaki Lemma A.11 (first part).**  If `Â ≥ 0` and `⟨Φ|Â|Φ⟩ = 0` (the full complex energy
expectation `star Φ ⬝ᵥ Â Φ` vanishes), then `Â Φ = 0`. -/
theorem posSemidef_mulVec_eq_zero_of_inner_zero {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {Φ : n → ℂ} (h : star Φ ⬝ᵥ A.mulVec Φ = 0) : A.mulVec Φ = 0 :=
  posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero hA (by
    change (star Φ ⬝ᵥ A.mulVec Φ).re = 0
    rw [h, Complex.zero_re])

/-- **Tasaki Lemma A.11 (second part).**  If `Â = B̂†B̂` and `⟨Φ|Â|Φ⟩ = 0`, then `B̂ Φ = 0`
(`⟨Φ|B̂†B̂|Φ⟩ = ‖B̂ Φ‖² = 0`). -/
theorem conjTranspose_mul_self_mulVec_eq_zero_of_inner_zero {m : Type*} [Fintype m]
    {B : Matrix m n ℂ} {Φ : n → ℂ} (h : star Φ ⬝ᵥ (Bᴴ * B).mulVec Φ = 0) : B.mulVec Φ = 0 :=
  conjTranspose_mul_self_mulVec_eq_zero
    (posSemidef_mulVec_eq_zero_of_inner_zero (Matrix.posSemidef_conjTranspose_mul_self B) h)

/-- **Angular-momentum corollary of Lemma A.11** (Tasaki's illustration): if
`Ĵ² = (Ĵ⁽¹⁾)² + (Ĵ⁽²⁾)² + (Ĵ⁽³⁾)²` with self-adjoint `Ĵ⁽ᵅ⁾` and `Ĵ²|Φ⟩ = 0`, then
`Ĵ⁽ᵅ⁾|Φ⟩ = 0` for each `α`.  Each `(Ĵ⁽ᵅ⁾)² = (Ĵ⁽ᵅ⁾)†Ĵ⁽ᵅ⁾ ≥ 0`, so `⟨Φ|Ĵ²|Φ⟩ = 0` forces each
`⟨Φ|(Ĵ⁽ᵅ⁾)²|Φ⟩ = 0`, hence `Ĵ⁽ᵅ⁾|Φ⟩ = 0` by Lemma A.11. -/
theorem mulVec_eq_zero_of_sq_sum_inner_zero {ι : Type*} (s : Finset ι) (J : ι → Matrix n n ℂ)
    (hJ : ∀ α ∈ s, (J α).IsHermitian) {Φ : n → ℂ}
    (h : star Φ ⬝ᵥ (∑ α ∈ s, (J α) * (J α)).mulVec Φ = 0) :
    ∀ α ∈ s, (J α).mulVec Φ = 0 := by
  have hnn : ∀ α ∈ s, 0 ≤ rayleighOnVec ((J α) * (J α)) Φ := by
    intro α hα
    have hps : ((J α) * (J α)).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self (J α)
      rwa [(hJ α hα).eq] at this
    simpa using (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg Φ)).1
  have hsum0 : ∑ α ∈ s, rayleighOnVec ((J α) * (J α)) Φ = 0 := by
    rw [← rayleighOnVec_sum]
    change (star Φ ⬝ᵥ (∑ α ∈ s, (J α) * (J α)).mulVec Φ).re = 0
    rw [h, Complex.zero_re]
  intro α hα
  have hαz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 α hα
  have hps : ((J α) * (J α)).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (J α)
    rwa [(hJ α hα).eq] at this
  have hker := posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero hps hαz
  refine conjTranspose_mul_self_mulVec_eq_zero ?_
  rwa [(hJ α hα).eq]

end LatticeSystem.Math
