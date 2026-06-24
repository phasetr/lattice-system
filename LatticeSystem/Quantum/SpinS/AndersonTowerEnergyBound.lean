import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra
import LatticeSystem.Math.PosSemidef.Basics

/-!
# Tasaki §4.2.1 Theorem 4.6: Anderson tower energy bound — phat foundations

The Anderson tower energy bound (Theorem 4.6) is proved, *given* the long-range-order hypothesis
`q₀`, as a purely finite-volume variational estimate (no reflection positivity — that only enters in
establishing `q₀ > 0`, which is here a hypothesis).  This file collects the `U(1)`-symmetric
order-operator `p̂ = ½(ô⁺ô⁻ + ô⁻ô⁺)` foundations used throughout: the order-density adjoint relation
`(ô^b)ᴴ = ô^{¬b}`, the Hermiticity of `p̂`, its positive-semidefiniteness `⟨Φ, p̂ Φ⟩ ≥ 0` (since
`p̂ = (ô⁽¹⁾)² + (ô⁽²⁾)²` with `ô⁽¹⁾, ô⁽²⁾` Hermitian), and the Cauchy–Schwarz monotonicity of the
moments `⟨Φ, p̂ⁿ Φ⟩` (eq. (4.2.35)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **staggered raising order operator is the adjoint of the lowering one**:
`(Ô_L^+)ᴴ = Ô_L^−` (each per-site `Ŝ⁺` adjoints to `Ŝ⁻`, and the staggered signs `±1` are real). -/
theorem staggeredRaisingOpS_conjTranspose (A : Λ → Bool) :
    Matrix.conjTranspose (staggeredRaisingOpS A N) = staggeredLoweringOpS A N := by
  unfold staggeredRaisingOpS staggeredLoweringOpS spinSSiteOpPlus spinSSiteOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_smul, onSiteS_conjTranspose, spinSOpPlus_conjTranspose]
  congr 1
  split_ifs <;> simp

/-- The **staggered lowering order operator is the adjoint of the raising one**:
`(Ô_L^−)ᴴ = Ô_L^+`. -/
theorem staggeredLoweringOpS_conjTranspose (A : Λ → Bool) :
    Matrix.conjTranspose (staggeredLoweringOpS A N) = staggeredRaisingOpS A N := by
  rw [← staggeredRaisingOpS_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- The **per-volume order-density adjoint**: `(ô^b)ᴴ = ô^{¬b}` (the `(L^d)⁻¹` factor is real). -/
theorem staggeredOrderDensityOpS_conjTranspose (d L N : ℕ) [NeZero L] (b : Bool) :
    Matrix.conjTranspose (staggeredOrderDensityOpS d L N b)
      = staggeredOrderDensityOpS d L N (!b) := by
  unfold staggeredOrderDensityOpS
  rw [Matrix.conjTranspose_smul, star_inv₀, star_pow, Complex.star_def, Complex.conj_natCast]
  cases b <;>
    simp [staggeredRaisingOpS_conjTranspose, staggeredLoweringOpS_conjTranspose]

/-- `ô⁻` is the conjugate transpose of `ô⁺`. -/
theorem staggeredOrderDensityOpS_false_eq_conjTranspose (d L N : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false
      = Matrix.conjTranspose (staggeredOrderDensityOpS d L N true) :=
  (staggeredOrderDensityOpS_conjTranspose d L N true).symm

/-- **`ô⁺ô⁻` is positive-semidefinite** (`= ô⁺(ô⁺)ᴴ`). -/
theorem staggeredOrderDensity_mul_posSemidef_tf (d L N : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (staggeredOrderDensityOpS d L N true)
  rwa [← staggeredOrderDensityOpS_false_eq_conjTranspose] at h

/-- **`ô⁻ô⁺` is positive-semidefinite** (`= (ô⁺)ᴴô⁺`). -/
theorem staggeredOrderDensity_mul_posSemidef_ft (d L N : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (staggeredOrderDensityOpS d L N true)
  rwa [← staggeredOrderDensityOpS_false_eq_conjTranspose] at h

/-- **`p̂` is Hermitian**: `p̂ = ½(ô⁺(ô⁺)ᴴ + (ô⁺)ᴴô⁺)` with both summands Hermitian squares. -/
theorem staggeredPhatS_isHermitian (d L N : ℕ) [NeZero L] :
    (staggeredPhatS d L N).IsHermitian := by
  unfold staggeredPhatS
  refine (((staggeredOrderDensity_mul_posSemidef_tf d L N).1.add
    (staggeredOrderDensity_mul_posSemidef_ft d L N).1).smul ?_)
  rw [isSelfAdjoint_iff, Complex.star_def, map_inv₀, Complex.conj_ofNat]

end LatticeSystem.Quantum
