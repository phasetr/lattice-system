import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Horsch–von der Linden trial state (Tasaki §3.4)

The normalised trial state `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` of eq. (3.4.7) and the absorption
algebra that moves powers of the order operator `Ô_L` across the `L²` pairing between `Γ` and the
reference vector `Φ_GS`.  This is the shared `Γ`-vocabulary of §3.4: the states built on top of `Γ`
(the symmetric combination `Ξ₊` of eq. (3.4.14) and its mirror) live in the modules that import
this one.

Everything is stated for an arbitrary finite index type and an arbitrary Hermitian `Ô_L`; the only
quantitative input is positivity of the second moment `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩`, which is what
makes the normalisation of `Γ` well defined.  No lattice, locality or Hamiltonian structure enters,
so nothing here certifies a concrete model.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.7), p. 66.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### Sesquilinear reductions -/

/-- A Hermitian square splits as a self-pairing: `⟨v, A² v⟩ = ⟨A v, A v⟩`. -/
theorem hermitianSq_dotProduct_split {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    star v ⬝ᵥ ((A ^ 2) *ᵥ v) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hA.eq, Matrix.mulVec_mulVec, pow_two]

/-- The squared norm of `A v` is the Rayleigh quotient of `A²` at `v`, for Hermitian `A`. -/
private theorem vecNormSqRe_mulVec_eq_rayleigh {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    vecNormSqRe (A *ᵥ v) = rayleighOnVec (A ^ 2) v := by
  unfold vecNormSqRe rayleighOnVec
  rw [hermitianSq_dotProduct_split hA v]

/-! ### The trial state `Γ` (eq. (3.4.7)) -/

/-- The **Horsch–von der Linden trial state** `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` (eq. (3.4.7)): the
image of the reference vector under the order operator, unit-normalised in the `L²` pairing. -/
noncomputable def hvlTrialState {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  unitNormalize (O *ᵥ Φ)

/-- `Γ` written out as the scalar multiple `(√m₂)⁻¹ • (Ô_L|Φ_GS⟩)`.  This is the defining
unfolding of `unitNormalize`, so no positivity of `m₂` is needed. -/
theorem trialState_eq_smul {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ}
    (hO : O.IsHermitian) (Φ : n → ℂ) :
    hvlTrialState O Φ = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ • (O *ᵥ Φ) := by
  rw [hvlTrialState, unitNormalize, vecNormSqRe_mulVec_eq_rayleigh hO Φ]

/-- Ket-side absorption: `⟨Φ_GS, (Ô_L)^k Γ⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩`. -/
theorem dotProduct_mulVec_trialState {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (k : ℕ) :
    star Φ ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) := by
  rw [trialState_eq_smul hO Φ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Matrix.mulVec_mulVec, ← pow_succ]

/-- `Γ` is a unit vector: `⟨Γ, Γ⟩ = 1`, since `‖Ô_L|Φ_GS⟩‖² = m₂ > 0`. -/
theorem trialState_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 := by
  have hpos : 0 < vecNormSqRe (O *ᵥ Φ) := by
    rw [vecNormSqRe_mulVec_eq_rayleigh hO Φ]; exact hm2
  rw [hvlTrialState]
  exact unitNormalize_dotProduct_self (O *ᵥ Φ) hpos

end LatticeSystem.Quantum
