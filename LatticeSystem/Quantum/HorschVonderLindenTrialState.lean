import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Horsch–von der Linden trial state and the basic variational estimate (Tasaki §3.4)

The normalised trial state `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` of eq. (3.4.7), the absorption algebra
that moves powers of the order operator `Ô_L` across the `L²` pairing between `Γ` and the reference
vector `Φ_GS`, and the basic variational estimate

`⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L, [Ĥ, Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)` (eq. (3.4.8))

together with its non-negativity side.  This is the shared `Γ`-vocabulary of §3.4: the states built
on top of `Γ` (the symmetric combination `Ξ₊` of eq. (3.4.14) and its mirror) live in the modules
that import this one.

Everything is stated for an arbitrary finite index type and an arbitrary Hermitian `Ô_L`; the only
quantitative input is positivity of the second moment `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩`, which is what
makes the normalisation of `Γ` well defined.  No lattice, locality or Hamiltonian structure enters
the trial-state algebra, so nothing here certifies a concrete model.

Eq. (3.4.8) is the un-normalised double-commutator identity `double_commutator_ground_state_eq`
divided by `2 m₂`, rewritten through the unit normalisation of `Γ`; as such it holds at any
eigenvector `Φ_GS` of `Ĥ`, with `E_GS` its eigenvalue, and needs no long-range-order or odd-moment
assumption.  Its non-negativity side genuinely needs `E_GS` to be a *ground-state* energy, i.e. the
minimum of the Rayleigh quotient over normalised vectors — the book's running assumption of the
"Setting and assumptions" paragraph, p. 65, used silently at (3.4.8) — so that hypothesis is
carried explicitly: at a non-minimal eigenvalue the difference is genuinely negative.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, "Setting and assumptions" p. 65, eqs. (3.4.7)–(3.4.8), p. 66.
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

/-- Bra-side adjoint transfer: `⟨Γ, (Ô_L)^k Φ_GS⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩`, using
`Ô_L^† = Ô_L` to move the operator across the pairing. -/
theorem trialState_dotProduct_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) := by
  rw [trialState_eq_smul hO Φ, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def,
    map_inv₀, Complex.conj_ofReal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hO.eq,
    Matrix.mulVec_mulVec, ← pow_succ']

/-- Diagonal term: `⟨Γ, (Ô_L)^k Γ⟩ = ((√m₂)⁻¹)² ⟨Φ_GS, (Ô_L)^{k+2} Φ_GS⟩`. -/
theorem trialState_dotProduct_mulVec_trialState {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ (k + 2)) *ᵥ Φ)) := by
  have hpow : (O * O ^ k) * O = O ^ (k + 2) := by
    rw [← pow_succ', ← pow_succ]
  rw [trialState_eq_smul hO Φ, star_smul, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hO.eq, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hpow]
  ring

/-- `Γ` is a unit vector: `⟨Γ, Γ⟩ = 1`, since `‖Ô_L|Φ_GS⟩‖² = m₂ > 0`. -/
theorem trialState_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 := by
  have hpos : 0 < vecNormSqRe (O *ᵥ Φ) := by
    rw [vecNormSqRe_mulVec_eq_rayleigh hO Φ]; exact hm2
  rw [hvlTrialState]
  exact unitNormalize_dotProduct_self (O *ᵥ Φ) hpos

/-! ### The basic variational estimate (eq. (3.4.8)) -/

/-- **The basic variational estimate** (Tasaki eq. (3.4.8), p. 66):
`⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L, [Ĥ, Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`.  It is the un-normalised
double-commutator identity divided by `2 m₂`, so it holds at any eigenvector `Φ_GS` of `Ĥ` with
eigenvalue `E_GS`; the ground-state property of `Φ_GS` is used only for the non-negativity of the
left-hand side, not for the identity. -/
theorem hvlTrialState_energy_sub_eq {n : Type*} [Fintype n] [DecidableEq n]
    {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀
      = (star Φ ⬝ᵥ ((O * (H * O - O * H) - (H * O - O * H) * O) *ᵥ Φ)).re
          / (2 * rayleighOnVec (O ^ 2) Φ) := by
  have hself : (star (O *ᵥ Φ) ⬝ᵥ (O *ᵥ Φ)).re = rayleighOnVec (O ^ 2) Φ :=
    vecNormSqRe_mulVec_eq_rayleigh hO Φ
  have hnum : (star Φ ⬝ᵥ ((O * (H * O - O * H) - (H * O - O * H) * O) *ᵥ Φ)).re
      = 2 * rayleighOnVec H (O *ᵥ Φ) - 2 * E₀ * rayleighOnVec (O ^ 2) Φ := by
    rw [double_commutator_ground_state_eq hH hO hΦE, ← hself]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, rayleighOnVec]
    ring
  have hcplx : star (hvlTrialState O Φ) ⬝ᵥ (H *ᵥ hvlTrialState O Φ)
      = (((rayleighOnVec (O ^ 2) Φ)⁻¹ : ℝ) : ℂ) * (star (O *ᵥ Φ) ⬝ᵥ (H *ᵥ (O *ᵥ Φ))) := by
    rw [trialState_eq_smul hO Φ, star_smul, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, map_inv₀,
      Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt hm2.le]
  have hscale : rayleighOnVec H (hvlTrialState O Φ)
      = rayleighOnVec H (O *ᵥ Φ) / rayleighOnVec (O ^ 2) Φ := by
    change (star (hvlTrialState O Φ) ⬝ᵥ (H *ᵥ hvlTrialState O Φ)).re = _
    rw [hcplx, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      div_eq_inv_mul]
    rfl
  rw [hnum, hscale]
  field_simp

/-- **Non-negativity of the basic variational estimate** (Tasaki eq. (3.4.8), p. 66):
`⟨Γ|Ĥ|Γ⟩ − E_GS ≥ 0`.  Unlike the identity itself this direction needs `E_GS` to be a ground-state
energy: `hGS` is the book's running assumption of the "Setting and assumptions" paragraph (p. 65),
that `E_GS` is the minimum of the Rayleigh quotient over normalised vectors, and it is applied at
the normalised trial state `Γ`.  At a non-minimal eigenvalue the difference is genuinely negative,
so `hGS` cannot be dropped.  The Hermiticity of `Ĥ` and the eigenvector hypothesis are carried for
uniformity with `hvlTrialState_energy_sub_eq` and are not used by this direction. -/
theorem hvlTrialState_energy_sub_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ} (_hH : H.IsHermitian) (hO : O.IsHermitian)
    (_hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ)
    (hGS : ∀ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 → (E₀ : ℝ) ≤ rayleighOnVec H ψ) :
    0 ≤ rayleighOnVec H (hvlTrialState O Φ) - E₀ :=
  sub_nonneg.mpr (hGS (hvlTrialState O Φ) (trialState_dotProduct_self hO Φ hm2))

end LatticeSystem.Quantum
