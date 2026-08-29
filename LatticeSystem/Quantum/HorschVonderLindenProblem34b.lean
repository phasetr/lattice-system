import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Tasaki Problem 3.4.b: the order fluctuation in the Horsch–von der Linden state `Ξ₊`

Tasaki's Problem 3.4.b asks to show that vanishing of the fourth-moment combination
`⟨Φ_GS|(Ô_L/L^d)⁴|Φ_GS⟩ − {⟨Φ_GS|(Ô_L/L^d)²|Φ_GS⟩}²` as `L ↑ ∞` (eq. (3.4.18)) forces the
fluctuation of `Ô_L/L^d` in the state `|Ξ₊⟩` to vanish, so that `|Ξ₊⟩` behaves like a physical
"ground state".

The state is built here rather than hypothesised: `hvlTrialState` is the Horsch–von der Linden
trial state `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` (eq. (3.4.7)) and `hvlPlusState` is
`|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + |Γ⟩)` (eq. (3.4.14)).  The exact finite-`L` identities of the published
solution — `⟨Ξ₊|Ô_L|Ξ₊⟩ = √(⟨Φ_GS|(Ô_L)²|Φ_GS⟩)` (eq. (3.4.15)),
`⟨Ξ₊|(Ô_L)²|Ξ₊⟩ = (1/2){⟨Φ_GS|(Ô_L)²|Φ_GS⟩ + ⟨Φ_GS|(Ô_L)⁴|Φ_GS⟩/⟨Φ_GS|(Ô_L)²|Φ_GS⟩}` (eq. (S.42))
and the resulting variance identity (eq. (S.43)) — are equalities, not approximations, and are
proved as such.  The capstone then adds the elementary squeeze that turns (3.4.18) into the
vanishing of the fluctuation.

The `L`-indexed family is typed abstractly (`n : ℕ → Type*` with a `Fintype` and a `DecidableEq`
instance for each `L`), because the solution's algebra uses only Hermiticity of `Ô_L`,
normalisation of `|Φ_GS⟩` and the vanishing of its odd moments; no lattice, locality or
Hamiltonian structure enters.  Consequently nothing here certifies any concrete model: neither
that the quantum Ising model satisfies (3.4.18) nor that the antiferromagnetic Heisenberg model
fails it.  The informal notion of a physical "ground state" discussed on p. 69 is not formalised;
only the fluctuation limit is.  Every per-`L` statement is guarded by `1 ≤ L` because the
normalisation `L^d` degenerates at `L = 0`.  The source's `d` is the spatial dimension with
`L^d = |Λ_L|`; the identities are scale-covariant in that factor, so no lower bound on `d` is
required.  Assumption (3.4.4) is used in the form of complex equalities
`⟨Φ_GS|(Ô_L)^k|Φ_GS⟩ = 0` for `k = 1, 3`, which for Hermitian `Ô_L` is equivalent to the vanishing
of the (automatically real) odd moments.

Out of scope here: eq. (3.4.16) `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀`, the Schwarz remark (3.4.17), and the
mirror state `Ξ₋`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, Problem 3.4.b, statement p. 69 eq. (3.4.18), solution p. 501 eqs. (S.42)–(S.43),
with the surrounding eqs. (3.4.3), (3.4.4), (3.4.7), (3.4.14)–(3.4.15), pp. 65–69.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### Sesquilinear reductions -/

/-- A Hermitian square splits as a self-pairing: `⟨v, A² v⟩ = ⟨A v, A v⟩`. -/
private theorem hermitianSq_dotProduct_split {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    star v ⬝ᵥ ((A ^ 2) *ᵥ v) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hA.eq, Matrix.mulVec_mulVec, pow_two]

/-- The squared norm of `A v` is the Rayleigh quotient of `A²` at `v`, for Hermitian `A`. -/
private theorem vecNormSqRe_mulVec_eq_rayleigh {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    vecNormSqRe (A *ᵥ v) = rayleighOnVec (A ^ 2) v := by
  unfold vecNormSqRe rayleighOnVec
  rw [hermitianSq_dotProduct_split hA v]

open scoped ComplexOrder in
/-- The even moment `⟨v, A² v⟩` of a Hermitian `A` is real, hence the coercion of its Rayleigh
quotient.  Instantiated at `A = Ô_L` for `m₂` and at `A = (Ô_L)²` for `m₄`. -/
private theorem even_moment_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    star v ⬝ᵥ ((A ^ 2) *ᵥ v) = ((rayleighOnVec (A ^ 2) v : ℝ) : ℂ) := by
  have him : (star v ⬝ᵥ ((A ^ 2) *ᵥ v)).im = 0 := by
    rw [hermitianSq_dotProduct_split hA v]
    exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  apply Complex.ext
  · rw [Complex.ofReal_re]; rfl
  · rw [Complex.ofReal_im]; exact him

/-- Expansion of a sandwiched form on a scaled sum: `⟨c(u+v), A c(u+v)⟩` is `conj c · c` times the
sum of the four pairings.  The cross terms are kept, since for `Ξ₊` they do not vanish. -/
private theorem smul_add_dotProduct_mulVec {n : Type*} [Fintype n] (c : ℂ)
    (A : Matrix n n ℂ) (u v : n → ℂ) :
    star (c • (u + v)) ⬝ᵥ (A *ᵥ (c • (u + v)))
      = (star c * c) * (star u ⬝ᵥ (A *ᵥ u) + star u ⬝ᵥ (A *ᵥ v) + star v ⬝ᵥ (A *ᵥ u)
          + star v ⬝ᵥ (A *ᵥ v)) := by
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-! ### The Horsch–von der Linden trial state `Γ` and the state `Ξ₊` -/

/-- The **Horsch–von der Linden trial state** `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` (eq. (3.4.7)): the
image of the reference vector under the order operator, unit-normalised in the `L²` pairing. -/
noncomputable def hvlTrialState {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  unitNormalize (O *ᵥ Φ)

/-- The **state `|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + |Γ⟩)`** (eq. (3.4.14)), the symmetric combination of the
reference vector and the Horsch–von der Linden trial state. -/
noncomputable def hvlPlusState {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (Φ + hvlTrialState O Φ)

/-- Scaling `Γ` back by `√m₂` recovers `Ô_L|Φ_GS⟩`, where `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩`. -/
private theorem smul_trialState_eq {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ}
    (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) • hvlTrialState O Φ = O *ᵥ Φ := by
  have hne : ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hm2).ne'
  rw [hvlTrialState, unitNormalize, vecNormSqRe_mulVec_eq_rayleigh hO Φ, smul_smul,
    mul_inv_cancel₀ hne, one_smul]

/-- `Γ` written out as the scalar multiple `(√m₂)⁻¹ • (Ô_L|Φ_GS⟩)`. -/
private theorem trialState_eq_smul {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ}
    (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    hvlTrialState O Φ = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ • (O *ᵥ Φ) := by
  have hne : ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hm2).ne'
  rw [← smul_trialState_eq hO Φ hm2, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- Ket-side absorption: `⟨Φ_GS, (Ô_L)^k Γ⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩`. -/
private theorem dotProduct_mulVec_trialState {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ)
    (k : ℕ) :
    star Φ ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) := by
  rw [trialState_eq_smul hO Φ hm2, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Matrix.mulVec_mulVec, ← pow_succ]

/-- Bra-side adjoint transfer: `⟨Γ, (Ô_L)^k Φ_GS⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩`, using
`Ô_L^† = Ô_L` to move the operator across the pairing. -/
private theorem trialState_dotProduct_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ)
    (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) := by
  rw [trialState_eq_smul hO Φ hm2, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def,
    map_inv₀, Complex.conj_ofReal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hO.eq,
    Matrix.mulVec_mulVec, ← pow_succ']

/-- Diagonal term: `⟨Γ, (Ô_L)^k Γ⟩ = ((√m₂)⁻¹)² ⟨Φ_GS, (Ô_L)^{k+2} Φ_GS⟩`. -/
private theorem trialState_dotProduct_mulVec_trialState {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ)
    (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ (k + 2)) *ᵥ Φ)) := by
  have hpow : (O * O ^ k) * O = O ^ (k + 2) := by
    rw [← pow_succ', ← pow_succ]
  rw [trialState_eq_smul hO Φ hm2, star_smul, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hO.eq, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hpow]
  ring

/-- `Γ` is a unit vector: `⟨Γ, Γ⟩ = 1`, since `‖Ô_L|Φ_GS⟩‖² = m₂ > 0`. -/
private theorem trialState_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} (hO : O.IsHermitian) (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 := by
  have hpos : 0 < vecNormSqRe (O *ᵥ Φ) := by
    rw [vecNormSqRe_mulVec_eq_rayleigh hO Φ]; exact hm2
  rw [hvlTrialState]
  exact unitNormalize_dotProduct_self (O *ᵥ Φ) hpos

/-! ### The moments of `Ξ₊` -/

/-- The scalar of eq. (3.4.14) squares to one half: `conj((√2)⁻¹)·(√2)⁻¹ = 1/2`. -/
private theorem sqrtTwoInv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← mul_inv, ← sq, h2]
  norm_num

/-- **Normalisation of `Ξ₊`** (Tasaki eq. (3.4.14)): `⟨Ξ₊|Ξ₊⟩ = 1`.  The two cross terms
`⟨Φ_GS|Γ⟩` and `⟨Γ|Φ_GS⟩` vanish by the first odd-moment assumption (3.4.4), and both diagonal
terms are `1`, so the global `1/√2` normalises the sum. -/
theorem hvlPlusState_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ)
    (Φ : n → ℂ) (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlPlusState O Φ) ⬝ᵥ hvlPlusState O Φ = 1 := by
  have hΦΓ : star Φ ⬝ᵥ hvlTrialState O Φ = 0 := by
    simpa [hodd1] using dotProduct_mulVec_trialState hHerm Φ hm2 0
  have hΓΦ : star (hvlTrialState O Φ) ⬝ᵥ Φ = 0 := by
    simpa [hodd1] using trialState_dotProduct_mulVec hHerm Φ hm2 0
  have hΓΓ : star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 :=
    trialState_dotProduct_self hHerm Φ hm2
  have hone : star (hvlPlusState O Φ) ⬝ᵥ hvlPlusState O Φ
      = star (hvlPlusState O Φ) ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ hvlPlusState O Φ) := by
    rw [Matrix.one_mulVec]
  rw [hone, hvlPlusState, smul_add_dotProduct_mulVec]
  simp only [Matrix.one_mulVec]
  rw [hΦ, hΦΓ, hΓΦ, hΓΓ, Complex.star_def, map_inv₀, Complex.conj_ofReal, sqrtTwoInv_sq]
  norm_num

/-- **The order parameter of `Ξ₊`** (Tasaki eq. (3.4.15)):
`⟨Ξ₊|Ô_L|Ξ₊⟩ = √(⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`.  The two diagonal terms vanish by the first and third
odd-moment assumptions (3.4.4), and each cross term contributes `m₂/√m₂ = √m₂`. -/
theorem hvlPlusState_order_mean {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ)
    (Φ : n → ℂ) (hHerm : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec O (hvlPlusState O Φ) = Real.sqrt (rayleighOnVec (O ^ 2) Φ) := by
  have hsqrt : ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hm2).ne'
  have hm2s : star Φ ⬝ᵥ ((O ^ 2) *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ^ 2 := by
    rw [even_moment_ofReal hHerm Φ, ← Complex.ofReal_pow, Real.sq_sqrt hm2.le]
  have hbra : star (hvlTrialState O Φ) ⬝ᵥ (O *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ 2) *ᵥ Φ)) := by
    simpa only [pow_one, Nat.reduceAdd] using trialState_dotProduct_mulVec hHerm Φ hm2 1
  have hket : star Φ ⬝ᵥ (O *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ 2) *ᵥ Φ)) := by
    simpa only [pow_one, Nat.reduceAdd] using dotProduct_mulVec_trialState hHerm Φ hm2 1
  have hdiag : star (hvlTrialState O Φ) ⬝ᵥ (O *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ)) := by
    simpa only [pow_one, Nat.reduceAdd] using
      trialState_dotProduct_mulVec_trialState hHerm Φ hm2 1
  have hkey : star (hvlPlusState O Φ) ⬝ᵥ (O *ᵥ hvlPlusState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) := by
    rw [hvlPlusState, smul_add_dotProduct_mulVec, hodd1, hbra, hket, hdiag, hodd3, hm2s,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, sqrtTwoInv_sq]
    field_simp
    ring
  have hdef : rayleighOnVec O (hvlPlusState O Φ)
      = (star (hvlPlusState O Φ) ⬝ᵥ (O *ᵥ hvlPlusState O Φ)).re := rfl
  rw [hdef, hkey, Complex.ofReal_re]

end LatticeSystem.Quantum
