import LatticeSystem.Quantum.HorschVonderLindenTrialState
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

The state is built rather than hypothesised: on top of the trial state
`|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` (eq. (3.4.7)) and its absorption algebra, imported from
`HorschVonderLindenTrialState`, `hvlPlusState` is the symmetric combination
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

Eq. (3.4.16) `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀` and the Schwarz remark (3.4.17) are in
`HorschVonderLindenLowLyingState.lean`, which reads eq. (3.4.15) below against the long-range-order
assumption (3.4.3).  The mirror state `Ξ₋` of pp. 68-69 is built there too, on the sign identity
`hvlTrialState_neg` of `HorschVonderLindenTrialState.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, Problem 3.4.b, statement p. 69 eq. (3.4.18), solution p. 501 eqs. (S.42)–(S.43),
with the surrounding eqs. (3.4.3), (3.4.4), (3.4.7), (3.4.14)–(3.4.15), pp. 65–69.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### Sesquilinear reductions -/

open scoped ComplexOrder in
/-- The even moment `⟨v, A² v⟩` of a Hermitian `A` is real, hence the coercion of its Rayleigh
quotient.  Instantiated at `A = Ô_L` for `m₂` and at `A = (Ô_L)²` for `m₄`. -/
private theorem even_moment_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    star v ⬝ᵥ ((A ^ 2) *ᵥ v) = ((rayleighOnVec (A ^ 2) v : ℝ) : ℂ) := by
  have him : (star v ⬝ᵥ ((A ^ 2) *ᵥ v)).im = 0 := by
    have hsplit := hermitian_pow_dotProduct_split hA 1 1 v
    rw [pow_one, show (1 : ℕ) + 1 = 2 from rfl] at hsplit
    rw [← hsplit]
    exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  apply Complex.ext
  · rw [Complex.ofReal_re]; rfl
  · rw [Complex.ofReal_im]; exact him

/-- Expansion of a sandwiched form on a scaled sum: `⟨c(u+v), A c(u+v)⟩` is `conj c · c` times the
sum of the four pairings.  All four are kept, since which of them survive depends on the
sandwiched `A`: for `Ξ₊` the cross terms vanish in the normalisation but carry all of (3.4.15).
Against the Hamiltonian both cross terms vanish instead, which is the identity behind the
low-lying energy bound of `HorschVonderLindenLowLyingState.lean`. -/
theorem smul_add_dotProduct_mulVec {n : Type*} [Fintype n] (c : ℂ)
    (A : Matrix n n ℂ) (u v : n → ℂ) :
    star (c • (u + v)) ⬝ᵥ (A *ᵥ (c • (u + v)))
      = (star c * c) * (star u ⬝ᵥ (A *ᵥ u) + star u ⬝ᵥ (A *ᵥ v) + star v ⬝ᵥ (A *ᵥ u)
          + star v ⬝ᵥ (A *ᵥ v)) := by
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-! ### The state `Ξ₊` -/

/-- The **state `|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + |Γ⟩)`** (eq. (3.4.14)), the symmetric combination of the
reference vector and the Horsch–von der Linden trial state. -/
noncomputable def hvlPlusState {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (Φ + hvlTrialState O Φ)

/-! ### The moments of `Ξ₊` -/

/-- **Normalisation of `Ξ₊`** (Tasaki eq. (3.4.14)): `⟨Ξ₊|Ξ₊⟩ = 1`.  The two cross terms
`⟨Φ_GS|Γ⟩` and `⟨Γ|Φ_GS⟩` vanish by the first odd-moment assumption (3.4.4), and both diagonal
terms are `1`, so the global `1/√2` normalises the sum. -/
theorem hvlPlusState_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ)
    (Φ : n → ℂ) (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlPlusState O Φ) ⬝ᵥ hvlPlusState O Φ = 1 := by
  have hΦΓ : star Φ ⬝ᵥ hvlTrialState O Φ = 0 := by
    simpa [hodd1] using dotProduct_mulVec_trialState hHerm Φ 0
  have hΓΦ : star (hvlTrialState O Φ) ⬝ᵥ Φ = 0 := by
    simpa [hodd1] using trialState_dotProduct_mulVec hHerm Φ 0
  have hΓΓ : star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 :=
    trialState_dotProduct_self hHerm Φ hm2
  have hone : star (hvlPlusState O Φ) ⬝ᵥ hvlPlusState O Φ
      = star (hvlPlusState O Φ) ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ hvlPlusState O Φ) := by
    rw [Matrix.one_mulVec]
  rw [hone, hvlPlusState, smul_add_dotProduct_mulVec]
  simp only [Matrix.one_mulVec]
  rw [hΦ, hΦΓ, hΓΦ, hΓΓ, Complex.star_def, map_inv₀, Complex.conj_ofReal, sqrt2_inv_mul_sqrt2_inv]
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
    simpa only [pow_one, Nat.reduceAdd] using trialState_dotProduct_mulVec hHerm Φ 1
  have hket : star Φ ⬝ᵥ (O *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ 2) *ᵥ Φ)) := by
    simpa only [pow_one, Nat.reduceAdd] using dotProduct_mulVec_trialState hHerm Φ 1
  have hdiag : star (hvlTrialState O Φ) ⬝ᵥ (O *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ)) := by
    simpa only [pow_one, Nat.reduceAdd] using
      trialState_dotProduct_mulVec_trialState hHerm Φ 1
  have hkey : star (hvlPlusState O Φ) ⬝ᵥ (O *ᵥ hvlPlusState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) := by
    rw [hvlPlusState, smul_add_dotProduct_mulVec, hodd1, hbra, hket, hdiag, hodd3, hm2s,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, sqrt2_inv_mul_sqrt2_inv]
    field_simp
    ring
  have hdef : rayleighOnVec O (hvlPlusState O Φ)
      = (star (hvlPlusState O Φ) ⬝ᵥ (O *ᵥ hvlPlusState O Φ)).re := rfl
  rw [hdef, hkey, Complex.ofReal_re]

/-- **The second moment of `Ξ₊`** (Tasaki eq. (S.42)):
`⟨Ξ₊|(Ô_L)²|Ξ₊⟩ = (1/2){m₂ + m₄/m₂}` with `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩` and
`m₄ = ⟨Φ_GS|(Ô_L)⁴|Φ_GS⟩`.  The cross terms carry the third moment and vanish by (3.4.4). -/
theorem hvlPlusState_order_second_moment {n : Type*} [Fintype n] [DecidableEq n]
    (O : Matrix n n ℂ) (Φ : n → ℂ) (hHerm : O.IsHermitian)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec (O ^ 2) (hvlPlusState O Φ)
      = 1 / 2 * (rayleighOnVec (O ^ 2) Φ + rayleighOnVec (O ^ 4) Φ / rayleighOnVec (O ^ 2) Φ) := by
  have hsqrt : ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hm2).ne'
  have hm2z : ((rayleighOnVec (O ^ 2) Φ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm2.ne'
  have hsq : ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) ^ 2
      = ((rayleighOnVec (O ^ 2) Φ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hm2.le]
  have hm2c : star Φ ⬝ᵥ ((O ^ 2) *ᵥ Φ) = ((rayleighOnVec (O ^ 2) Φ : ℝ) : ℂ) :=
    even_moment_ofReal hHerm Φ
  have hpow4 : ((O ^ 2) ^ 2 : Matrix n n ℂ) = O ^ 4 := by rw [← pow_mul]
  have hm4c : star Φ ⬝ᵥ ((O ^ 4) *ᵥ Φ) = ((rayleighOnVec (O ^ 4) Φ : ℝ) : ℂ) := by
    have h := even_moment_ofReal (hHerm.pow 2) Φ
    rwa [hpow4] at h
  have hbra : star (hvlTrialState O Φ) ⬝ᵥ ((O ^ 2) *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ)) := by
    simpa only [Nat.reduceAdd] using trialState_dotProduct_mulVec hHerm Φ 2
  have hket : star Φ ⬝ᵥ ((O ^ 2) *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ)) := by
    simpa only [Nat.reduceAdd] using dotProduct_mulVec_trialState hHerm Φ 2
  have hdiag : star (hvlTrialState O Φ) ⬝ᵥ ((O ^ 2) *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ 4) *ᵥ Φ)) := by
    simpa only [Nat.reduceAdd] using trialState_dotProduct_mulVec_trialState hHerm Φ 2
  have hkey : star (hvlPlusState O Φ) ⬝ᵥ ((O ^ 2) *ᵥ hvlPlusState O Φ)
      = ((1 / 2 * (rayleighOnVec (O ^ 2) Φ
          + rayleighOnVec (O ^ 4) Φ / rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ) := by
    rw [hvlPlusState, smul_add_dotProduct_mulVec, hbra, hket, hdiag, hodd3, hm2c, hm4c,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, sqrt2_inv_mul_sqrt2_inv]
    push_cast
    rw [← hsq]
    field_simp
    ring
  have hdef : rayleighOnVec (O ^ 2) (hvlPlusState O Φ)
      = (star (hvlPlusState O Φ) ⬝ᵥ ((O ^ 2) *ᵥ hvlPlusState O Φ)).re := rfl
  rw [hdef, hkey, Complex.ofReal_re]

/-- **The fluctuation identity for `Ξ₊`** (Tasaki eq. (S.43)), in the `L^d`-normalised form used by
Problem 3.4.b.  Writing `V` for the volume factor `L^d`, the variance of `Ô_L/V` in `Ξ₊` equals
`(1/2){⟨Φ_GS|(Ô_L/V)²|Φ_GS⟩}^{-1}[⟨Φ_GS|(Ô_L/V)⁴|Φ_GS⟩ − {⟨Φ_GS|(Ô_L/V)²|Φ_GS⟩}²]`.  This is an
exact identity at every finite volume, not an asymptotic statement. -/
theorem hvlPlusState_order_variance {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ)
    (Φ : n → ℂ) (V : ℝ) (hHerm : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) (hV : 0 < V) :
    rayleighOnVec (O ^ 2) (hvlPlusState O Φ) / V ^ 2
        - (rayleighOnVec O (hvlPlusState O Φ) / V) ^ 2
      = 1 / 2 * (rayleighOnVec (O ^ 4) Φ / V ^ 4 - (rayleighOnVec (O ^ 2) Φ / V ^ 2) ^ 2)
          / (rayleighOnVec (O ^ 2) Φ / V ^ 2) := by
  rw [hvlPlusState_order_second_moment O Φ hHerm hodd3 hm2,
    hvlPlusState_order_mean O Φ hHerm hodd1 hodd3 hm2, div_pow, Real.sq_sqrt hm2.le]
  field_simp
  ring

/-! ### The vanishing of the fluctuation -/

/-- Scalar squeeze: if the second moments stay above a positive constant `q₀` for `L ≥ 1` and the
fourth-moment combination tends to `0`, then so does the ratio appearing in eq. (S.43). -/
private theorem tendsto_variance_ratio_of_tendsto_sub {q₀ : ℝ} (hq₀ : 0 < q₀) (M2 M4 : ℕ → ℝ)
    (hM2 : ∀ L : ℕ, 1 ≤ L → q₀ ≤ M2 L)
    (hsub : Filter.Tendsto (fun L : ℕ => M4 L - (M2 L) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun L : ℕ => 1 / 2 * (M4 L - (M2 L) ^ 2) / M2 L) Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' (a := fun L : ℕ => |M4 L - (M2 L) ^ 2| / (2 * q₀)) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with L hL
    have hpos : 0 < M2 L := lt_of_lt_of_le hq₀ (hM2 L hL)
    have hrw : 1 / 2 * (M4 L - (M2 L) ^ 2) / M2 L
        = (M4 L - (M2 L) ^ 2) / (2 * M2 L) := by ring
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * M2 L)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) (by linarith [hM2 L hL])
  · simpa using (hsub.abs).div_const (2 * q₀)

/-- **Tasaki Problem 3.4.b** (statement p. 69 eq. (3.4.18), solution p. 501 eqs. (S.42)–(S.43)).
For an `L`-indexed family of finite-dimensional spaces carrying Hermitian order operators `Ô_L`
and normalised reference vectors `|Φ_GS⟩` whose first and third moments vanish (3.4.4), and whose
normalised second moment stays above an `L`-independent `q₀ > 0` (3.4.3), the constructed states
`|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + Ô_L|Φ_GS⟩/‖Ô_L|Φ_GS⟩‖)` satisfy, at every `L ≥ 1`, the normalisation
`⟨Ξ₊|Ξ₊⟩ = 1` (3.4.14), the order-parameter identity (3.4.15), the second-moment identity (S.42)
and the fluctuation identity (S.43); and, assuming (3.4.18), the fluctuation of `Ô_L/L^d` in
`|Ξ₊⟩` tends to `0` as `L ↑ ∞`.

The Hamiltonian never appears: the low-lying energy bound of the unnumbered sentence following
(3.4.14) (p. 68) and the ground-state property of `|Φ_GS⟩` are not assumed, matching the published
solution, which derives (S.42)/(S.43) from Hermiticity, normalisation and (3.4.4) alone.  The
informal conclusion that `|Ξ₊⟩` "can be regarded as a physical ground state" is not formalised
here; the source itself defers its precise formulation to §4.3. -/
theorem tasaki_problem_3_4_b_order_fluctuation {n : ℕ → Type*} [∀ L, Fintype (n L)]
    [∀ L, DecidableEq (n L)] (d : ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Φ : (L : ℕ) → n L → ℂ)
    (hHerm : ∀ L, (O L).IsHermitian)
    (hΦ : ∀ L, star (Φ L) ⬝ᵥ Φ L = 1)
    (hodd1 : ∀ L, star (Φ L) ⬝ᵥ (O L) *ᵥ Φ L = 0)
    (hodd3 : ∀ L, star (Φ L) ⬝ᵥ ((O L) ^ 3) *ᵥ Φ L = 0)
    (hLRO : ∀ L : ℕ, 1 ≤ L → q₀ ≤ rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
    (hFourth : Filter.Tendsto
      (fun L : ℕ => rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
        - (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ^ 2)
      Filter.atTop (nhds 0)) :
    (∀ L : ℕ, 1 ≤ L →
        star (hvlPlusState (O L) (Φ L)) ⬝ᵥ hvlPlusState (O L) (Φ L) = 1
      ∧ rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d
          = Real.sqrt (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
      ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2
              + rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
                / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2))
      ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
              - (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ^ 2)
            / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2))
    ∧ Filter.Tendsto
        (fun L : ℕ =>
          rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
            - (rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d) ^ 2)
        Filter.atTop (nhds 0) := by
  have hmain : ∀ L : ℕ, 1 ≤ L →
      star (hvlPlusState (O L) (Φ L)) ⬝ᵥ hvlPlusState (O L) (Φ L) = 1
    ∧ rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d
        = Real.sqrt (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
    ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
        = 1 / 2 * (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2
            + rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
              / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2))
    ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
        - (rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d) ^ 2
        = 1 / 2 * (rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
            - (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ^ 2)
          / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) := by
    intro L hL
    have hV : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (by exact_mod_cast hL) d
    have hm2 : 0 < rayleighOnVec ((O L) ^ 2) (Φ L) := by
      have hq : 0 < rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2 :=
        lt_of_lt_of_le hq₀ (hLRO L hL)
      have hid : rayleighOnVec ((O L) ^ 2) (Φ L)
          = rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2 * ((L : ℝ) ^ d) ^ 2 := by
        field_simp
      rw [hid]
      exact mul_pos hq (by positivity)
    refine ⟨hvlPlusState_dotProduct_self (O L) (Φ L) (hHerm L) (hΦ L) (hodd1 L) hm2, ?_, ?_,
      hvlPlusState_order_variance (O L) (Φ L) ((L : ℝ) ^ d) (hHerm L) (hodd1 L) (hodd3 L) hm2 hV⟩
    · rw [hvlPlusState_order_mean (O L) (Φ L) (hHerm L) (hodd1 L) (hodd3 L) hm2,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq hV.le]
    · rw [hvlPlusState_order_second_moment (O L) (Φ L) (hHerm L) (hodd3 L) hm2]
      field_simp
  refine ⟨hmain, ?_⟩
  refine Filter.Tendsto.congr' ?_
    (tendsto_variance_ratio_of_tendsto_sub hq₀
      (fun L : ℕ => rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
      (fun L : ℕ => rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4) hLRO hFourth)
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  exact ((hmain L hL).2.2.2).symm

end LatticeSystem.Quantum
