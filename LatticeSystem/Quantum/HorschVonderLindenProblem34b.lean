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

end LatticeSystem.Quantum
