import LatticeSystem.Fermion.JWAbstract
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Fock space representation of tight-binding electrons (Tasaki §9.2.3)

This file sets up the second-quantized (Fock space) representation of
the Slater determinant states used throughout Part III of

  Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer (2020), §9.2.3, pp. 314–321.

We work with the concrete Jordan–Wigner representation already developed
in `LatticeSystem.Fermion.JWAbstract`, where for a finite, linearly
ordered mode-index type `Λ` the smeared creation operator

  `Ĉ†(φ) = Σ_x φ(x) ĉ†_x`               (Tasaki eq. (9.2.46))

acts on the many-body space `(Λ → Fin 2) → ℂ`. The Slater determinant
state of single-electron wave functions `φ⁽¹⁾, …, φ⁽ᴺ⁾` is

  `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾) |Φvac⟩`.   (Tasaki eq. (9.2.52))

## Main results

* `fermionCreationFromVector`, `slaterState` — the smeared creation
  operator and the Slater determinant state.
* `lemma_9_1_slater_inner_det` — **Tasaki Lemma 9.1** (p. 319, eq.
  (9.2.53)): the inner product of two Slater determinant states equals
  the determinant of the single-particle overlap (Gram) matrix.
* `lemma_9_1_slater_inner_perm_sum` — the explicit permutation-sum form
  of eq. (9.2.53), derived from `lemma_9_1_slater_inner_det`.
* `lemma_9_2_slater_ne_zero_iff_linearIndependent` — **Tasaki Lemma 9.2**
  (p. 320): the Slater determinant state is nonvanishing iff its
  single-electron wave functions are linearly independent.

## Status of Lemma 9.1

Tasaki's Lemma 9.1 is the determinant overlap identity for Slater
states. In the concrete Jordan–Wigner representation it is a
finite-dimensional linear-algebra statement, but a direct sorry-free
proof requires a dedicated development (the canonical anticommutator
Wick/Laplace expansion together with the Koszul/ordered-list sign
bookkeeping, comparable in size to the flat-band Slater-reorder work).
We therefore record it here as a **faithful documented axiom** — the
standard project treatment for heavy results that are in scope but not
yet discharged — and prove its `n = 0` instance independently
(`fockInner_vacuum_self`) as a consistency guard. The downstream
Lemmas 9.2 and 9.3 are proved from this identity.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-- The Jordan–Wigner Fock vacuum `|Φvac⟩`: the all-empty
computational-basis configuration `(fun _ => 0)` (Tasaki §9.2.3,
p. 314). It is annihilated by every `ĉ_x`. -/
noncomputable def fermionVacuumAbstract : (Λ → Fin 2) → ℂ :=
  basisVec (fun _ : Λ => (0 : Fin 2))

/-- The smeared creation operator `Ĉ†(φ) = Σ_x φ(x) ĉ†_x`
(Tasaki eq. (9.2.46), p. 313). -/
noncomputable def fermionCreationFromVector (φ : Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, φ x • fermionCreationAbstract x

/-- The smeared annihilation operator `Ĉ(φ) = Σ_x φ(x)* ĉ_x` written
without the conjugation on the coefficients, i.e. `Σ_x φ(x) ĉ_x`; the
physical `Ĉ(φ)` is obtained by feeding the conjugated vector. We keep
the linear (un-conjugated) form here for algebraic convenience
(Tasaki eq. (9.2.46), p. 313). -/
noncomputable def fermionAnnihilationFromVector (φ : Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, φ x • fermionAnnihilationAbstract x

/-- The Fock-space inner product `⟨v, w⟩ = Σ_τ v(τ)* w(τ)` of two
many-body vectors. -/
noncomputable def fockInner (v w : (Λ → Fin 2) → ℂ) : ℂ :=
  dotProduct (star v) w

/-- The single-electron overlap `⟨φ, ψ⟩ = Σ_x φ(x)* ψ(x)`
(Tasaki eq. (9.2.53) entries). -/
noncomputable def singleParticleInner (φ ψ : Λ → ℂ) : ℂ :=
  ∑ x : Λ, star (φ x) * ψ x

/-- The Slater determinant state `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾) |Φvac⟩`
(Tasaki eq. (9.2.52), p. 319). The creation operators are applied in
list order via an ordered `List.prod`, since matrix multiplication is
noncommutative. -/
noncomputable def slaterState (φs : List (Λ → ℂ)) : (Λ → Fin 2) → ℂ :=
  ((φs.map fermionCreationFromVector).prod).mulVec fermionVacuumAbstract

/-- The single-particle overlap (Gram) matrix
`(G)_{j,k} = ⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩` of Tasaki eq. (9.2.53). -/
noncomputable def slaterGram {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k => singleParticleInner (φ j) (ψ k)

/-- The empty Slater state is the vacuum: `|Φ⟩ = |Φvac⟩` when there are
no creation operators (the `n = 0` case of eq. (9.2.52)). -/
@[simp]
theorem slaterState_nil :
    slaterState ([] : List (Λ → ℂ)) = fermionVacuumAbstract := by
  unfold slaterState
  rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]

omit [LinearOrder Λ] in
/-- The Fock vacuum is normalized: `⟨Φvac, Φvac⟩ = 1`. This is the
`n = 0` instance of Lemma 9.1 (the determinant of the empty Gram matrix
is `1`), proved independently as a consistency guard for the axiom
`lemma_9_1_slater_inner_det`. -/
theorem fockInner_vacuum_self :
    fockInner (Λ := Λ) fermionVacuumAbstract fermionVacuumAbstract = 1 := by
  unfold fockInner fermionVacuumAbstract dotProduct
  have hstar : ∀ τ : Λ → Fin 2,
      star (basisVec (fun _ : Λ => (0 : Fin 2)) τ)
        = basisVec (fun _ : Λ => (0 : Fin 2)) τ := by
    intro τ
    rw [basisVec_apply]
    split <;> simp
  simp_rw [Pi.star_apply, hstar]
  rw [basisVec_inner]
  simp

/-- **Tasaki Lemma 9.1** (1st ed., Springer 2020, §9.2.3, p. 319, eq.
(9.2.53)). The inner product of the two Slater determinant states
`|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾)|Φvac⟩` and `|Ψ⟩ = Ĉ†(ψ⁽¹⁾) ⋯ Ĉ†(ψ⁽ᴺ⁾)|Φvac⟩`
equals the determinant of the single-particle overlap (Gram) matrix
`(⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩)_{j,k}`.

This is a finite-dimensional linear-algebra identity in the concrete
Jordan–Wigner representation, recorded here as a faithful documented
axiom; its `n = 0` instance is `fockInner_vacuum_self`. See the module
docstring for the discharge status. -/
axiom lemma_9_1_slater_inner_det {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    fockInner (slaterState (List.ofFn φ)) (slaterState (List.ofFn ψ))
      = (slaterGram φ ψ).det

/-- **Tasaki Lemma 9.1**, explicit permutation-sum form of eq. (9.2.53):

  `⟨Φ, Ψ⟩ = Σ_p (sign p) ∏_j ⟨φ⁽ʲ⁾, ψ⁽ᵖ⁽ʲ⁾⁾⟩`,

obtained from the determinant identity `lemma_9_1_slater_inner_det` by
the Leibniz expansion of the determinant. -/
theorem lemma_9_1_slater_inner_perm_sum {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    fockInner (slaterState (List.ofFn φ)) (slaterState (List.ofFn ψ))
      = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℂ)
            * ∏ j : Fin n, singleParticleInner (φ j) (ψ (p j)) := by
  rw [lemma_9_1_slater_inner_det, ← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rfl

/-- The `Λ × Fin n` coefficient matrix whose `j`-th column is the
single-electron wave function `φ⁽ʲ⁾`:
`(slaterCoeffMatrix φ) x j = φ⁽ʲ⁾(x)`. -/
noncomputable def slaterCoeffMatrix {n : ℕ} (φ : Fin n → Λ → ℂ) :
    Matrix Λ (Fin n) ℂ :=
  Matrix.of (fun x j => φ j x)

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The single-particle overlap (Gram) matrix of a family with itself is
the conjugate-transpose square `Aᴴ A` of its coefficient matrix
`A = slaterCoeffMatrix φ`: `(G)_{j,k} = ⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩ = (Aᴴ A)_{j,k}`. -/
theorem slaterGram_self_eq_conjTranspose_mul_self {n : ℕ} (φ : Fin n → Λ → ℂ) :
    slaterGram φ φ = (slaterCoeffMatrix φ)ᴴ * slaterCoeffMatrix φ := by
  ext j k
  simp only [slaterGram, singleParticleInner, Matrix.mul_apply,
    Matrix.conjTranspose_apply, slaterCoeffMatrix, Matrix.of_apply]

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The Gram determinant of a family with itself is nonzero iff the family
is linearly independent. This is the linear-algebra core behind Lemma 9.2:
`det(⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩) ≠ 0 ↔ φ` are linearly independent, via `G = Aᴴ A`,
`ker(Aᴴ A) = ker A`, and the column-injectivity criterion. -/
theorem slaterGram_self_det_ne_zero_iff {n : ℕ} (φ : Fin n → Λ → ℂ) :
    (slaterGram φ φ).det ≠ 0 ↔ LinearIndependent ℂ φ := by
  have hcol : (slaterCoeffMatrix φ).col = φ := by
    funext j; funext x; rfl
  have hLI : LinearIndependent ℂ φ ↔
      Function.Injective (slaterCoeffMatrix φ).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
  have hker :
      Function.Injective ((slaterCoeffMatrix φ)ᴴ * slaterCoeffMatrix φ).mulVec ↔
        Function.Injective (slaterCoeffMatrix φ).mulVec := by
    rw [← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin,
      ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
      Matrix.ker_mulVecLin_eq_bot_iff, Matrix.ker_mulVecLin_eq_bot_iff]
    constructor
    · intro h v hv
      exact h v ((Matrix.conjTranspose_mul_self_mulVec_eq_zero _ v).mpr hv)
    · intro h v hv
      exact h v ((Matrix.conjTranspose_mul_self_mulVec_eq_zero _ v).mp hv)
  rw [slaterGram_self_eq_conjTranspose_mul_self, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit,
    hker, ← hLI]

/-- **Tasaki Lemma 9.2** (1st ed., Springer 2020, §9.2.3, p. 320). The
Slater determinant state `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾)|Φvac⟩` is
nonvanishing if and only if the `N` single-electron wave functions
`φ⁽¹⁾, …, φ⁽ᴺ⁾` are linearly independent.

Proof: by Lemma 9.1 (with `ψ = φ`) the squared norm `⟨Φ, Φ⟩` equals the
Gram determinant `det(⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩)`; the Fock inner product is positive
definite, so `Φ = 0` iff `⟨Φ, Φ⟩ = 0`, and the Gram determinant vanishes
iff the family is linearly dependent. -/
theorem lemma_9_2_slater_ne_zero_iff_linearIndependent {n : ℕ}
    (φ : Fin n → Λ → ℂ) :
    slaterState (List.ofFn φ) ≠ 0 ↔ LinearIndependent ℂ φ := by
  rw [← slaterGram_self_det_ne_zero_iff, ← lemma_9_1_slater_inner_det,
    ne_eq, ne_eq, not_iff_not]
  unfold fockInner
  exact dotProduct_star_self_eq_zero.symm

end LatticeSystem.Fermion
