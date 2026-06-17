import LatticeSystem.Fermion.JWAbstractCrossSite
import LatticeSystem.Fermion.JordanWigner.FockSpaceRepresentation

/-!
# Smeared canonical anticommutation relations (Tasaki §9.2.3)

This module lifts the on-site and cross-site canonical anticommutation
relations (CAR) of the abstract Jordan–Wigner operators
`fermionAnnihilationAbstract` / `fermionCreationAbstract` to the
**smeared** operators

  `Ĉ(φ) = Σ_x φ(x) ĉ_x`,   `Ĉ†(ψ) = Σ_x ψ(x) ĉ†_x`

(`fermionAnnihilationFromVector` / `fermionCreationFromVector`,
Tasaki eq. (9.2.46), p. 313), and records the vacuum-killing identity
`Ĉ(φ) |Φvac⟩ = 0`. Together these are the algebraic core of Tasaki's
Lemma 9.1 (the Slater-determinant overlap = Gram determinant,
§9.2.3, p. 319, eq. (9.2.53)), tracked in #4593.

  Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer (2020), §9.2.3, pp. 313–319.

## Main results

* `fermionFromVector_anticomm_mixed` — the smeared mixed CAR
  `{Ĉ(φ), Ĉ†(ψ)} = (Σ_x φ(x) ψ(x)) · 1`.
* `fermionCreationFromVector_anticomm` — `{Ĉ†(φ), Ĉ†(ψ)} = 0`.
* `fermionAnnihilationFromVector_anticomm` — `{Ĉ(φ), Ĉ(ψ)} = 0`.
* `fermionAnnihilationFromVector_mulVec_vacuum` — `Ĉ(φ) |Φvac⟩ = 0`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-! ## Bilinear expansion of a product of two smeared operators -/

omit [LinearOrder Λ] in
/-- Expansion of the anticommutator of two smeared (coefficient-weighted)
sums of operators into a weighted double sum of per-pair
anticommutators:

  `(Σ_x φ_x f_x)(Σ_y ψ_y g_y) + (Σ_y ψ_y g_y)(Σ_x φ_x f_x)`
    `= Σ_x Σ_y (φ_x ψ_y) • (f_x g_y + g_y f_x)`.

A purely algebraic identity used to reduce each smeared CAR to the
on-site / cross-site CAR of the abstract operators (Tasaki §9.2.3,
p. 313). -/
private lemma sum_smul_anticomm_eq_double_sum
    (φ ψ : Λ → ℂ) (f g : Λ → ManyBodyOp Λ) :
    (∑ x : Λ, φ x • f x) * (∑ y : Λ, ψ y • g y) +
        (∑ y : Λ, ψ y • g y) * (∑ x : Λ, φ x • f x)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (f x * g y + g y * f x) := by
  have hST : (∑ x : Λ, φ x • f x) * (∑ y : Λ, ψ y • g y)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (f x * g y) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hTS : (∑ y : Λ, ψ y • g y) * (∑ x : Λ, φ x • f x)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (g y * f x) := by
    rw [Finset.sum_mul]
    rw [show (∑ y : Λ, (ψ y • g y) * ∑ x : Λ, φ x • f x)
        = ∑ y : Λ, ∑ x : Λ, (φ x * ψ y) • (g y * f x) from by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (ψ y) (φ x)]]
    rw [Finset.sum_comm]
  rw [hST, hTS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_add]

/-! ## Smeared canonical anticommutation relations -/

/-- **Smeared mixed CAR** (Tasaki §9.2.3, p. 313, eq. (9.2.46) +
on-site/cross-site CAR). The mixed anticommutator of the smeared
annihilation operator `Ĉ(φ) = Σ_x φ(x) ĉ_x` and the smeared creation
operator `Ĉ†(ψ) = Σ_x ψ(x) ĉ†_x` is the scalar
`Σ_x φ(x) ψ(x)` times the identity:

  `Ĉ(φ) Ĉ†(ψ) + Ĉ†(ψ) Ĉ(φ) = (Σ_x φ(x) ψ(x)) · 1`. -/
theorem fermionFromVector_anticomm_mixed (φ ψ : Λ → ℂ) :
    fermionAnnihilationFromVector φ * fermionCreationFromVector ψ +
        fermionCreationFromVector ψ * fermionAnnihilationFromVector φ
      = (∑ x : Λ, φ x * ψ x) • (1 : ManyBodyOp Λ) := by
  unfold fermionAnnihilationFromVector fermionCreationFromVector
  rw [sum_smul_anticomm_eq_double_sum φ ψ fermionAnnihilationAbstract
    fermionCreationAbstract]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [fermionMultiAnticommAbstract_self]
  · intro y _ hyx
    rw [fermionAnnihilationAbstract_creation_anticomm_of_ne (Ne.symm hyx),
      smul_zero]
  · intro hx; exact absurd (Finset.mem_univ x) hx

/-- **Smeared creation CAR** (Tasaki §9.2.3, p. 313). Two smeared
creation operators anticommute:

  `Ĉ†(φ) Ĉ†(ψ) + Ĉ†(ψ) Ĉ†(φ) = 0`.

The diagonal terms vanish by `fermionCreationAbstract_sq`, the
off-diagonal terms by the cross-site CAR
`fermionCreationAbstract_anticomm_of_ne`. -/
theorem fermionCreationFromVector_anticomm (φ ψ : Λ → ℂ) :
    fermionCreationFromVector φ * fermionCreationFromVector ψ +
        fermionCreationFromVector ψ * fermionCreationFromVector φ
      = 0 := by
  unfold fermionCreationFromVector
  rw [sum_smul_anticomm_eq_double_sum φ ψ fermionCreationAbstract
    fermionCreationAbstract]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [fermionCreationAbstract_sq, add_zero, smul_zero]
  · rw [fermionCreationAbstract_anticomm_of_ne hxy, smul_zero]

/-- **Smeared annihilation CAR** (Tasaki §9.2.3, p. 313). Two smeared
annihilation operators anticommute:

  `Ĉ(φ) Ĉ(ψ) + Ĉ(ψ) Ĉ(φ) = 0`.

The diagonal terms vanish by `fermionAnnihilationAbstract_sq`, the
off-diagonal terms by the cross-site CAR
`fermionAnnihilationAbstract_anticomm_of_ne`. -/
theorem fermionAnnihilationFromVector_anticomm (φ ψ : Λ → ℂ) :
    fermionAnnihilationFromVector φ * fermionAnnihilationFromVector ψ +
        fermionAnnihilationFromVector ψ * fermionAnnihilationFromVector φ
      = 0 := by
  unfold fermionAnnihilationFromVector
  rw [sum_smul_anticomm_eq_double_sum φ ψ fermionAnnihilationAbstract
    fermionAnnihilationAbstract]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [fermionAnnihilationAbstract_sq, add_zero, smul_zero]
  · rw [fermionAnnihilationAbstract_anticomm_of_ne hxy, smul_zero]

/-! ## Vacuum-killing identity -/

/-- The single-mode abstract annihilation operator kills the Fock
vacuum: `ĉ_x |Φvac⟩ = 0` (Tasaki §9.2.3, p. 314). The vacuum has
the site-`x` entry `0` (empty/up), and the column `0` of
`spinHalfOpPlus = !![0,1;0,0]` is zero, so the single-site action
`onSite x spinHalfOpPlus` annihilates the vacuum, and the leading
Jordan–Wigner string maps `0` to `0`. -/
theorem fermionAnnihilationAbstract_mulVec_vacuum (x : Λ) :
    (fermionAnnihilationAbstract x).mulVec
        (fermionVacuumAbstract : (Λ → Fin 2) → ℂ) = 0 := by
  unfold fermionAnnihilationAbstract fermionVacuumAbstract
  rw [← Matrix.mulVec_mulVec, onSite_mulVec_basisVec]
  have hzero : (fun τ : Λ → Fin 2 =>
      ∑ k : Fin 2, spinHalfOpPlus k ((fun _ : Λ => (0 : Fin 2)) x) *
        basisVec (Function.update (fun _ : Λ => (0 : Fin 2)) x k) τ)
      = (0 : (Λ → Fin 2) → ℂ) := by
    funext τ
    refine Finset.sum_eq_zero fun k _ => ?_
    have : spinHalfOpPlus k (0 : Fin 2) = 0 := by
      fin_cases k <;> simp [spinHalfOpPlus]
    rw [this, zero_mul]
  rw [hzero, Matrix.mulVec_zero]

/-- **Smeared vacuum-killing identity** (Tasaki §9.2.3, p. 314). The
smeared annihilation operator `Ĉ(φ) = Σ_x φ(x) ĉ_x` annihilates the
Fock vacuum: `Ĉ(φ) |Φvac⟩ = 0`. Follows from
`fermionAnnihilationAbstract_mulVec_vacuum` by linearity of `mulVec`
over the coefficient-weighted sum. -/
theorem fermionAnnihilationFromVector_mulVec_vacuum (φ : Λ → ℂ) :
    (fermionAnnihilationFromVector φ).mulVec
        (fermionVacuumAbstract : (Λ → Fin 2) → ℂ) = 0 := by
  unfold fermionAnnihilationFromVector
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.smul_mulVec, fermionAnnihilationAbstract_mulVec_vacuum,
    smul_zero]

end LatticeSystem.Fermion
