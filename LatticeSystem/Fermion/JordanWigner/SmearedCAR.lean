import LatticeSystem.Fermion.JWAbstractCrossSite
import LatticeSystem.Fermion.JordanWigner.SmearedOperators

/-!
# Smeared canonical anticommutation relations (Tasaki §9.2.3)

This module lifts the on-site and cross-site canonical anticommutation
relations (CAR) of the abstract Jordan–Wigner operators
`fermionAnnihilationAbstract` / `fermionCreationAbstract` to the
**smeared** operators

  `Ĉ(φ) = Σ_x φ(x) ĉ_x`,   `Ĉ†(ψ) = Σ_x ψ(x) ĉ†_x`

(`fermionAnnihilationFromVector` / `fermionCreationFromVector`,
Tasaki eq. (9.2.46), p. 313). The smeared *mixed* CAR and the
vacuum-killing identity are proved upstream in
`LatticeSystem.Fermion.JordanWigner.SmearedOperators`; this file records
the two remaining pure creation / annihilation anticommutators. Together
these are the algebraic core of Tasaki's Lemma 9.1 (the Slater-determinant
overlap = Gram determinant, §9.2.3, p. 319, eq. (9.2.53)), tracked in #4593.

  Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer (2020), §9.2.3, pp. 313–319.

## Main results

* `fermionCreationFromVector_anticomm` — `{Ĉ†(φ), Ĉ†(ψ)} = 0`.
* `fermionAnnihilationFromVector_anticomm` — `{Ĉ(φ), Ĉ(ψ)} = 0`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-! ## Smeared canonical anticommutation relations -/

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

end LatticeSystem.Fermion
