/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Sublattice spin operators for the MLM toy Hamiltonian

To establish the Casimir identity for the toy Hamiltonian
(Tasaki §2.5 eq. (2.5.11)),

  `Ĥ_toy = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)`,

we need the **sublattice spin operators** for `α ∈ {1, 2, 3}`:

  `Ŝ_A^(α) := Σ_{x ∈ A} Ŝ_x^(α)`,
  `Ŝ_B^(α) := Σ_{x ∈ ¬A} Ŝ_x^(α)`,

where the sums are over the sublattice indicators `A : Λ → Bool`.
The total spin then decomposes as
`Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_B^(α)`.

This module defines the sublattice operators and proves the basic
decomposition `Ŝ_tot = Ŝ_A + Ŝ_B`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice spin operators -/

/-- The sublattice-`A` total spin (axis 1):
`Ŝ_A^(1) := Σ_{x ∈ A} onSite x Ŝ^(1)`. -/
noncomputable def sublatticeSpinHalfOp1 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp1 else 0

/-- The sublattice-`A` total spin (axis 2):
`Ŝ_A^(2) := Σ_{x ∈ A} onSite x Ŝ^(2)`. -/
noncomputable def sublatticeSpinHalfOp2 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp2 else 0

/-- The sublattice-`A` total spin (axis 3):
`Ŝ_A^(3) := Σ_{x ∈ A} onSite x Ŝ^(3)`. -/
noncomputable def sublatticeSpinHalfOp3 (A : Λ → Bool) : ManyBodyOp Λ :=
  ∑ x : Λ, if A x then onSite x spinHalfOp3 else 0

/-! ## Decomposition of the total spin into sublattices -/

/-- The total spin (axis 1) decomposes as a sum over the two
sublattices: `Ŝ_tot^(1) = Ŝ_A^(1) + Ŝ_¬A^(1)`. -/
theorem totalSpinHalfOp1_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp1 Λ =
      sublatticeSpinHalfOp1 A + sublatticeSpinHalfOp1 (fun x => ! A x) := by
  unfold totalSpinHalfOp1 sublatticeSpinHalfOp1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin (axis 2) decomposes as a sum over the two
sublattices. -/
theorem totalSpinHalfOp2_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp2 Λ =
      sublatticeSpinHalfOp2 A + sublatticeSpinHalfOp2 (fun x => ! A x) := by
  unfold totalSpinHalfOp2 sublatticeSpinHalfOp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-- The total spin (axis 3) decomposes as a sum over the two
sublattices. -/
theorem totalSpinHalfOp3_eq_sublattice_sum (A : Λ → Bool) :
    totalSpinHalfOp3 Λ =
      sublatticeSpinHalfOp3 A + sublatticeSpinHalfOp3 (fun x => ! A x) := by
  unfold totalSpinHalfOp3 sublatticeSpinHalfOp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

end LatticeSystem.Quantum
